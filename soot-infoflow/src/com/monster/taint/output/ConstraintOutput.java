package com.monster.taint.output;

import java.io.File;
import java.util.ArrayList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.monster.taint.z3.Constraint;

import soot.SootMethod;
import soot.Unit;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;

public class ConstraintOutput {
	private Logger logger = LoggerFactory.getLogger(getClass());
	private final String CONSTRAINT_DIR = "../monster-out/constraints/";
	
	private static ConstraintOutput instance = null;
	
	//the proportion for the sliced path of original path
	private ArrayList<Float> slicedPathProportions = new ArrayList<Float>();
	private int ORIGINAL_SIZE, SLICED_SIZE = 0;
	
	private ConstraintOutput(){}
	
	public static ConstraintOutput v(){
		if(instance == null){
			instance = new ConstraintOutput();
		}
		return instance;
	}
	
	/**
	 * For each 'IfStmt', do backwards slice to get the units related
	 * to IfStmt's values. Merge all the units at last.
	 * 
	 * @param pathChain
	 * @throws Exception
	 */
	public void extractConstraints(PathChain pathChain) throws Exception{
		//xml output
		SootMethod method = pathChain.getSinglePath().getMethodHub().getMethod();
		int pathID = pathChain.getSinglePath().getPathID();
		String outputFileName = method.getDeclaringClass().getName() + "-" + method.getName() + "-" + pathID + ".xml";
		DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
		DocumentBuilder docBuilder = docFactory.newDocumentBuilder();
		Document doc = docBuilder.newDocument();
		
		Element rootElement = doc.createElement("RootElement");
		doc.appendChild(rootElement);

		Element sinkContainerElement = doc.createElement("SinkContainer");
		sinkContainerElement.setAttribute("MethodSignature", method.getSignature());
		sinkContainerElement.setAttribute("Sink-Invoking", pathChain.getActivationUnit().toString());
		rootElement.appendChild(sinkContainerElement);
		
		Unit activationUnit = pathChain.getActivationUnit();
		ArrayList<Unit> unitsOnPath = pathChain.getSinglePath().getUnitsOnPath(); 
		int[] flagsArray = new int[unitsOnPath.size()];
		int activationIndex = unitsOnPath.indexOf(activationUnit);
		assert(activationIndex >= 0 && activationIndex < unitsOnPath.size());
		
		//original path
		Element originalPathElement = doc.createElement("OriginalPath");
		originalPathElement.setAttribute("size", "" + unitsOnPath.size());
		ORIGINAL_SIZE = unitsOnPath.size();
		for(int i = 0; i < unitsOnPath.size(); i++){
			Element stmtElement = doc.createElement("Stmt");
			stmtElement.setAttribute("value", unitsOnPath.get(i).toString());
			originalPathElement.appendChild(stmtElement);
		}
		sinkContainerElement.appendChild(originalPathElement);

		//constraints element
		Element allConstaintsElement = doc.createElement("AllConstraints");
		ArrayList<Constraint> constraintList = new ArrayList<Constraint>();
		//backwards from 'activationUnit' and find all the IfStmt
		for(int i = activationIndex; i >= 0; i--){
			Unit unit = unitsOnPath.get(i);
			if(unit instanceof IfStmt){
				IfStmt ifStmt = (IfStmt) unit;
				//include IfStmt
				flagsArray[i] = 1;
				boolean satisfied = false;
				Stmt target = ifStmt.getTarget();
				if(i + 1 < unitsOnPath.size()){
					Stmt nextStmt = (Stmt) unitsOnPath.get(i + 1);
					//warn: in most cases, using 'toString' to compare two stmt 
					//has no problem
					if(target.toString().equals(nextStmt.toString())){
						satisfied = true;
					}
				}
				Constraint constraint = new Constraint(ifStmt, satisfied, i, unitsOnPath);
				constraint.stepBackwrads();
				constraintList.add(constraint);
			}
		}
		allConstaintsElement.setAttribute("size", "" + constraintList.size());
		int filteredConstraintSize = 0;
		for(int i = constraintList.size() - 1; i >= 0; i--){
			Constraint constraint = constraintList.get(i);
			if(constraint.dependOnIntentParameters() || constraint.dependOnStringParameters()){
				filteredConstraintSize++;
				unionTwoIntArray(flagsArray, constraint.getFlagsArray());
				allConstaintsElement.appendChild(constraint.getConstraintElement(doc));
			}
		}
		allConstaintsElement.setAttribute("filtered_size", "" + filteredConstraintSize);
		sinkContainerElement.appendChild(allConstaintsElement);
	
		//path relevant to constraints
		Element constraintRelatedPathElement = doc.createElement("ConstraintRelatedPath");
		int size = 0;
		//merge each constraint's related stmts
		for(int i = 0; i < flagsArray.length; i++){
			if(flagsArray[i] == 1){
				size++;
				Element stmtElement = doc.createElement("Stmt");
				stmtElement.setAttribute("value", unitsOnPath.get(i).toString());
				constraintRelatedPathElement.appendChild(stmtElement);
			}
		}
		constraintRelatedPathElement.setAttribute("size", "" + size);
		SLICED_SIZE = size;
		sinkContainerElement.appendChild(constraintRelatedPathElement);
		
		//record the slice efficiency
		this.slicedPathProportions.add(new Float(((float) SLICED_SIZE)/((float) ORIGINAL_SIZE)));
		
		TransformerFactory transformerFactory = TransformerFactory.newInstance();
		Transformer transformer = transformerFactory.newTransformer();
		DOMSource source = new DOMSource(doc);
		StreamResult result = new StreamResult(new File(CONSTRAINT_DIR + outputFileName));
		transformer.transform(source, result);
	}
	
	private void unionTwoIntArray(int[] dest, int[] src){
		assert(dest.length == src.length);
		for(int i = 0; i < src.length; i++){
			dest[i] |= src[i];
		}
	}

	@Override
	protected void finalize() throws Throwable {
		float sum = 0f;
		for(Float f : this.slicedPathProportions){
			sum += f.floatValue();
		}
		logger.info("Average Constraint Related Slice Efficiency: {}", sum / (float) this.slicedPathProportions.size());
		super.finalize();
	}
	
}
