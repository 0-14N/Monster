package com.monster.taint.output;

import java.io.File;
import java.io.IOException;
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
import com.monster.taint.z3.SMT2FileGenerator;

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
		sinkContainerElement.setAttribute("SinkInvoking", pathChain.getActivationUnit().toString());
		rootElement.appendChild(sinkContainerElement);
		
		//the stmt invoking the sink
		Unit activationUnit = pathChain.getActivationUnit();
		ArrayList<Unit> unitsOnPath = pathChain.getSinglePath().getUnitsOnPath(); 
		//indicate whether a stmt should be contained in the slice
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
				//whether the condition is satisfied
				if(i + 1 < unitsOnPath.size()){
					Stmt nextStmt = (Stmt) unitsOnPath.get(i + 1);
					//if(target.toString().equals(nextStmt.toString())){
					if(target.equals(nextStmt)){
						satisfied = true;
					}
				}
				Constraint constraint = new Constraint(ifStmt, satisfied, i, unitsOnPath);
				//get the propagation of condition values
				constraint.stepBackwrads();
				constraintList.add(constraint);
			}
		}
		
		ArrayList<Constraint> filteredConstraints = new ArrayList<Constraint>();
		for(int i = constraintList.size() - 1; i >= 0; i--){
			Constraint constraint = constraintList.get(i);
			//currently, we only care about the constraints related to String/Intent type
			//parameter passed in
			//if(constraint.dependOnIntentParameters() || constraint.dependOnStringParameters()){
			if(constraint.dependOnParameters()){
				filteredConstraints.add(constraint);
				unionTwoIntArray(flagsArray, constraint.getFlagsArray());
				allConstaintsElement.appendChild(constraint.getConstraintElement(doc));
			}
		}
		allConstaintsElement.setAttribute("filtered_size", "" + filteredConstraints.size());
		sinkContainerElement.appendChild(allConstaintsElement);
		
	
		//path relevant to constraints
		Element constraintRelatedPathElement = doc.createElement("ConstraintRelatedPath");
		ArrayList<Unit> allRelatedUnits = new ArrayList<Unit>();
		int size = 0;
		//merge each constraint's related stmts
		for(int i = 0; i < flagsArray.length; i++){
			if(flagsArray[i] == 1){
				size++;
				Element stmtElement = doc.createElement("Stmt");
				stmtElement.setAttribute("value", unitsOnPath.get(i).toString());
				constraintRelatedPathElement.appendChild(stmtElement);
				allRelatedUnits.add(unitsOnPath.get(i));
			}
		}
		constraintRelatedPathElement.setAttribute("size", "" + size);
		SLICED_SIZE = size;
		sinkContainerElement.appendChild(constraintRelatedPathElement);
		
		//generate the SMT2 file according the constraints
		String dependenceFileName = SMT2FileGenerator.v().generateSMT2File(filteredConstraints, 
				pathChain.getSinglePath(), allRelatedUnits, outputFileName);
		
		//handle the InDependence Chains
		if(pathChain.hasInDepPaths()){
			Element inDepsElement = doc.createElement("InDependencePaths");
			ArrayList<PathChain> inDepChains = pathChain.getInDepPaths();
			inDepsElement.setAttribute("size", "" + inDepChains.size());
			for(PathChain inDepChain : inDepChains){
				extractConstraintsOfPathChain(inDepChain, inDepsElement, doc, "InDepPath", dependenceFileName);
			}
			rootElement.appendChild(inDepsElement);
		}
		
		//handle the RetDepdence Chains
		if(pathChain.hasRetDepPaths()){
			Element retDepsElement = doc.createElement("RetDependencePaths");
			ArrayList<PathChain> retDepChains = pathChain.getRetDepPaths();
			retDepsElement.setAttribute("size", "" + retDepChains.size());
			for(PathChain retDeChain : retDepChains){
				extractConstraintsOfPathChain(retDeChain, retDepsElement, doc, "RetDepPath", dependenceFileName);
			}
			rootElement.appendChild(retDepsElement);
		}
		
		//record the slice efficiency
		this.slicedPathProportions.add(new Float(((float) SLICED_SIZE)/((float) ORIGINAL_SIZE)));
		
		TransformerFactory transformerFactory = TransformerFactory.newInstance();
		Transformer transformer = transformerFactory.newTransformer();
		DOMSource source = new DOMSource(doc);
		StreamResult result = new StreamResult(new File(CONSTRAINT_DIR + outputFileName));
		transformer.transform(source, result);
	}

	/**
	 * Improve: extract code from "extractConstraints" and reuse it.
	 * 
	 * @param pathChain
	 * @param parentElement
	 * @param doc
	 * @param elementName : "InDependencePaths", "RetDependencePaths"
	 * @param dependenceFileName : for smt2 file generator
	 */
	private void extractConstraintsOfPathChain(PathChain pathChain, Element parentElement, 
			Document doc, String elementName, String dependenceFileName){
		Unit activationUnit = pathChain.getActivationUnit();
		ArrayList<Unit> unitsOnPath = pathChain.getSinglePath().getUnitsOnPath(); 
		int[] flagsArray = new int[unitsOnPath.size()];
		int activationIndex = unitsOnPath.indexOf(activationUnit);
		SootMethod method = pathChain.getSinglePath().getMethodHub().getMethod();
		String thisSMT2FileName =null;
		assert(activationIndex >= 0 && activationIndex < unitsOnPath.size());
		
		Element pathChainElement = doc.createElement(elementName);
		pathChainElement.setAttribute("MethodSignature", method.getSignature());
		pathChainElement.setAttribute("Invoking", pathChain.getActivationUnit().toString());
		parentElement.appendChild(pathChainElement);
		
		//original path
		Element originalPathElement = doc.createElement("OriginalPath");
		originalPathElement.setAttribute("size", "" + unitsOnPath.size());
		ORIGINAL_SIZE = unitsOnPath.size();
		for(int i = 0; i < unitsOnPath.size(); i++){
			Element stmtElement = doc.createElement("Stmt");
			stmtElement.setAttribute("value", unitsOnPath.get(i).toString());
			originalPathElement.appendChild(stmtElement);
		}
		pathChainElement.appendChild(originalPathElement);

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
		
		//add the constraints elements
		ArrayList<Constraint> filteredConstraints = new ArrayList<Constraint>();
		for(int i = constraintList.size() - 1; i >= 0; i--){
			Constraint constraint = constraintList.get(i);
			//if(constraint.dependOnIntentParameters() || constraint.dependOnStringParameters()){
			if(constraint.dependOnParameters()){
				filteredConstraints.add(constraint);
				unionTwoIntArray(flagsArray, constraint.getFlagsArray());
				allConstaintsElement.appendChild(constraint.getConstraintElement(doc));
			}
		}
		allConstaintsElement.setAttribute("size", "" + filteredConstraints.size());
		pathChainElement.appendChild(allConstaintsElement);

		//if(filteredConstraints.size() > 0){
			//path relevant to constraints
			Element constraintRelatedPathElement = doc.createElement("ConstraintRelatedPath");
			ArrayList<Unit> allRelatedUnits = new ArrayList<Unit>();
			int size = 0;
			//merge each constraint's related stmts
			for(int i = 0; i < flagsArray.length; i++){
				if(flagsArray[i] == 1){
					size++;
					Element stmtElement = doc.createElement("Stmt");
					stmtElement.setAttribute("value", unitsOnPath.get(i).toString());
					constraintRelatedPathElement.appendChild(stmtElement);
					allRelatedUnits.add(unitsOnPath.get(i));
				}
			}
			constraintRelatedPathElement.setAttribute("size", "" + size);
			SLICED_SIZE = size;
			pathChainElement.appendChild(constraintRelatedPathElement);
			
			//generate SMT2 file
			try {
				thisSMT2FileName = SMT2FileGenerator.v().generateSMT2File(filteredConstraints, 
						pathChain.getSinglePath(), allRelatedUnits, dependenceFileName);
			} catch (IOException e) {
				e.printStackTrace();
			}
		//}
		
		//handle the InDependence Chains
		if(pathChain.hasInDepPaths()){
			Element inDepsElement = doc.createElement("InDependencePaths");
			ArrayList<PathChain> inDepChains = pathChain.getInDepPaths();
			inDepsElement.setAttribute("size", "" + inDepChains.size());
			for(PathChain inDepChain : inDepChains){
				extractConstraintsOfPathChain(inDepChain, inDepsElement, doc, "InDepPath", thisSMT2FileName);
			}
			pathChainElement.appendChild(inDepsElement);
		}
		
		//handle the RetDepdence Chains
		if(pathChain.hasRetDepPaths()){
			Element retDepsElement = doc.createElement("RetDependencePaths");
			ArrayList<PathChain> retDepChains = pathChain.getRetDepPaths();
			retDepsElement.setAttribute("size", "" + retDepChains.size());
			for(PathChain retDeChain : retDepChains){
				extractConstraintsOfPathChain(retDeChain, retDepsElement, doc, "RetDepPath", thisSMT2FileName);
			}
			pathChainElement.appendChild(retDepsElement);
		}
		
		//record the slice efficiency
		this.slicedPathProportions.add(new Float(((float) SLICED_SIZE)/((float) ORIGINAL_SIZE)));
		
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
