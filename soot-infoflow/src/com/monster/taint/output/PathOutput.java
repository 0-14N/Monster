package com.monster.taint.output;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.monster.taint.path.MethodPath;
import com.monster.taint.slice.ITESlice;
import com.monster.taint.slice.UnitWrapper;

public class PathOutput {
	private static PathOutput instance = null;
	
	private PathOutput(){}
	
	public static PathOutput v(){
		if(instance == null){
			instance = new PathOutput();
		}
		return instance;
	}
	
	public Element handlePathChain(PathChain pathChain, Document doc){
		MethodPath methodPath = pathChain.getSinglePath();
		List<UnitWrapper> slicedPath = ITESlice.v().slice(methodPath);
		Element slicedPathElement = doc.createElement("slicedPath");
		slicedPathElement.setAttribute("length", "" + slicedPath.size());
		for(UnitWrapper wrapper : slicedPath){
			Element stmtElement = doc.createElement("stmt");
			stmtElement.setAttribute("value", wrapper.getUnit().toString());
			slicedPathElement.appendChild(stmtElement);
		}
		
		if(pathChain.hasInDepPaths()){
			Element inDepsSlicedPathsElement = doc.createElement("inDepsSlicedPaths");
			ArrayList<PathChain> inDepPaths = pathChain.getInDepPaths();
			for(PathChain inDepPath : inDepPaths){
				inDepsSlicedPathsElement.appendChild(handlePathChain(inDepPath, doc));
			}
			slicedPathElement.appendChild(inDepsSlicedPathsElement);
		}
		
		if(pathChain.hasRetDepPaths()){
			Element retDepsSlicedPathsElement = doc.createElement("retDepsSlicedPaths");
			ArrayList<PathChain> retDepPaths = pathChain.getRetDepPaths();
			for(PathChain retDepPath : retDepPaths){
				retDepsSlicedPathsElement.appendChild(handlePathChain(retDepPath, doc));
			}
			slicedPathElement.appendChild(retDepsSlicedPathsElement);
		}
		return slicedPathElement;
	}
}
