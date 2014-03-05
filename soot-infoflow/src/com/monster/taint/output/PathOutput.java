package com.monster.taint.output;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.monster.taint.path.MethodPath;
import com.monster.taint.slice.ITESlice;
import com.monster.taint.slice.IntentSourceSlice;
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
	
	public void handlePathChain(PathChain pathChain, Document doc, Element parentElement){
		MethodPath methodPath = pathChain.getSinglePath();
		
		//the backwards slice start from "if ... "
		List<UnitWrapper> iteSlicedPath = ITESlice.v().slice(methodPath);
		//the forwards slice start from "rn := @parametern: android.content.Intent"
		List<UnitWrapper> intentSlicedPath = IntentSourceSlice.v().slice(iteSlicedPath);
		
		handleSlice(pathChain, iteSlicedPath, doc, parentElement, "iteSlicedPath");
		handleSlice(pathChain, intentSlicedPath, doc, parentElement, "intentSlicedPath");
	}
	
	private void handleSlice(PathChain pathChain, List<UnitWrapper> slicedPath, 
			Document doc, Element parentElement, String sliceName){
		Element iteSlicedPathElement = doc.createElement(sliceName);
		iteSlicedPathElement.setAttribute("length", "" + slicedPath.size());
		for(UnitWrapper wrapper : slicedPath){
			Element stmtElement = doc.createElement("stmt");
			stmtElement.setAttribute("value", wrapper.getUnit().toString());
			iteSlicedPathElement.appendChild(stmtElement);
		}
		
		if(pathChain.hasInDepPaths()){
			Element inDepsSlicedPathsElement = doc.createElement("inDepsSlicedPaths");
			ArrayList<PathChain> inDepPaths = pathChain.getInDepPaths();
			for(PathChain inDepPath : inDepPaths){
				handlePathChain(inDepPath, doc, inDepsSlicedPathsElement);
			}
			iteSlicedPathElement.appendChild(inDepsSlicedPathsElement);
		}
		
		if(pathChain.hasRetDepPaths()){
			Element retDepsSlicedPathsElement = doc.createElement("retDepsSlicedPaths");
			ArrayList<PathChain> retDepPaths = pathChain.getRetDepPaths();
			for(PathChain retDepPath : retDepPaths){
				handlePathChain(retDepPath, doc, retDepsSlicedPathsElement);
			}
			iteSlicedPathElement.appendChild(retDepsSlicedPathsElement);
		}
		parentElement.appendChild(iteSlicedPathElement);
	}
}
