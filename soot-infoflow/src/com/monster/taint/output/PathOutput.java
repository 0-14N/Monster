package com.monster.taint.output;

import java.util.ArrayList;

import com.monster.taint.path.MethodPath;
import com.monster.taint.slice.ITESlice;

public class PathOutput {
	private static PathOutput instance = null;
	
	private PathOutput(){}
	
	public static PathOutput v(){
		if(instance == null){
			instance = new PathOutput();
		}
		return instance;
	}
	
	public void handlePathChain(PathChain pathChain){
		MethodPath methodPath = pathChain.getSinglePath();
		ITESlice.v().slice(methodPath);
		
		if(pathChain.hasInDepPaths()){
			ArrayList<PathChain> inDepPaths = pathChain.getInDepPaths();
			for(PathChain inDepPath : inDepPaths){
				handlePathChain(inDepPath);
			}
		}
		
		if(pathChain.hasRetDepPaths()){
			ArrayList<PathChain> retDepPaths = pathChain.getRetDepPaths();
			for(PathChain retDepPath : retDepPaths){
				handlePathChain(retDepPath);
			}
		}
	}
}
