package com.monster.taint.wrapper;

import java.util.Map;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;

public class MyWrapper {
	private final Logger logger = LoggerFactory.getLogger(getClass());
	private EasyTaintWrapper wrapper = null;
	private static MyWrapper instance = null;
	private  Map<String, Set<String>> classList = null;
	private  Map<String, Set<String>> excludeList = null;
	private  Map<String, Set<String>> killList = null;
	private  Set<String> includeList = null;
	
	private MyWrapper(){}
	
	public static MyWrapper v(){
		if(instance == null)
			instance = new MyWrapper();
		return instance;
	}
	
	public void init(EasyTaintWrapper wrapper){
		this.wrapper = wrapper;
		this.classList = this.wrapper.getClassList();
		this.excludeList = this.wrapper.getExcludeList();
		this.killList = this.wrapper.getKillList();
		this.includeList = this.wrapper.getIncludeList();
	}

	private boolean isInList(String className, String subSignature, Map<String, Set<String>> map){
		boolean isIn = false;
		Set<String> methodsSubSignatures = map.get(className);
		if(methodsSubSignatures != null){
			for(String s : methodsSubSignatures){
				if(s.equals(subSignature)){
					isIn = true;
					break;
				}
			}
		}
		return isIn;
		
	}
	
	public boolean isInExcludeList(String className, String subSignature){
		return this.isInList(className, subSignature, this.excludeList);
	}
	
	public boolean isInClassList(String className, String subSignature){
		return this.isInList(className, subSignature, this.classList);
	}
	
	public boolean isInKillList(String className, String subSignature){
		return this.isInList(className, subSignature, this.killList);
	}
}
