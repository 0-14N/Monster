package com.monster.taint.wrapper;

import java.util.ArrayList;

import soot.SootMethod;

/**
 * This class is mainly responsible for recording the method
 * invoking with tainted parameters, but without producing
 * new taint values
 * 
 * @author chenxiong
 *
 */
public class InvokingHistoryPool {
	private static InvokingHistoryPool instance = null;
	
	private ArrayList<SootMethod> invokedMethodList = null;
	
	private InvokingHistoryPool(){
		this.invokedMethodList = new ArrayList<SootMethod>();
	}
	
	public static InvokingHistoryPool v(){
		if(instance == null){
			instance = new InvokingHistoryPool();
		}
		return instance;
	}
	
	public boolean isInBlacklist(SootMethod method){
		if(this.invokedMethodList.contains(method)){
			return true;
		}
		return false;
	}
	
	public void addToBlocklist(SootMethod method){
		if(!this.invokedMethodList.contains(method)){
			this.invokedMethodList.add(method);
		}
	}
}
