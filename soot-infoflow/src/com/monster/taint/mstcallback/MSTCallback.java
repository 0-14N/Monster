package com.monster.taint.mstcallback;

import java.util.List;

import soot.Scene;
import soot.SootClass;
import soot.SootMethod;

/**
 * this class represents certain callbacks that their input parameters
 * should be tainted, e.g. Service.onStartCommand(Intent intent*, ...)
 * @author chenxiong
 *
 */
public class MSTCallback {
	private String signature = null;
	private String name = null;
	private boolean isStatic = false;
	private int argCount = 0;
	private SootMethod method = null;;
	//taintedArgs is an array of parameter index which should be tainted
	private int[] taintedArgs = null;
	
	public MSTCallback(String signature, boolean isStatic,
			int argCount, int[] taintedArgs) throws RuntimeException{
		this.signature = signature;
		this.isStatic = isStatic;
		this.argCount = argCount;
		this.taintedArgs = taintedArgs;
		//this may throw RuntimeException: nonexistent method
		this.method = Scene.v().getMethod(this.signature);
	}

	/**
	 * whether a method matches this, true when satisfy following conditions:
	 * 1. method's signature (or parent's signature) matches this.signature
	 * 2. this.taintedArgs[n] == paramIdx (n=0, 1, 2, ...)  
	 * otherwise, false
	 * @param inSignature 
	 * @param paramIdx
	 * @return
	 */
	public boolean hitMe(String inSignature, int paramIdx){
		if(this.signature.equals(inSignature) && isParamTainted(paramIdx)){
			return true;
		}
		
		SootMethod inMethod = null;
		try{
			inMethod = Scene.v().getMethod(inSignature);
		}catch(RuntimeException re){
			re.printStackTrace();
			return false;
		}
		if(inMethod == null){
			return false;
		}
		SootClass inClass = inMethod.getDeclaringClass();
		List<SootClass> superClasses = Scene.v().getActiveHierarchy().getSuperclassesOf(inClass);
		//inClass is the subclass of this.method's declaring class
		if(superClasses != null && superClasses.contains(this.method.getDeclaringClass())){
			if(inMethod.getSubSignature().equals(this.method.getSubSignature())){
				if(isParamTainted(paramIdx)){
					return true;
				}
			}
		}
		return false;
	}
	
	private boolean isParamTainted(int paramIdx){
		boolean tainted = false;
		for(int i = 0; i < taintedArgs.length; i++){
			if(taintedArgs[i] == paramIdx){
				tainted = true;
				break;
			}
		}
		return tainted;
	}
	
}
