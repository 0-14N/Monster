package com.monster.taint.state;

import java.util.ArrayList;

/**
 * 
 * @author chenxiong
 *
 */
public class MethodState {
	private ArrayList<TaintValue> thisTVs = null;
	private ArrayList<ArrayList<TaintValue>> argsTVs = null;
	private ArrayList<TaintValue> staticTVs = null;
	//for method init state, retTVs should be empty
	private ArrayList<TaintValue> retTVs = null;
	
	public MethodState(int argsCount){
		this.thisTVs = new ArrayList<TaintValue>();
		this.argsTVs = new ArrayList<ArrayList<TaintValue>>(argsCount);
		for(int i = 0; i < argsCount; i++){
			this.argsTVs.add(new ArrayList<TaintValue>());
		}
		this.staticTVs = new ArrayList<TaintValue>();
		this.retTVs = new ArrayList<TaintValue>();
	}
	
	public ArrayList<TaintValue> getThisTVs(){
		return this.thisTVs;
	}
	
	public ArrayList<TaintValue> getArgTVs(int argIndex){
		return this.argsTVs.get(argIndex);
	}
	
	public ArrayList<TaintValue> getStaticTVs(){
		return this.staticTVs;
	}
	
	public ArrayList<TaintValue> getRetTVs(){
		return this.retTVs;
	}
}
