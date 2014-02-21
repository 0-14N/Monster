package com.monster.taint.state;

import java.util.ArrayList;

import soot.Value;

public class PathState {
	private ArrayList<TaintValue> taintValues = null;
	
	public PathState(){
		this.taintValues = new ArrayList<TaintValue>();
	}

	/**
	 * If the 'taintValue' doesn't exist in current taint
	 * values, add it.
	 * 
	 * @param taintValue
	 * @return : true if added, otherwise, false
	 */
	public boolean addTaintValue(TaintValue taintValue){
		boolean exists = false;
		TaintValue tv = null;
		for(int i = 0; i < this.taintValues.size(); i++){
			tv = this.taintValues.get(i);
			if(tv.equals(taintValue)){
				exists = true;
				break;
			}
		}
		if(!exists){
			this.taintValues.add(taintValue);
		}
		return !exists;
	}
	
	public ArrayList<TaintValue> getTVsBasedOn(Value base){
		ArrayList<TaintValue> retTVs = new ArrayList<TaintValue>();
		for(TaintValue tv : taintValues){
			if(tv.getBase() != null && tv.getBase().equals(base))
				retTVs.add(tv);
		}
		return retTVs;
	}
}
