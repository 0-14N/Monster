package com.monster.taint.state;

import java.util.ArrayList;

public class PathState {
	private ArrayList<TaintValue> taintValues = null;
	
	public PathState(){
		this.taintValues = new ArrayList<TaintValue>();
	}
	
	public void addTaintValue(TaintValue taintValue){
		boolean exists = false;
		for(TaintValue tv : taintValues){
			if(tv.equals(taintValue)){
				exists = true;
				break;
			}
		}
		if(!exists)
			this.taintValues.add(taintValue);
	}
}
