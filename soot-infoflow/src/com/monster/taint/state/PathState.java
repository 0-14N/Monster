package com.monster.taint.state;

import java.util.ArrayList;

import soot.Local;
import soot.SootField;
import soot.Value;
import soot.jimple.InstanceFieldRef;

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
	
	public ArrayList<TaintValue> getTVsBasedOnLocal(Local local){
		ArrayList<TaintValue> retTVs = new ArrayList<TaintValue>();
		for(TaintValue tv : this.taintValues){
			if(tv.getBase() != null && tv.getBase().equals(local))
				retTVs.add(tv);
		}
		return retTVs;
	}
	
	public ArrayList<TaintValue> getTVsBasedOnStaticField(SootField sootField){
		ArrayList<TaintValue> retTVs = new ArrayList<TaintValue>();
		for(TaintValue tv : this.taintValues){
			if(tv.getType() == TaintValueType.STATIC_FIELD){
				if(tv.getAccessPath().get(0).equals(sootField))
					retTVs.add(tv);
			}
		}
		return retTVs;
	}
	
	public ArrayList<TaintValue> getTVsBasedOnInstanceFieldRef(InstanceFieldRef ifr){
		ArrayList<TaintValue> retTVs = new ArrayList<TaintValue>();
		Value ifrBase = ifr.getBase();
		SootField ifrField = ifr.getField();
		for(TaintValue tv : this.taintValues){
			if(tv.getBase() != null && tv.getBase().equals(ifrBase)){
				if(tv.getAccessPath().size() > 0 && tv.getAccessPath().get(0).equals(ifrField))
					retTVs.add(tv);
			}
		}
		return retTVs;
	}
}
