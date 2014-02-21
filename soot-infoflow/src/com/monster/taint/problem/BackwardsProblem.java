package com.monster.taint.problem;

import java.util.ArrayList;

import com.monster.taint.path.MethodPath;
import com.monster.taint.state.TaintValue;

import soot.Unit;

public class BackwardsProblem {
	private MethodPath methodPath = null;
	private ArrayList<Unit> units = null;
	private int startIndex = -1;
	private TaintValue dependence = null;

	public BackwardsProblem(ArrayList<Unit> units, int startIndex, MethodPath methodPath, 
			TaintValue dependence){
		this.units = units;
		this.startIndex = startIndex;
		this.methodPath = methodPath;
		this.dependence = dependence;
	}
	
	public void solve(){
		
	}
}
