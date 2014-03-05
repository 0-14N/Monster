package com.monster.taint.output;

import java.util.ArrayList;

import soot.Unit;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;

import com.monster.taint.path.MethodPath;

public class PathChain {
	private MethodPath singlePath = null;
	private Unit activationUnit = null;
	private ArrayList<PathChain> inDepPaths = null;
	private ArrayList<PathChain> retDepPaths = null;
	
	public PathChain(){}
	
	public void init(MethodPath path, Unit activationUnit){
		this.singlePath = path;
		this.inDepPaths = new ArrayList<PathChain>();
		this.retDepPaths = new ArrayList<PathChain>();
		this.activationUnit = activationUnit;
	}
	
	public PathChain(MethodPath path, Unit activationUnit){
		this.singlePath = path;
		this.inDepPaths = new ArrayList<PathChain>();
		this.retDepPaths = new ArrayList<PathChain>();
		this.activationUnit = activationUnit;
	}
	
	public void setInDepPaths(ArrayList<MethodPath> paths){
		Unit activation = null;
		for(MethodPath path : paths){
			ArrayList<Unit> unitsOnPath = path.getUnitsOnPath();
			for(int i = unitsOnPath.size() - 1; i >= 0; i--){
				Unit unit = unitsOnPath.get(i);
				InvokeExpr invokeExpr = null;
				if(unit instanceof InvokeStmt){
					InvokeStmt invokeStmt = (InvokeStmt) unit;
					invokeExpr = invokeStmt.getInvokeExpr();
				}else if(unit instanceof AssignStmt){
					AssignStmt assignStmt = (AssignStmt) unit;
					if(assignStmt.containsInvokeExpr()){
						invokeExpr = assignStmt.getInvokeExpr();
					}
				}
				if(invokeExpr != null){
					if(invokeExpr.getMethod().equals(this.singlePath.getMethodHub().getMethod())){
						activation = unit;
						break;
					}
				}
			}
			assert(activation != null);
			PathChain inDepPath = new PathChain(path, activation);
			this.inDepPaths.add(inDepPath);
		}
	}
	
	public void setRetDepPaths(ArrayList<MethodPath> paths){
		for(MethodPath path : paths){
			ArrayList<Unit> unitsOnPath = path.getUnitsOnPath();
			PathChain retDepPath = new PathChain(path, unitsOnPath.get(unitsOnPath.size() - 1));
			this.retDepPaths.add(retDepPath);
		}
	}

	public PathChain getFirstInDepChain(){
		assert(hasInDepPaths());
		return this.inDepPaths.get(0);
	}
	
	public PathChain getFirstRetDepChain(){
		assert(hasRetDepPaths());
		return this.retDepPaths.get(0);
	}
	
	public boolean hasInDepPaths(){
		return this.inDepPaths.size() > 0;
	}
	
	public boolean hasRetDepPaths(){
		return this.retDepPaths.size() > 0;
	}

	public MethodPath getSinglePath() {
		return singlePath;
	}

	public ArrayList<PathChain> getInDepPaths() {
		return inDepPaths;
	}

	public ArrayList<PathChain> getRetDepPaths() {
		return retDepPaths;
	}
	
	public Unit getActivationUnit(){
		return this.activationUnit;
	}
	
}
