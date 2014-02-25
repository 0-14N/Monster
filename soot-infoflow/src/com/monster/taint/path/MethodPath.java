package com.monster.taint.path;

import java.util.ArrayList;
import java.util.Iterator;

import com.monster.taint.MethodHub;
import com.monster.taint.MethodHubType;
import com.monster.taint.problem.ForwardsProblem;
import com.monster.taint.state.PathState;

import soot.Unit;
import soot.Value;
import soot.toolkits.graph.Block;

public class MethodPath {
	private ArrayList<Block> blockList = null;
	private MethodHub methodHub = null;
	private MethodHubType type = null;
	private Unit activationUnit = null;
	private ArrayList<Unit> unitsOnPath = null;
	private PathState pathState = null;
	private Value retValue = null;
	
	public MethodPath(ArrayList<Block> blockList, MethodHub methodHub, 
			MethodHubType type, Unit activationUnit){
		this.blockList = blockList;
		this.methodHub = methodHub;
		this.type = type;
		this.activationUnit = activationUnit;
		this.pathState = new PathState(this);
	}
	
	public MethodHub getMethodHub(){
		return this.methodHub;
	}
	
	public PathState getPathState(){
		return this.pathState;
	}
	
	public boolean isActivationUnit(Unit u){
		return this.activationUnit.equals(u);
	}
	
	public void setRetValue(Value retValue){
		this.retValue = retValue;
	}
	
	public Value getRetValue(){
		return this.retValue;
	}
	
	private void init(){
		unitsOnPath = new ArrayList<Unit>();
		for(Block block : blockList){
			Iterator<Unit> iter = block.iterator();
			while(iter.hasNext()){
				unitsOnPath.add(iter.next());
			}
		}
		if(this.activationUnit == null)
			activationUnit = this.unitsOnPath.get(0);
	}
	
	public void start(){
		//convert block list to unit list, convenient for iterating
		this.init();
		//for CALLED_FORWARD and CALLED_BACKWARD types MethodHub,
		//the path state can be initialized when analyzing IdentityStmt
		if(this.type == MethodHubType.CALLED_FORWARD || 
				this.type == MethodHubType.CALLED_BACKWARD){
			int startIndex = unitsOnPath.indexOf(activationUnit);
			int stopIndex = unitsOnPath.size();
			ForwardsProblem fProblem = new ForwardsProblem(unitsOnPath, startIndex, stopIndex, this);
			fProblem.solve();
		}else if(this.type == MethodHubType.INVOKING_RETURN){
			//INVOKE_RETURN, there are two ways to initialize path states, one is initializing the 
			//state at here, another is initializing at ForwardsProblem's 'handleInvokeExpr'.
			//To be consistent, we adopt the second one.
			int startIndex = unitsOnPath.indexOf(activationUnit);
			int stopIndex = unitsOnPath.size();
			ForwardsProblem fProblem = new ForwardsProblem(unitsOnPath, startIndex, stopIndex, this);
			fProblem.solve();
		}
	}
	
	public ArrayList<Unit> getUnitsOnPath(){
		return this.unitsOnPath;
	}
}
