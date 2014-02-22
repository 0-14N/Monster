package com.monster.taint.path;

import java.util.ArrayList;
import java.util.Iterator;

import com.monster.taint.MethodHub;
import com.monster.taint.MethodHubType;
import com.monster.taint.problem.ForwardsProblem;
import com.monster.taint.state.PathState;

import soot.Unit;
import soot.toolkits.graph.Block;

public class MethodPath {
	private ArrayList<Block> blockList = null;
	private MethodHub methodHub = null;
	private MethodHubType type = null;
	private Unit activationUnit = null;
	private ArrayList<Unit> unitsOnPath = null;
	private PathState pathState = null;
	
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
		return this.getPathState();
	}
	
	public boolean isActivationUnit(Unit u){
		return this.activationUnit.equals(u);
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
		if(this.type == MethodHubType.CALLED_FORWARD || 
				this.type == MethodHubType.CALLED_BACKWARD){
			int startIndex = unitsOnPath.indexOf(activationUnit);
			int stopIndex = unitsOnPath.size();
			ForwardsProblem fProblem = new ForwardsProblem(unitsOnPath, startIndex, stopIndex, this);
			fProblem.solve();
		}else if(this.type == MethodHubType.INVOKING_RETURN){
			//TODO INVOKE_RETURN
		}
	}
	
	public ArrayList<Unit> getUnitsOnPath(){
		return this.unitsOnPath;
	}
}
