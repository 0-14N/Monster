package com.monster.taint;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.monster.taint.path.MethodPath;
import com.monster.taint.path.MethodPathCreator;
import com.monster.taint.state.MethodState;
import com.monster.taint.state.PathState;

import soot.SootMethod;
import soot.Unit;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ZonedBlockGraph;

/**
 * In order to analyze a method, we have to take all the
 * paths into consideration, to analyze a path, we need
 * to create the ForwardsProblem/BackwardsProblem at first.
 * 
 * @author chenxiong
 *
 */
public class MethodHub {
	private Logger logger = LoggerFactory.getLogger(getClass());
	
	private SootMethod method = null;
	private Unit activationUnit = null;
	private MethodHubType type = null;
	private boolean isSource = false;
	private ZonedBlockGraph zonedBlockGraph = null;
	//Paths of method
	private Set<MethodPath> paths = null;
	//the states
	private MethodState initState = null;//for method contains sources, unused
	private HashMap<MethodPath, PathState> pathStates = null;
	private MethodState exitState = null;
	private MethodHub preHub = null;

	/**
	 * 
	 * @param method
	 * @param activationUnit : null if type==CALLED_FORWARD || type==CALLED_BACKWARD
	 * @param type
	 * @param isSource
	 */
	public MethodHub(SootMethod method, Unit activationUnit, MethodHubType type,
			boolean isSource, MethodHub preHub) {
		this.method = method;
		this.activationUnit = activationUnit;
		this.type = type;
		this.isSource = isSource;
		this.zonedBlockGraph = new ZonedBlockGraph(this.method.getActiveBody());
		this.paths = new HashSet<MethodPath>();
		this.pathStates = new HashMap<MethodPath, PathState>();
		this.preHub = preHub;
	}
	
	public void setInitState(MethodState initState){
		this.initState = initState;
	}
	
	public boolean isSource(){
		return this.isSource;
	}
	
	public void start(){
		//first, get all paths contain the activationUnit
		calculatePaths();
	
		//method contains source
		if(this.type == MethodHubType.CALLED_FORWARD || 
				this.type == MethodHubType.CALLED_BACKWARD){
			for(MethodPath methodPath : paths){
				methodPath.start();
			}
		}
	}
	
	public MethodState getInitState(){
		return this.initState;
	}

	/**
	 * calculated all the paths contain activationUnit
	 */
	private void calculatePaths(){
		ArrayList<ArrayList<Block>> pathBlockLists = MethodPathCreator.v().getPaths(this.zonedBlockGraph);
		for(ArrayList<Block> blockList : pathBlockLists){
			MethodPath methodPath = null;
			if(this.type == MethodHubType.INVOKING_RETURN){
				if(containsUnit(blockList, activationUnit)){
					methodPath = new MethodPath(blockList, this, this.type, this.activationUnit);
				}
			}else{
				methodPath = new MethodPath(blockList, this, this.type, this.activationUnit);
			}
			if(methodPath != null){
				this.paths.add(methodPath);
			}
		}
	}
	
	private boolean containsUnit(ArrayList<Block> blockList, Unit activationUnit){
		boolean contains = false;
		for(Block block : blockList){
			Iterator iter = block.iterator();
			while(iter.hasNext()){
				Unit unit = (Unit) iter.next();
				if(unit.equals(activationUnit)) return true;
			}
		}
		return contains;
	}
	
}
