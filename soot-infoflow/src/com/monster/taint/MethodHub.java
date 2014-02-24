package com.monster.taint;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.monster.taint.path.MethodPath;
import com.monster.taint.path.MethodPathCreator;
import com.monster.taint.state.MethodState;
import com.monster.taint.state.PathState;
import com.monster.taint.state.TaintValue;
import com.monster.taint.state.TaintValueType;

import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.Constant;
import soot.jimple.InstanceFieldRef;
import soot.jimple.StaticFieldRef;
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
	//flag indicates whether pathsStates have been merged
	private boolean pathStatesMerged = false;

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
				this.pathStates.put(methodPath, methodPath.getPathState());
			}
		}
	}
	
	public MethodState getInitState(){
		return this.initState;
	}
	
	public MethodHubType getType(){
		return this.type;
	}

	/**
	 * calculated all the paths contain activationUnit
	 */
	private void calculatePaths(){
		ArrayList<ArrayList<Block>> pathBlockLists = MethodPathCreator.v().getPaths(this.zonedBlockGraph);
		for(ArrayList<Block> blockList : pathBlockLists){
			MethodPath methodPath = null;
			if(this.activationUnit != null){
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
			Iterator<Unit> iter = block.iterator();
			while(iter.hasNext()){
				Unit unit = (Unit) iter.next();
				if(unit.equals(activationUnit)) return true;
			}
		}
		return contains;
	}
	
	public MethodHub getPreHub(){
		return this.preHub;
	}
	
	public boolean causeLoop(SootMethod method){
		if(this.method.equals(method))
			return true;
		MethodHub preHub = getPreHub();
		if(preHub == null)
			return false;
		else
			return preHub.causeLoop(method);
	}
	
	public MethodState getExitState(){
		if(!this.pathStatesMerged)
			return null;
		else
			return this.exitState;
	}
	
	public void mergePathStates(){
		if(!this.pathStatesMerged){
			this.pathStatesMerged = true;
			
			this.exitState = new MethodState(this.method.getParameterCount());
			
			//merge all the path states
			Iterator<Entry<MethodPath, PathState>> iter = this.pathStates.entrySet().iterator();
			while(iter.hasNext()){
				Entry<MethodPath, PathState> entry = iter.next();
				PathState pathState = entry.getValue();
				
				Local thisLocal = this.method.getActiveBody().getThisLocal();
				ArrayList<TaintValue> thisTVs = pathState.getTVsBasedOnLocal(thisLocal);
				for(TaintValue thisTV : thisTVs){
					this.exitState.addThisTVContextSensitive(thisTV);
				}
				
				List<Local> paramsLocals = this.method.getActiveBody().getParameterLocals();
				for(int i = 0; i < paramsLocals.size(); i++){
					ArrayList<TaintValue> argTVs = pathState.getTVsBasedOnLocal(paramsLocals.get(i));
					for(TaintValue argTV : argTVs){
						this.exitState.addArgTVContextSensitive(i, argTV);
					}
				}
				
				ArrayList<TaintValue> staticTVs = pathState.getStaticTVs();
				for(TaintValue staticTV : staticTVs){
					this.exitState.addStaticTVContextSensitive(staticTV);
				}
				
				//return taint values
				Value retValue = pathState.getMethodPath().getRetValue();
				if(retValue != null && !(retValue instanceof Constant)){
					ArrayList<TaintValue> retTVs = null;
					//the retValue can be Local, instance field, static field, array
					if(retValue instanceof Local){
						retTVs = pathState.getTVsBasedOnLocal((Local) retValue);
					}else if(retValue instanceof InstanceFieldRef){
						retTVs = pathState.getTVsBasedOnInstanceFieldRef((InstanceFieldRef) retValue);
					}else if(retValue instanceof StaticFieldRef){
						StaticFieldRef sfr = (StaticFieldRef) retValue;
						retTVs = pathState.getTVsBasedOnStaticField(sfr.getField());
					}else if(retValue instanceof ArrayRef){
						ArrayRef ar = (ArrayRef) retValue;
						retTVs = pathState.getTVsBasedOnLocal((Local) ar.getBase());
					}
					assert(retTVs != null);
					for(TaintValue retTV : retTVs){
						this.exitState.addRetTVContextSensitive(retTV);
					}
				}
			}
		}
	}

	@Override
	public String toString() {
		return "MethodHub [method=" + method + "]";
	}
	
}
