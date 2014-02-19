package com.monster.taint;

import java.util.HashMap;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;

public class Monster {
	private Logger logger = LoggerFactory.getLogger(getClass());
	private static boolean debug = true;
	
	private static Monster monster = null;
	
	private IInfoflowCFG iCfg = null;
	private ISourceSinkManager sourcesSinks = null;
	private HashMap<SootMethod, Set<Unit>> sources = null;
	private HashMap<SootMethod, Set<Unit>> sinks = null;
	private HashMap<SootMethod, Set<SootField>> methodReachableSFsMap = null;
	
	private Monster(){}
	
	public static Monster v(){
		if(monster == null){
			monster = new Monster();
		}
		return monster;
	}
	
	public void init(IInfoflowCFG iCfg, ISourceSinkManager sourcesSinks, 
			HashMap<SootMethod, Set<Unit>> sources, HashMap<SootMethod, Set<Unit>> sinks, 
			HashMap<SootMethod, Set<SootField>> methodReachableSFsMap){
		this.iCfg = iCfg;
		this.sourcesSinks = sourcesSinks;
		this.sources = sources;
		this.sinks = sinks;
		this.methodReachableSFsMap = methodReachableSFsMap;
	}
}
