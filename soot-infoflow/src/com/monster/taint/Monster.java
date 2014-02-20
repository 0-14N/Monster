package com.monster.taint;

import java.io.IOException;
import java.util.HashMap;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.monster.taint.mstcallback.MSTCallback;
import com.monster.taint.mstcallback.MSTCallbackFactory;

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
	/*
	 * The source can also be some callbacks (e.g. Service.onStart)
	 */
	private Set<MSTCallback> mstCallBacks = null;
	
	private Monster(){}
	
	public static Monster v(){
		if(monster == null){
			monster = new Monster();
		}
		return monster;
	}

	public void initMSTCallbacks(){
		try {
			this.mstCallBacks = MSTCallbackFactory.v().createMSTCallbacks();
		} catch (IOException ioe) {
			if(this.debug)
				logger.error("create MSTCallbacks error!");
		}
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
	
	public void start(){
		
	}

	/**
	 * whether a method with 'signature', and paramIdx(st)
	 * parameter is tainted
	 * @param signature
	 * @param paramIdx
	 * @return
	 */
	public boolean isMSTCallback(String signature, int paramIdx){
		boolean isMSTCallback = false;
		for(MSTCallback mstCallback : mstCallBacks){
			if(mstCallback.hitMe(signature, paramIdx)){
				isMSTCallback = true;
				break;
			}
		}
		return isMSTCallback;
	}
}
