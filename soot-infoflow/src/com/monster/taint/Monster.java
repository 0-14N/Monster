package com.monster.taint;

import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.monster.taint.mstcallback.MSTCallback;
import com.monster.taint.mstcallback.MSTCallbackFactory;
import com.monster.taint.wrapper.MyWrapper;

import soot.PointsToAnalysis;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.IdentityStmt;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;

/**
 * This is the manager of analyzing.
 * 
 * Q: Why "Monster"?
 * A: I was listening Eminem's "Monster" ... 
 * 
 * @author chenxiong
 *
 */
public class Monster {
	private Logger logger = LoggerFactory.getLogger(getClass());
	private static boolean debug = true;
	
	private static Monster monster = null;
	
	private IInfoflowCFG iCfg = null;
	private ISourceSinkManager sourcesSinks = null;
	private PointsToAnalysis pta = null;
	private HashMap<SootMethod, Set<Unit>> sources = null;
	private HashMap<SootMethod, Set<Unit>> sinks = null;
	private HashMap<SootMethod, Set<SootField>> methodReachableSFsMap = null;
	/*
	 * The source can also be some callbacks (e.g. Service.onStart)
	 */
	private Set<MSTCallback> mstCallBacks = null;
	/**
	 * Analysis starts at sources, each source is contained in a method.
	 * We use sourceMethodHubs to store those methods contain sources.
	 */
	private Set<MethodHub> sourceMethodHubs = null;
	
	private Monster(){}
	
	public static Monster v(){
		if(monster == null){
			monster = new Monster();
		}
		return monster;
	}

	/**
	 * this method must be called first! 
	 * even before calling "init"
	 */
	public void initMSTCallbacks(){
		try {
			this.mstCallBacks = MSTCallbackFactory.v().createMSTCallbacks();
		} catch (IOException ioe) {
			if(this.debug)
				logger.error("create MSTCallbacks error!");
		}
	}
	
	public void init(IInfoflowCFG iCfg, ISourceSinkManager sourcesSinks, 
			PointsToAnalysis pta, EasyTaintWrapper taintWrapper,
			HashMap<SootMethod, Set<Unit>> sources, HashMap<SootMethod, Set<Unit>> sinks, 
			HashMap<SootMethod, Set<SootField>> methodReachableSFsMap){
		this.iCfg = iCfg;
		this.sourcesSinks = sourcesSinks;
		this.pta = pta;
		MyWrapper.v().init(taintWrapper);
		this.sources = sources;
		this.sinks = sinks;
		this.methodReachableSFsMap = methodReachableSFsMap;
		this.sourceMethodHubs = new HashSet<MethodHub>();
	}
	
	public void start(){
		
		//TODO collect source trigger units
		
		//TODO collect sink trigger units
		
		createSourceMethodHubs();
		for(MethodHub methodHub : this.sourceMethodHubs){
			methodHub.start();
			
			//TODO backwards to "dummyMain"
		}
	}

	/**
	 * create MethodHubs for sources, a MethodHub for each source unit,
	 * maybe it should be optimized in future. 
	 */
	private void createSourceMethodHubs(){
		Iterator iter = sources.entrySet().iterator();
		while(iter.hasNext()){
			Entry<SootMethod, Set<Unit>> entry = (Entry<SootMethod, Set<Unit>>) iter.next();
			SootMethod method = entry.getKey();
			Set<Unit> sourceUnits = entry.getValue();
			for(Unit unit : sourceUnits){
				MethodHubType type = null;
				if(unit instanceof IdentityStmt)
					type = MethodHubType.CALLED_FORWARD;
				else
					type = MethodHubType.INVOKING_RETURN;
				MethodHub methodHub = new MethodHub(method, unit, type, true, null);
				this.sourceMethodHubs.add(methodHub);
			}
		}
	}

	/**
	 * whether a method with 'signature', and paramIdx(st)
	 * parameter is tainted
	 * @param signature
	 * @param paramIdx
	 * @return
	 */
	//[start] public boolean isMSTCallback(String signature, int paramIdx)
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
	//[end]
	
	public PointsToAnalysis getPTA(){
		return this.pta;
	}
	
	public Set<SootField> getReachableStaticFields(SootMethod method){
		return this.methodReachableSFsMap.get(method);
	}
}
