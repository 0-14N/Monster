package com.monster.taint;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.monster.taint.mstcallback.MSTCallback;
import com.monster.taint.mstcallback.MSTCallbackFactory;
import com.monster.taint.state.MethodState;
import com.monster.taint.wrapper.MyWrapper;

import soot.PointsToAnalysis;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.IdentityStmt;
import soot.jimple.Stmt;
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
	
	public static String DUMMYMAIN_SIGNATURE = "<dummyMainClass: void dummyMainMethod()>";
	public static int LENGTH_THRESHOD_NUMERATOR = 2;
	public static int LENGTH_THRESHOD_DENOMINATOR = 3;
	
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
	//source and sink trigger units
	private ArrayList<Unit> sourceTriggerUnits = new ArrayList<Unit>();
	private ArrayList<Unit> sinkTriggerUnits = new ArrayList<Unit>();
	
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
		
		//collect source trigger units
		Iterator<Entry<SootMethod, Set<Unit>>> sourceIter = this.sources.entrySet().iterator();
		while(sourceIter.hasNext()){
			Entry<SootMethod, Set<Unit>> entry = sourceIter.next();
			SootMethod sourceContainer = entry.getKey();
			Set<Unit> sourceUnits = entry.getValue();
			for(Unit sourceUnit : sourceUnits){
				SootMethodNode sourceNode = new SootMethodNode(sourceContainer, null, null);
				this.collectSourceSinkTriggerUnits(sourceContainer, sourceUnit, sourceNode, this.sourceTriggerUnits);
			}
		}
		
		//collect sink trigger units
		Iterator<Entry<SootMethod, Set<Unit>>> sinkIter = this.sinks.entrySet().iterator();
		while(sinkIter.hasNext()){
			Entry<SootMethod, Set<Unit>> entry = sinkIter.next();
			SootMethod sinkContainer = entry.getKey();
			Set<Unit> sinkUnits = entry.getValue();
			for(Unit sinkUnit : sinkUnits){
				SootMethodNode sinkNode = new SootMethodNode(sinkContainer, null, null);
				this.collectSourceSinkTriggerUnits(sinkContainer, sinkUnit, sinkNode, this.sinkTriggerUnits);
			}
		}
		
		createSourceMethodHubs();
		
		for(MethodHub methodHub : this.sourceMethodHubs){
			methodHub.start();
			methodHub.mergePathStates();
			MethodState exitState = methodHub.getExitState();
			/*
			logger.info("Analyzed source {}, begin backwards!", methodHub);
			ArrayList<MethodHub> callerHubs = getCallerHubsOf(methodHub);
			for(MethodHub callerHub : callerHubs){
				callerHub.setInitState(exitState);
				stepBackwards(callerHub);
			}
			*/
		}
	}

	private void collectSourceSinkTriggerUnits(SootMethod smOnSourcePath, Unit u, 
			SootMethodNode methodNode, ArrayList<Unit> collectedUnits){
		if(smOnSourcePath.getSignature().equals(Monster.DUMMYMAIN_SIGNATURE)){
			if(!collectedUnits.contains(u)){
				collectedUnits.add(u);
			}
			return;
		}
		Set<Unit> callerUnits = iCfg.getCallersOf(smOnSourcePath);
		for(Unit callUnit : callerUnits){
			try{
				SootMethod caller = iCfg.getMethodOf(callUnit);
				if(!methodNode.isMyAncestor(caller)){
					SootMethodNode callerNode = new SootMethodNode(caller, methodNode, null);
					methodNode.addSon(callerNode);
					collectSourceSinkTriggerUnits(caller, callUnit, callerNode, collectedUnits);
				}
			}catch(Exception e){
				logger.info(e.toString());
			}
		}
	}
	
	/**
	 * create MethodHubs for sources, a MethodHub for each source unit,
	 * maybe it should be optimized in future. 
	 */
	private void createSourceMethodHubs(){
		Iterator<Entry<SootMethod, Set<Unit>>> iter = sources.entrySet().iterator();
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
	 * To avoid looping, we should check it.
	 * @param methodHub
	 * @return
	 */
	private ArrayList<MethodHub> getCallerHubsOf(MethodHub methodHub){
		ArrayList<MethodHub> callerHubs = new ArrayList<MethodHub>();
		SootMethod method = methodHub.getMethod();
		Set<Unit> callerUnits = this.iCfg.getCallersOf(method);
		for(Unit callerUnit : callerUnits){
			SootMethod caller = this.iCfg.getMethodOf(callerUnit);
			//check loop existence
			if(!methodHub.causeLoop(caller) && !caller.isPhantom()){
				MethodHub callerHub = new MethodHub(caller, callerUnit, MethodHubType.INVOKING_RETURN, false, methodHub);
				callerHubs.add(callerHub);
			}
		}
		return callerHubs;
	}

	/**
	 * Analyze currHub and continuously analyze currHub's callers
	 * 
	 * @param currHub : currHub's init state must be initialized before
	 * 					calling this method
	 */
	private void stepBackwards(MethodHub currHub){
		if(currHub.getMethod().getSignature().equals(Monster.DUMMYMAIN_SIGNATURE)){
			//logger.info("Arrived at dummyMainMethod! Start analyzing \"dummyMainMethod\"");
			//currHub.start();
		}else{
			currHub.start();
			currHub.mergePathStates();
			MethodState exitState = currHub.getExitState();
			ArrayList<MethodHub> callerMethodHubs = getCallerHubsOf(currHub);
			for(MethodHub callerMethodHub : callerMethodHubs){
				callerMethodHub.setInitState(exitState);
				stepBackwards(callerMethodHub);
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
	
	public IInfoflowCFG getICFG(){
		return this.iCfg;
	}
	
	
	public Set<SootField> getReachableStaticFields(SootMethod method){
		return this.methodReachableSFsMap.get(method);
	}

	public boolean isSink(Stmt smt){
		return this.sourcesSinks.isSink(smt, this.iCfg);
	}
}
