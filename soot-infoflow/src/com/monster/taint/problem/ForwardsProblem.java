package com.monster.taint.problem;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import javax.xml.parsers.ParserConfigurationException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Local;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.Scene;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;

import com.monster.taint.MethodHub;
import com.monster.taint.MethodHubType;
import com.monster.taint.Monster;
import com.monster.taint.output.TaintOutput;
import com.monster.taint.path.MethodPath;
import com.monster.taint.state.MethodState;
import com.monster.taint.state.PathState;
import com.monster.taint.state.TaintValue;
import com.monster.taint.state.TaintValueType;
import com.monster.taint.target.TargetManager;
import com.monster.taint.wrapper.InvokingHistoryPool;
import com.monster.taint.wrapper.MyWrapper;

public class ForwardsProblem {
	private Logger logger = LoggerFactory.getLogger(getClass());
	private MethodPath methodPath = null;
	private ArrayList<Unit> units = null;
	private int startIndex = -1;
	private int stopIndex = -1;
	
	/**
	 * [startIndex, stopIndex)
	 * @param units
	 * @param startIndex
	 * @param stopIndex
	 * @param methodPath
	 */
	public ForwardsProblem(ArrayList<Unit> units, int startIndex, int stopIndex, MethodPath methodPath){
		this.methodPath = methodPath;
		this.units = units;
		this.startIndex = startIndex;
		this.stopIndex = stopIndex;
	}
	
	public void solve(){
		int currIndex = startIndex;
		while(currIndex < stopIndex){
			Unit currUnit = this.units.get(currIndex);
			
		
			//at the beginning of method, assign parameters to
			//local variables
			if(currUnit instanceof IdentityStmt){
				if(this.methodPath.getMethodHub().getType() != MethodHubType.INVOKING_RETURN){
					handleIdentityStmt((IdentityStmt) currUnit);
				}
			}
			
			if(currUnit instanceof AssignStmt){
				handleAssignStmt((AssignStmt) currUnit);
			}
		
			//virtualinvoke $r6.<java.lang.String: boolean equals(java.lang.Object)>($r1);
			if(currUnit instanceof InvokeStmt){
				InvokeExpr invokeExpr = ((InvokeStmt) currUnit).getInvokeExpr();
				handleInvokeExpr(invokeExpr, null, currUnit);
			}
			
			if(currUnit instanceof ReturnStmt){
				handleReturnStmt((ReturnStmt) currUnit);
				break;
			}
			
			if(currUnit instanceof ReturnVoidStmt){
				break;
			}
			
			currIndex++;
		}
	}

	/**
	 * Handle the IdentifyStmt, for this type Stmt,
	 * the left value can never be instance field, static field
	 * @param stmt
	 */
	private void handleIdentityStmt(IdentityStmt stmt){
		Value rv = stmt.getRightOp();
		Value lv = stmt.getLeftOp();
		
		if(this.methodPath.getMethodHub().isSource()){
			//the MethodHub is source container
			if(this.methodPath.isActivationUnit(stmt)){
				//taint lv
				TaintValue sourceTV = new TaintValue(TaintValueType.TAINT, lv, stmt, this.methodPath);
				this.methodPath.getPathState().addTaintValue(sourceTV);
			}
		}else{
			//taint lv depend on initial MethodState
			//the MethodHub is called by others, get the initial MethodState
			MethodState initMethodState = this.methodPath.getMethodHub().getInitState();
			if(initMethodState != null){
				//$r0 := @this: type;
				if(rv instanceof ThisRef){
					ArrayList<TaintValue> thisTVs = initMethodState.getThisTVs();
					for(TaintValue tv : thisTVs){
						TaintValue newTV = new TaintValue(TaintValueType.TAINT, lv, stmt, this.methodPath);
						newTV.appendAllSootField(tv.getAccessPath());
						newTV.setInDependence(tv);
						this.methodPath.getPathState().addTaintValue(newTV);
					}
				}else if(rv instanceof ParameterRef){
					//e.g. $r1 := @parameter1: type;
					int argIndex = ((ParameterRef) rv).getIndex();
					ArrayList<TaintValue> paramTVs = initMethodState.getArgTVs(argIndex);
					for(TaintValue tv : paramTVs){
						TaintValue newTV = new TaintValue(TaintValueType.TAINT, lv, stmt, this.methodPath);
						newTV.appendAllSootField(tv.getAccessPath());
						newTV.setInDependence(tv);
						this.methodPath.getPathState().addTaintValue(newTV);
					}
				}
			}
		}
	}
	
	private void handleAssignStmt(AssignStmt stmt){
		Value lv = stmt.getLeftOp();
		Value rv = stmt.getRightOp();
	
		//e.g. $z0 = virtualinvoke $r6.<java.lang.String: boolean equals(java.lang.Object)>($r1);
		if(rv instanceof InvokeExpr){
			handleInvokeExpr((InvokeExpr) rv, lv, stmt);
		}else{
			//$r3 = <de.ub0r.android.smsdroid.Message: java.lang.String[] PROJECTION_READ>;
			
			//the MethodHub is source container, actually this case doesn't exist at this moment
			if(this.methodPath.getMethodHub().isSource()){
				if(this.methodPath.isActivationUnit(stmt)){
					//lv is static field
					if(lv instanceof StaticFieldRef){
						StaticFieldRef sfr = (StaticFieldRef) lv;
						TaintValue sourceTV = new TaintValue(TaintValueType.TAINT, null, stmt, this.methodPath);
						sourceTV.appendSootField(sfr.getField());
						this.methodPath.getPathState().addTaintValue(sourceTV);
					}else if(lv instanceof InstanceFieldRef){
						InstanceFieldRef ifr = (InstanceFieldRef) lv;
						TaintValue sourceTV = new TaintValue(TaintValueType.TAINT, ifr.getBase(), stmt, this.methodPath);
						sourceTV.appendSootField(ifr.getField());
						boolean added = this.methodPath.getPathState().addTaintValue(sourceTV);
						if(added){
							//added sourceTV successfully, trigger backwards alias analysis
							startBackwardsProblem(sourceTV, stmt);
						}
					}else if(lv instanceof ArrayRef){
						//add taint to the array ref
						ArrayRef ar = (ArrayRef) lv;
						Value arrayBase = ar.getBase();
						TaintValue sourceTV = new TaintValue(TaintValueType.TAINT, arrayBase, stmt, this.methodPath);
						this.methodPath.getPathState().addTaintValue(sourceTV);
					}else{
						//not static field, instance field, must be Local?
						assert(lv instanceof Local);
						TaintValue sourceTV = new TaintValue(TaintValueType.TAINT, lv, stmt, this.methodPath);
						this.methodPath.getPathState().addTaintValue(sourceTV);
					}
				}
			}
			
			//right value is tainted or its field is tainted
			//right value can be local, instance field, static field, array ref
			//constant expr,cast expr
			boolean rvTainted = false;
			if(rv instanceof Local){
				rvTainted |= handleRVLocal(lv, (Local) rv, stmt);
			}else if(rv instanceof StaticFieldRef){
				rvTainted |= handleRVStaticFieldRef(lv, (StaticFieldRef) rv, stmt);
			}else if(rv instanceof InstanceFieldRef){
				rvTainted |= handleRVInstanceFieldRef(lv, (InstanceFieldRef) rv, stmt);
			}else if(rv instanceof ArrayRef){
				rvTainted |= handleRVArrayRef(lv, (ArrayRef) rv, stmt);
			}else if(rv instanceof CastExpr){
				rvTainted |= handleRVCastExpr(lv, (CastExpr) rv, stmt);
			}else if(rv instanceof Constant ||
					rv instanceof NewExpr){
				this.methodPath.getPathState().eraseTaintOf(lv, stmt);
			}
			if(!rvTainted)
				this.methodPath.getPathState().eraseTaintOf(lv, stmt);
		}
	}

	/**
	 * The invoke stmt (assign stmt) is the activation unit, 
	 * instead of calling the method, initialize the path state.
	 *  
	 * @param invokeExpr
	 * @param retValue
	 * @param currUnit
	 * 
	 * Only called by this.handleInvokeExpr
	 */
	private void handleInvokeExprAtAcivationUnit(InvokeExpr invokeExpr, Value retValue, Unit currUnit){
		assert(this.methodPath.getMethodHub().getType() == MethodHubType.INVOKING_RETURN);
		Value thisBase = null;
		List<Value> args = invokeExpr.getArgs();
		int argsCount = invokeExpr.getArgCount();
		
		if(invokeExpr instanceof InstanceInvokeExpr){
			thisBase = ((InstanceInvokeExpr) invokeExpr).getBase();
		}

		//if this is a source container, just taint retValue
		if(this.methodPath.getMethodHub().isSource()){
			assert(retValue != null);
			this.taintLV(retValue, currUnit, TaintValueType.TAINT, null, null, null, new ArrayList<SootField>());
		}else{
			//this is not a source container, so this is a callee of certain method
			MethodState initState = this.methodPath.getMethodHub().getInitState();
			ArrayList<ArrayList<TaintValue>> argsTVs = initState.getAllArgsTVs();
			ArrayList<TaintValue> thisTVs = initState.getThisTVs();
			ArrayList<TaintValue> retTVs = initState.getRetTVs();
			ArrayList<TaintValue> staticTVs = initState.getStaticTVs();
			ArrayList<TaintValue> newProducedTVs = new ArrayList<TaintValue>();
		
			//collect new this tvs
			if(thisBase != null && thisTVs.size() > 0){
				newProducedTVs.addAll(this.addNewProducedTVs(thisBase, TaintValueType.TAINT, thisTVs, currUnit));
			}
			
			//collect args' tvs
			if(argsCount > 0){
				assert(argsTVs.size() == argsCount);
				for(int i = 0; i < argsCount; i++){
					Value argValue = args.get(i);
					if(argValue instanceof Constant)
						continue;
					assert(argValue instanceof Local);
					ArrayList<TaintValue> newArgTVs = argsTVs.get(i);
					newProducedTVs.addAll(this.addNewProducedTVs(argValue, TaintValueType.TAINT, newArgTVs, currUnit));
				}
			}
		
			//collect new static tvs
			newProducedTVs.addAll(this.addNewProducedTVs(null, TaintValueType.TAINT, staticTVs, currUnit));
			
			//collect new ret  tvs
			if(retValue != null && retTVs.size() > 0){
				for(TaintValue retTV : retTVs){
					TaintValue newTV = null;
					//retValue can be Local, InstanceFieldRef, StaticFieldRef, ArrayRef
					if(retValue instanceof Local){
						newTV = new TaintValue(TaintValueType.TAINT, retValue, currUnit, this.methodPath);
					}else if(retValue instanceof InstanceFieldRef){
						InstanceFieldRef ifr = (InstanceFieldRef) retValue;
						newTV = new TaintValue(TaintValueType.TAINT, ifr.getBase(), currUnit, this.methodPath);
						newTV.appendSootField(ifr.getField());
					}else if(retValue instanceof StaticFieldRef){
						StaticFieldRef sfr = (StaticFieldRef) retValue;
						newTV = new TaintValue(TaintValueType.TAINT, null, currUnit, this.methodPath);
						newTV.appendSootField(sfr.getField());
					}else if(retValue instanceof ArrayRef){
						ArrayRef ar = (ArrayRef) retValue;
						newTV = new TaintValue(TaintValueType.TAINT, ar.getBase(), currUnit, this.methodPath);
					}
					assert(newTV != null);
					newTV.appendAllSootField(retTV.getAccessPath());
					newTV.setRetDependence(retTV);
					if(this.methodPath.getPathState().addTaintValue(newTV)){
						newProducedTVs.add(newTV);
					}
				}
			}
		
			for(TaintValue tv : newProducedTVs){
				if(tv.isStaticField() && tv.getAccessPath().size() > 1){
					startBackwardsProblem(tv, currUnit);
				}else if((!tv.isStaticField()) && tv.getAccessPath().size() > 0){
					startBackwardsProblem(tv, currUnit);
				}
			}
		}
		
	}
	
	private void handleInvokeExpr(InvokeExpr invokeExpr, Value retValue, Unit currUnit){
		//before invoking method, check whether currUnit is the activation unit.
		if(this.methodPath.isActivationUnit(currUnit)){
			this.handleInvokeExprAtAcivationUnit(invokeExpr, retValue, currUnit);
			return;
		}
		
		Value thisBase = null;
		List<Value> args = invokeExpr.getArgs();
		int argsCount = invokeExpr.getArgCount();
		
		if(invokeExpr instanceof InstanceInvokeExpr){
			thisBase = ((InstanceInvokeExpr) invokeExpr).getBase();
		}
		
		SootMethod method = invokeExpr.getMethod();
		SootMethodRef smr = invokeExpr.getMethodRef();
		
		//method is null, do point to analysis 
		if(method == null && invokeExpr instanceof InstanceInvokeExpr){
			String oldSignature = smr.getSignature();
			PointsToAnalysis pta = Monster.v().getPTA();
			PointsToSet pts = null;
			Set<Type> types = null;
			pts = pta.reachingObjects((Local) thisBase);

			if(pts != null){
				types = pts.possibleTypes();
				if(types != null){
					for(Type type : types){
						String newClassName = type.toString();
						String[] tokens = oldSignature.split(":");
						tokens[0] = "<" + newClassName + ":";
						String newSignature = tokens[0] + tokens[1];
						method = Scene.v().getMethod(newSignature);
						if(method != null){
							logger.info("**** found point to {}", newSignature);
							break;
						}
					}
				}
			}
		}
	
		String className = null;
		String subSignature = null;
		
		//method is still null, try TaintWrapper
		if(method == null){
			className = smr.declaringClass().getName();
			subSignature = smr.getSubSignature().getString();
		}else{
			className = method.getDeclaringClass().getName();
			subSignature = method.getSubSignature();
		}
	
		/*
		if(method != null && method.getSignature().equals("<android.os.Bundle: java.lang.Object get(java.lang.String)>")){
			logger.info("Break Point!");
		}
		
		if(method != null && method.getSignature().equals("<android.telephony.SmsMessage: android.telephony.SmsMessage createFromPdu(byte[])>")){
			logger.info("Break Point!");
		}
		
		if(method != null && method.getSignature().equals("<android.content.ContentValues: void put(java.lang.String,java.lang.String)>")){
			logger.info("Break Point!");
		}
		*/
	
		boolean isInTaintWrapper = false;
		//Regardless of method is null or not, check whether in taint wrapper
		//in excludelist, do ignore invoking
		if(MyWrapper.v().isInExcludeList(className, subSignature)){
			isInTaintWrapper = true;
			return;
		}else if(MyWrapper.v().isInClassList(className, subSignature)){
			isInTaintWrapper = true;
			if(retValue == null) return;
			//taint retValue if any argument is tainted
			boolean isTainted = false;
			for(int i = 0; i < argsCount && !isTainted; i++){
				Value arg = args.get(i);
				if(arg instanceof Constant)
					continue;
				assert(arg instanceof Local);
				ArrayList<TaintValue> tvs = this.methodPath.getPathState().getTVsBasedOnLocal((Local) arg);
				for(int j = 0; j < tvs.size() && !isTainted; j++){
					TaintValue tv = tvs.get(j);
					if(tv.getType() == TaintValueType.TAINT){
						taintLV(retValue, currUnit, TaintValueType.TAINT, tv, null, null, null);
						isTainted = true;
						break;
					}
				}
			}
			//no taints with args, check thisBase
			if(!isTainted && thisBase != null){
				assert(thisBase instanceof Local);
				ArrayList<TaintValue> tvs = this.methodPath.getPathState().getTVsBasedOnLocal((Local) thisBase);
				for(TaintValue tv : tvs){
					if(tv.getType() == TaintValueType.TAINT){
						taintLV(retValue, currUnit, TaintValueType.TAINT, tv, null, null, null);
						isTainted = true;
						break;
					}
				}
			}
			return;
		}else if(MyWrapper.v().isInCollectionPutList(className, subSignature)){
			boolean isTainted = false;
			for(int i = 0; i < argsCount && !isTainted; i++){
				Value arg = args.get(i);
				if(arg instanceof Constant)
					continue;
				assert(arg instanceof Local);
				ArrayList<TaintValue> tvs = this.methodPath.getPathState().getTVsBasedOnLocal((Local) arg);
				for(int j = 0; j < tvs.size() && !isTainted; j++){
					TaintValue tv = tvs.get(j);
					if(tv.getType() == TaintValueType.TAINT){
						taintLV(thisBase, currUnit, TaintValueType.TAINT, tv, null, null, null);
						isTainted = true;
						break;
					}
				}
			}
			return;
		}else if(MyWrapper.v().isInKillList(className, subSignature)){
			isInTaintWrapper = true;
			return;
		}
		
		if(!isInTaintWrapper && method != null &&
				!method.isPhantom() && !InvokingHistoryPool.v().isInBlacklist(method)){
				
			//check looping first
			if(!this.methodPath.getMethodHub().causeLoop(method)){
				//initial method state
				MethodState initState = new MethodState(argsCount);
				
				ArrayList<TaintValue> thisTVs = null;
				boolean thisTainted = false;
				if(thisBase != null){
					assert(thisBase instanceof Local);
					thisTVs = this.methodPath.getPathState().getTVsBasedOnLocal((Local) thisBase);
					for(TaintValue thisTV : thisTVs){
						if(thisTV.getType() == TaintValueType.TAINT){
							thisTainted = true;
							initState.addThisTV(thisTV);
						}
					}
				}
				
				ArrayList<ArrayList<TaintValue>> argsTVs = new ArrayList<ArrayList<TaintValue>>(argsCount);
				for(int i = 0; i < argsCount; i++){
					argsTVs.add(new ArrayList<TaintValue>());
				}
				boolean argsTainted = false;
				for(int i = 0; i <argsCount; i++){
					Value arg = args.get(i);
					if(arg instanceof Constant)
						continue;
					assert(arg instanceof Local) : arg.getClass().toString() + arg.toString();
					ArrayList<TaintValue> argTVs = this.methodPath.getPathState().getTVsBasedOnLocal((Local) arg);
					argsTVs.get(i).addAll(argTVs);
				}
				for(int i = 0; i < argsCount; i++){
					ArrayList<TaintValue> argTVs = argsTVs.get(i);
					for(int j = 0; j < argTVs.size(); j++){
						TaintValue argTV = argTVs.get(j);
						if(argTV.getType() == TaintValueType.TAINT){
							argsTainted = true;
							initState.addArgTV(i, argTV);
						}
					}
				}
				
				ArrayList<TaintValue> staticTVs = this.methodPath.getPathState().getStaticTVs();
				Set<SootField> reachableStaticFields = Monster.v().getReachableStaticFields(method);
				boolean staticFieldsReachable = false;
				if(reachableStaticFields != null){
					for(TaintValue staticTV : staticTVs){
						if(reachableStaticFields.contains(staticTV.getAccessPath().get(0))){
							if(staticTV.getType() == TaintValueType.TAINT){
								staticFieldsReachable = true;
								initState.addStaticTV(staticTV);
							}
						}
					}
				}
			
				//it's so tough to get here, so we have to start new method
				if(thisTainted || argsTainted || staticFieldsReachable){
					//the initstate has been initialized, get the actual 
					//taint values passed into new method hub
					ArrayList<TaintValue> inThisTVs = initState.getThisTVs();
					ArrayList<ArrayList<TaintValue>> inArgsTVs = initState.getAllArgsTVs();
					ArrayList<TaintValue> inStaticTVs = initState.getStaticTVs();
					
					//check whether this is a sink invoking
					if(Monster.v().isSink((Stmt) currUnit)){
						logger.info("Oh, my God! We arrived at Sink {}!", invokeExpr);
						//record the taint propagation
						try {
							TaintOutput.v().collectTaint(inThisTVs, inArgsTVs, inStaticTVs, currUnit, 
									this.methodPath.getMethodHub().getMethod(), this.methodPath.getPathID());
						} catch (Exception e) {
							e.printStackTrace();
						}
						return;
					}
					
					//check component invoking
					if(TargetManager.v().isStartComponent(className, subSignature)){
						logger.info("****Start another component****{}", currUnit);
						return;
					}
			
				
					//if method has no active body, just return
					if(!method.hasActiveBody()){
						//logger.info("Try to invoke \"{}\" with taint values, but it has no active body, just return.", method.toString());
						return;
					}
		
					logger.info("Invoke {} with taint values: \n thisTVs: {} \n argsTVs: {} \n staticTVs: {}", 
							method.toString(), thisTainted, argsTainted, staticFieldsReachable);
					//start new method hub
					MethodHub newHub = new MethodHub(method, null, MethodHubType.CALLED_FORWARD, 
							false, this.methodPath.getMethodHub());
					newHub.setInitState(initState);
					newHub.start();
					newHub.mergePathStates();
					
					//return from the method, handle the exit method state with current path state
					MethodState exitState = newHub.getExitState();
					assert(exitState != null);
					ArrayList<TaintValue> outThisTVs = exitState.getThisTVs();
					ArrayList<ArrayList<TaintValue>> outArgsTVs = exitState.getAllArgsTVs();
					ArrayList<TaintValue> outStaticTVs = exitState.getStaticTVs();
					ArrayList<TaintValue> retTVs = exitState.getRetTVs();
					
					//compare the out*TVs with in*TVs to add new produced taint values
					//and untainted related taint values
					ArrayList<TaintValue> newProducedTVs = new ArrayList<TaintValue>();
			
					//this
					if(thisBase != null){
						ArrayList<TaintValue> newProducedThisTVs = PathState.getNewProducedTVs(inThisTVs, outThisTVs);
						ArrayList<TaintValue> untaintedThisTVs = PathState.getUntaintedNonStaticTVs(inThisTVs, outThisTVs);
						//untainted some taint valued if this forwards problems is not
						//triggered by backwards problem
						if(!this.triggeredByBProblem(this.methodPath.getMethodHub())){
							this.untaintedTVs(untaintedThisTVs);
						}
						//add new produced this's taint values
						newProducedTVs.addAll(this.addNewProducedTVs(thisBase, TaintValueType.TAINT, newProducedThisTVs, currUnit));
					}
				
					//args
					if(argsCount > 0){
						assert(outArgsTVs.size() == argsCount);
						for(int i = 0; i < argsCount; i++){
							Value argValue = args.get(i);
							if(argValue instanceof Constant)
								continue;
							assert(argValue instanceof Local);
							ArrayList<TaintValue> newArgTVs = PathState.getNewProducedTVs(inArgsTVs.get(i), outArgsTVs.get(i));
							ArrayList<TaintValue> untaintedArgTVs = PathState.getUntaintedNonStaticTVs(inArgsTVs.get(i), outArgsTVs.get(i));
							if(!this.triggeredByBProblem(this.methodPath.getMethodHub())){
								this.untaintedTVs(untaintedArgTVs);
							}
							newProducedTVs.addAll(this.addNewProducedTVs(argValue, TaintValueType.TAINT, newArgTVs, currUnit));
						}
					}
				
					//static fields
					ArrayList<TaintValue> newProducedStaticTVs = PathState.getNewProducedTVs(inStaticTVs, outStaticTVs);
					ArrayList<TaintValue> untaintedStaticTVs = PathState.getUntaintedNonStaticTVs(inStaticTVs, outStaticTVs);
					if(!this.triggeredByBProblem(this.methodPath.getMethodHub())){
						this.untaintedTVs(untaintedStaticTVs);
					}
					newProducedTVs.addAll(this.addNewProducedTVs(null, TaintValueType.TAINT, newProducedStaticTVs, currUnit));
					
					//return value
					if(retValue != null){
						for(TaintValue retTV : retTVs){
							TaintValue newTV = null;
							//retValue can be Local, InstanceFieldRef, StaticFieldRef, ArrayRef
							if(retValue instanceof Local){
								newTV = new TaintValue(TaintValueType.TAINT, retValue, currUnit, this.methodPath);
							}else if(retValue instanceof InstanceFieldRef){
								InstanceFieldRef ifr = (InstanceFieldRef) retValue;
								newTV = new TaintValue(TaintValueType.TAINT, ifr.getBase(), currUnit, this.methodPath);
								newTV.appendSootField(ifr.getField());
							}else if(retValue instanceof StaticFieldRef){
								StaticFieldRef sfr = (StaticFieldRef) retValue;
								newTV = new TaintValue(TaintValueType.TAINT, null, currUnit, this.methodPath);
								newTV.appendSootField(sfr.getField());
							}else if(retValue instanceof ArrayRef){
								ArrayRef ar = (ArrayRef) retValue;
								newTV = new TaintValue(TaintValueType.TAINT, ar.getBase(), currUnit, this.methodPath);
							}
							assert(newTV != null);
							newTV.appendAllSootField(retTV.getAccessPath());
							newTV.setRetDependence(retTV);
							if(this.methodPath.getPathState().addTaintValue(newTV)){
								newProducedTVs.add(newTV);
							}
						}
					}
					
					//for the new produced taint values, start backwards problems if it is necessary
					logger.info("{} return with {} new taint values.", method, newProducedTVs.size());
					if(newProducedStaticTVs.size() > 0){
						for(TaintValue tv : newProducedTVs){
							if(tv.isStaticField() && tv.getAccessPath().size() > 1){
								startBackwardsProblem(tv, currUnit);
							}else if((!tv.isStaticField()) && tv.getAccessPath().size() > 0){
								startBackwardsProblem(tv, currUnit);
							}
						}
					}else{
						InvokingHistoryPool.v().addToBlocklist(method);
					}
				}
			}
		}
	}
	
	private void untaintedTVs(ArrayList<TaintValue> tvs){
		for(TaintValue tv : tvs){
			this.methodPath.getPathState().deleteTaintValue(tv);
		}
	}
	
	/**
	 * this must be called by after invoking
	 * @param base : must be Local
	 * @param type
	 * @param newProduecedTVs
	 * @param currUnit
	 * @return
	 */
	private ArrayList<TaintValue> addNewProducedTVs(Value base, TaintValueType type, ArrayList<TaintValue> newProduecedTVs, Unit currUnit){
		assert(base instanceof Local || base == null);
		ArrayList<TaintValue> result = new ArrayList<TaintValue>();
		for(TaintValue tv : newProduecedTVs){
			TaintValue newTV = new TaintValue(type, base, currUnit, this.methodPath);
			newTV.appendAllSootField(tv.getAccessPath());
			newTV.setRetDependence(tv);
			if(this.methodPath.getPathState().addTaintValue(newTV))
				result.add(newTV);
		}
		return result;
	}
	
	private void handleReturnStmt(ReturnStmt stmt){
		Value value = stmt.getOp();
		assert(value != null);
		this.methodPath.setRetValue(value);
	}
	
	private void startBackwardsProblem(TaintValue triggerTV, Unit currUnit){
		int currIndex = this.units.indexOf(currUnit); 
		BackwardsProblem bProblem = new BackwardsProblem(this.units, currIndex - 1, this.methodPath, triggerTV);
		bProblem.solve();
	}

	/**
	 * Right value of an assign stmt is local, get the taint values based
	 * on rv and taint lv if necessary.
	 * @param lv
	 * @param rv
	 * @param currUnit
	 * @return true if rv is tainted or its field is tainted before currUnit
	 */
	private boolean handleRVLocal(Value lv, Local rv, Unit currUnit){
		ArrayList<TaintValue> tvs = this.methodPath.getPathState().getTVsBasedOnLocal(rv);
		for(TaintValue tv : tvs){
			ArrayList<SootField> accessPath = tv.getAccessPath();
			int currIndex = this.units.indexOf(currUnit);
			int maxIndex = tv.getMaxIndexOnDependencePath();
			if(currIndex > maxIndex){
				//lv's type is TAINT
				taintLV(lv, currUnit, TaintValueType.TAINT, tv, null, null, accessPath);
			}else{
				//lv's type is ALIAS
				taintLV(lv, currUnit, TaintValueType.ALIAS, tv, null, null, accessPath);
			}
		}
		return tvs.size() > 0;
	}


	/**
	 * Right value of an assign stmt is static field, get the taint values related
	 * to rv, and taint lv if necessary.
	 * @param lv
	 * @param rv
	 * @param currUnit
	 * @return true if rv is tainted or its field is tainted before currUnit
	 */
	private boolean handleRVStaticFieldRef(Value lv, StaticFieldRef rv, Unit currUnit){
		SootField sootField = rv.getField();
		ArrayList<TaintValue> tvs = this.methodPath.getPathState().getTVsBasedOnStaticField(sootField);
		int currIndex = this.units.indexOf(currUnit);
		for(TaintValue tv : tvs){
			ArrayList<SootField> accessPath = tv.getAccessPath();
			int maxIndex = tv.getMaxIndexOnDependencePath();
			if(accessPath.size() == 1){
				if(currIndex > maxIndex){
					taintLV(lv, currUnit, TaintValueType.TAINT, tv, null, null, null);
				}else{
					taintLV(lv, currUnit, TaintValueType.ALIAS, tv, null, null, null);
				}
			}else{
				assert(accessPath.size() > 1);
				ArrayList<SootField> restFields = new ArrayList<SootField>();
				for(int i = 1; i < accessPath.size(); i++){
					restFields.add(accessPath.get(i));
				}
				if(currIndex > maxIndex){
					taintLV(lv, currUnit, TaintValueType.TAINT, tv, null, null, restFields);
				}else{
					taintLV(lv, currUnit, TaintValueType.ALIAS, tv, null, null, restFields);
				}
			}
		}
		return tvs.size() > 0;
	}

	/**
	 * Right value of an assign stmt is instance field, get the taint values related
	 * to rv, and taint lv if necessary
	 * @param lv
	 * @param rv
	 * @param currUnit
	 * @return true if rv is tainted or its field is tainted before currUnit
	 */
	private boolean handleRVInstanceFieldRef(Value lv, InstanceFieldRef rv, Unit currUnit){
		ArrayList<TaintValue> tvs = this.methodPath.getPathState().getTVsBasedOnInstanceFieldRef(rv);
		int currIndex = this.units.indexOf(currUnit);
		for(TaintValue tv : tvs){
			ArrayList<SootField> accessPath = tv.getAccessPath();
			int maxIndex = tv.getMaxIndexOnDependencePath();
			if(accessPath.size() == 1){
				if(currIndex > maxIndex){
					taintLV(lv, currUnit, TaintValueType.TAINT, tv, null, null, null);
				}else{
					taintLV(lv, currUnit, TaintValueType.ALIAS, tv, null, null, null);
				}
			}else{
				assert(accessPath.size() > 1);
				ArrayList<SootField> restFields = new ArrayList<SootField>();
				for(int i = 1; i < accessPath.size(); i++){
					restFields.add(accessPath.get(i));
				}
				if(currIndex > maxIndex){
					taintLV(lv, currUnit, TaintValueType.TAINT, tv, null, null, restFields);
				}else{
					taintLV(lv, currUnit, TaintValueType.ALIAS, tv, null, null, restFields);
				}
			}
		}
		return tvs.size() > 0;
	}

	/**
	 * Right value of an assign stmt is an array ref, get the taint values related
	 * to rv, and taint lv if necessary
	 * @param lv
	 * @param rv
	 * @param currUnit
	 * @return true if rv is tainted or its field is tainted before currUnit
	 */
	private boolean handleRVArrayRef(Value lv, ArrayRef rv, Unit currUnit){
		return handleRVLocal(lv, (Local) rv.getBase(), currUnit);
	}

	/**
	 * Right value of an assign stmt is cast expt, get the taint values related
	 * to rv, and taint lv if necessary
	 * @param lv
	 * @param rv
	 * @param currUnit
	 * @return true if rv is tainted or its field is tainted before currUnit
	 */
	private boolean handleRVCastExpr(Value lv, CastExpr rv, Unit currUnit){
		Value value = rv.getOp();
		if(value instanceof Local){
			return handleRVLocal(lv, (Local) value, currUnit);
		}else{
			//Constant, such as IntConstant
			return false;
		}
	}
	
	/**
	 * Certain left value should be tainted based on dependences, and append
	 * rvAccessPath to lv
	 * 
	 * @param lv
	 * @param activationUnit
	 * @param type
	 * @param dependence
	 * @param inDependence
	 * @param retDependence
	 * @param rvAccessPath
	 */
	private void taintLV(Value lv, Unit activationUnit, TaintValueType type, 
			TaintValue dependence, TaintValue inDependence, TaintValue retDependence,
			ArrayList<SootField> rvAccessPath){
		TaintValue newTV = null;
		boolean added = false;
		if(lv instanceof StaticFieldRef){
			StaticFieldRef sfr = (StaticFieldRef) lv;
			newTV = new TaintValue(type, null, activationUnit, this.methodPath);
			newTV.appendSootField(sfr.getField());
		}else if(lv instanceof InstanceFieldRef){
			InstanceFieldRef ifr = (InstanceFieldRef) lv;
			newTV = new TaintValue(type, ifr.getBase(), activationUnit, this.methodPath);
			newTV.appendSootField(ifr.getField());
		}else if(lv instanceof ArrayRef){
			ArrayRef ar = (ArrayRef) lv;
			newTV = new TaintValue(type, ar.getBase(), activationUnit, this.methodPath);
		}else if(lv instanceof Local){
			newTV = new TaintValue(type, lv, activationUnit, this.methodPath);
		}
		
		if(newTV == null){
			return;
		}
		
		newTV.appendAllSootField(rvAccessPath);
		newTV.setDependence(dependence);
		newTV.setInDependence(inDependence);
		newTV.setRetDependence(retDependence);
		added = this.methodPath.getPathState().addTaintValue(newTV);
		if(added && newTV.getType() == TaintValueType.TAINT){
			if((newTV.isStaticField() && newTV.getAccessPath().size() > 1)
					|| (!newTV.isStaticField() && newTV.getAccessPath().size() > 0)){
				this.startBackwardsProblem(newTV, activationUnit);
			}
		}
	}
	
	private boolean triggeredByBProblem(MethodHub hub){
		if(hub.getType() == MethodHubType.CALLED_BACKWARD){
			return true;
		}
		if(hub.getPreHub() == null)
			return false;
		return triggeredByBProblem(hub.getPreHub());
	}

}
