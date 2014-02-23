package com.monster.taint.problem;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import javax.media.jai.UntiledOpImage;

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
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;

import com.monster.taint.MethodHub;
import com.monster.taint.MethodHubType;
import com.monster.taint.Monster;
import com.monster.taint.path.MethodPath;
import com.monster.taint.state.MethodState;
import com.monster.taint.state.PathState;
import com.monster.taint.state.TaintValue;
import com.monster.taint.state.TaintValueType;
import com.monster.taint.wrapper.MyWrapper;

public class ForwardsProblem {
	private Logger logger = LoggerFactory.getLogger(getClass());
	private MethodPath methodPath = null;
	private ArrayList<Unit> units = null;
	private int startIndex = -1;
	private int stopIndex = -1;
	
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
				handleIdentityStmt((IdentityStmt) currUnit);
			}
			
			if(currUnit instanceof AssignStmt){
				handleAssignStmt((AssignStmt) currUnit);
			}
		
			//virtualinvoke $r6.<java.lang.String: boolean equals(java.lang.Object)>($r1);
			if(currUnit instanceof InvokeExpr){
				handleInvokeExpr((InvokeExpr) currUnit, null, currUnit);
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
					assert(argIndex > 0);
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
						TaintValue sourceTV = new TaintValue(TaintValueType.STATIC_FIELD, null, stmt, this.methodPath);
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
			}else if(rv instanceof Constant){
				this.methodPath.getPathState().eraseTaintOf(lv, stmt);
			}
			if(!rvTainted)
				this.methodPath.getPathState().eraseTaintOf(lv, stmt);
		}
	}
	
	private void handleInvokeExpr(InvokeExpr invokeExpr, Value retValue, Unit currUnit){
		assert(invokeExpr != null);
		Value thisBase = null;
		List<Value> args = invokeExpr.getArgs();
		int argsCount = invokeExpr.getArgCount();
		int currIndex = this.units.indexOf(currUnit);
		
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
				assert(arg instanceof Local);
				ArrayList<TaintValue> tvs = this.methodPath.getPathState().getTVsBasedOnLocal((Local) arg);
				for(int j = 0; j < tvs.size() && !isTainted; j++){
					TaintValue tv = tvs.get(j);
					TaintValue ultimateTV = tv.getUltimateDependence();
					int ultimateIndex = this.units.indexOf(ultimateTV.getActivationUnit());
					if(currIndex > ultimateIndex){
						//taint retValue and break
						taintLV(retValue, currUnit, TaintValueType.TAINT, ultimateTV, null);
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
					TaintValue ultimateTV = tv.getUltimateDependence();
					int ultimateIndex = this.units.indexOf(ultimateTV.getActivationUnit());
					if(currIndex > ultimateIndex){
						//taint retValue and break
						taintLV(retValue, currUnit, TaintValueType.TAINT, ultimateTV, null);
						isTainted = true;
						break;
					}
				}
			}
		}else if(MyWrapper.v().isInKillList(className, subSignature)){
			isInTaintWrapper = true;
			return;
		}
		
		if(!isInTaintWrapper && method != null){
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
						int ultimateIndex = this.units.indexOf(thisTV.getUltimateDependence().getActivationUnit());
						if(currIndex > ultimateIndex){
							thisTainted = true;
							initState.addThisTV(thisTV);
						}
					}
				}
				
				ArrayList<ArrayList<TaintValue>> argsTVs = new ArrayList<ArrayList<TaintValue>>(argsCount);
				boolean argsTainted = false;
				for(int i = 0; i <argsCount; i++){
					Value arg = args.get(i);
					assert(arg instanceof Local);
					ArrayList<TaintValue> argTVs = this.methodPath.getPathState().getTVsBasedOnLocal((Local) arg);
					argsTVs.set(i, argTVs);
				}
				for(int i = 0; i < argsCount && !argsTainted; i++){
					ArrayList<TaintValue> argTVs = argsTVs.get(i);
					for(int j = 0; j < argTVs.size() && !argsTainted; j++){
						TaintValue argTV = argTVs.get(j);
						int ultimateIndex = this.units.indexOf(argTV.getUltimateDependence().getActivationUnit());
						if(currIndex > ultimateIndex){
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
							int ultimateIndex = this.units.indexOf(staticTV.getUltimateDependence().getActivationUnit());
							if(currIndex > ultimateIndex){
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
					
					
					//start new method hub
					MethodHub newHub = new MethodHub(method, null, MethodHubType.CALLED_FORWARD, 
							false, this.methodPath.getMethodHub());
					newHub.setInitState(initState);
					newHub.start();
					newHub.mergePathStates();
					
					//TODO return from the method, handle the exit method state with current path state
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
						//untainted some this taint values
						this.untaintedTVs(untaintedThisTVs);
						//add new produced this's taint values
						newProducedTVs.addAll(this.addNewProducedTVs(thisBase, TaintValueType.TAINT, newProducedThisTVs, currUnit));
					}
				
					//args
					if(argsCount > 0){
						assert(outThisTVs.size() == argsCount);
						for(int i = 0; i < argsCount; i++){
							Value argValue = args.get(i);
							ArrayList<TaintValue> newArgTVs = PathState.getNewProducedTVs(inArgsTVs.get(i), outArgsTVs.get(i));
							ArrayList<TaintValue> untaintedArgTVs = PathState.getUntaintedNonStaticTVs(inArgsTVs.get(i), outArgsTVs.get(i));
							this.untaintedTVs(untaintedArgTVs);
							newProducedTVs.addAll(this.addNewProducedTVs(argValue, TaintValueType.TAINT, newArgTVs, currUnit));
						}
					}
				
					//static fields
					ArrayList<TaintValue> newProducedStaticTVs = PathState.getNewProducedTVs(inStaticTVs, outStaticTVs);
					ArrayList<TaintValue> untaintedStaticTVs = PathState.getUntaintedNonStaticTVs(inStaticTVs, outStaticTVs);
					this.untaintedTVs(untaintedStaticTVs);
					newProducedTVs.addAll(this.addNewProducedTVs(null, TaintValueType.STATIC_FIELD, newProducedStaticTVs, currUnit));
					
					//return value
					if(retValue != null){
						newProducedTVs.addAll(this.addNewProducedTVs(retValue, TaintValueType.TAINT, retTVs, currUnit));
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
	
	private ArrayList<TaintValue> addNewProducedTVs(Value base, TaintValueType type, ArrayList<TaintValue> newProduecedTVs, Unit currUnit){
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
	
	private void startBackwardsProblem(TaintValue dependence, Unit currUnit){
		int currIndex = this.units.indexOf(currUnit); 
		BackwardsProblem bProblem = new BackwardsProblem(this.units, currIndex - 1, this.methodPath, dependence);
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
		boolean result = false;
		for(TaintValue tv : tvs){
			ArrayList<SootField> accessPath = tv.getAccessPath();
			int currIndex = this.units.indexOf(currUnit);
			TaintValue ultimateDependence = tv.getUltimateDependence();
			int ultimateIndex = this.units.indexOf(ultimateDependence.getActivationUnit());
			if(currIndex > ultimateIndex){
				//lv's type is TAINT
				taintLV(lv, currUnit, TaintValueType.TAINT, ultimateDependence, accessPath);
			}else{
				//lv's type is ALIAS
				taintLV(lv, currUnit, TaintValueType.ALIAS, tv, accessPath);
			}
		}
		return result;
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
			TaintValue ultimateDependence = tv.getUltimateDependence();
			int ultimateIndex = this.units.indexOf(ultimateDependence.getActivationUnit());
			if(accessPath.size() == 1){
				if(currIndex > ultimateIndex){
					taintLV(lv, currUnit, TaintValueType.TAINT, ultimateDependence, null);
				}else{
					taintLV(lv, currUnit, TaintValueType.ALIAS, tv, null);
				}
			}else{
				assert(accessPath.size() > 1);
				ArrayList<SootField> restFields = new ArrayList<SootField>();
				for(int i = 1; i < accessPath.size(); i++){
					restFields.add(accessPath.get(i));
				}
				if(currIndex > ultimateIndex){
					taintLV(lv, currUnit, TaintValueType.TAINT, tv, restFields);
				}else{
					taintLV(lv, currUnit, TaintValueType.ALIAS, tv, restFields);
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
			TaintValue ultimateDependence = tv.getUltimateDependence();
			int ultimateIndex = this.units.indexOf(ultimateDependence.getActivationUnit());
			if(accessPath.size() == 1){
				if(currIndex > ultimateIndex){
					taintLV(lv, currUnit, TaintValueType.TAINT, ultimateDependence, null);
				}else{
					taintLV(lv, currUnit, TaintValueType.ALIAS, tv, null);
				}
			}else{
				assert(accessPath.size() > 1);
				ArrayList<SootField> restFields = new ArrayList<SootField>();
				for(int i = 1; i < accessPath.size(); i++){
					restFields.add(accessPath.get(i));
				}
				if(currIndex > ultimateIndex){
					taintLV(lv, currUnit, TaintValueType.TAINT, tv, restFields);
				}else{
					taintLV(lv, currUnit, TaintValueType.ALIAS, tv, restFields);
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
		return handleRVLocal(lv, (Local) rv.getOp(), currUnit);
	}
	
	/**
	 * Certain left value should be tainted based on dependence, and append
	 * rvAccessPath to lv
	 *  
	 * @param lv : StaticFieldRef, InstanceFieldRef, ArrayRef, Local
	 * @param currUnit
	 * @param type
	 * @param dependence
	 * @param rvAccessPath
	 */
	private void taintLV(Value lv, Unit activationUnit, TaintValueType type, 
			TaintValue dependence, ArrayList<SootField> rvAccessPath){
		if(lv instanceof StaticFieldRef){
			StaticFieldRef sfr = (StaticFieldRef) lv;
			TaintValue newTV = new TaintValue(TaintValueType.STATIC_FIELD, null, activationUnit, this.methodPath);
			newTV.appendSootField(sfr.getField());
			newTV.appendAllSootField(rvAccessPath);
			newTV.setDependence(dependence);
			this.methodPath.getPathState().addTaintValue(newTV);
		}else if(lv instanceof InstanceFieldRef){
			InstanceFieldRef ifr = (InstanceFieldRef) lv;
			TaintValue newTV = new TaintValue(type, ifr.getBase(), activationUnit, this.methodPath);
			newTV.appendSootField(ifr.getField());
			newTV.appendAllSootField(rvAccessPath);
			newTV.setDependence(dependence);
			boolean added = this.methodPath.getPathState().addTaintValue(newTV);
			if(added){
				startBackwardsProblem(newTV, activationUnit);
			}
		}else if(lv instanceof ArrayRef){
			ArrayRef ar = (ArrayRef) lv;
			TaintValue newTV = new TaintValue(type, ar.getBase(), activationUnit, this.methodPath);
			newTV.appendAllSootField(rvAccessPath);
			this.methodPath.getPathState().addTaintValue(newTV);
		}else{
			assert(lv instanceof Local);
			TaintValue newTV = new TaintValue(type, lv, activationUnit, this.methodPath);
			newTV.appendAllSootField(rvAccessPath);
		}
	}

}
