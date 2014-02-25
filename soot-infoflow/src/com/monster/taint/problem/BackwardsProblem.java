package com.monster.taint.problem;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.monster.taint.MethodHub;
import com.monster.taint.MethodHubType;
import com.monster.taint.Monster;
import com.monster.taint.path.MethodPath;
import com.monster.taint.state.MethodState;
import com.monster.taint.state.PathState;
import com.monster.taint.state.TaintValue;
import com.monster.taint.state.TaintValueType;
import com.monster.taint.wrapper.MyWrapper;

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
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.StaticFieldRef;

public class BackwardsProblem {
	private Logger logger = LoggerFactory.getLogger(getClass());
	private MethodPath methodPath = null;
	private ArrayList<Unit> units = null;
	private int startIndex = -1;
	private TaintValue triggerTV = null;
	private Unit currUnit = null;
	private int currIndex = -1;

	public BackwardsProblem(ArrayList<Unit> units, int startIndex, MethodPath methodPath, 
			TaintValue triggerTV){
		this.units = units;
		this.startIndex = startIndex;
		this.currIndex = startIndex;
		this.methodPath = methodPath;
		this.triggerTV = triggerTV;
		assert(this.triggerTV.getType() == TaintValueType.TAINT);
	}
	
	public void solve(){
		while(currIndex >= 0){
			currUnit = this.units.get(currIndex);
		
			//for backwards problem, we only concern AssignStmt and InvokeExpr
			if(currUnit instanceof AssignStmt){
				handleAssignStmt((AssignStmt) currUnit);
			}
			
			if(currUnit instanceof InvokeStmt){
				InvokeExpr invokeExpr = ((InvokeStmt) currUnit).getInvokeExpr();
				handleInvokeExpr(invokeExpr, null);
			}
			
			currIndex--;
		}
	}

	//[start] handleAssignStmt
	private void handleAssignStmt(AssignStmt stmt){
		if(this.methodPath.isActivationUnit(stmt)){
			return;
		}
		
		Value lv = stmt.getLeftOp();
		Value rv = stmt.getRightOp();
		
		if(rv instanceof InvokeExpr){
			handleInvokeExpr((InvokeExpr) rv, lv);
		}else{
			//lv is part of 'triggerTV', but not equals to
			if(this.isPartOfTV(lv, this.triggerTV)){
				ArrayList<SootField> appendFields = new ArrayList<SootField>();
				//lv can be Local, instance field, static field, array ref
				if(lv instanceof Local || lv instanceof ArrayRef){
					appendFields.addAll(this.triggerTV.getAccessPath());
				}else if(lv instanceof InstanceFieldRef || 
						lv instanceof StaticFieldRef){
					ArrayList<SootField> accessPath = this.triggerTV.getAccessPath();
					for(int i = 1; i < accessPath.size(); i++){
						appendFields.add(accessPath.get(i));
					}
				}
				
				this.handleNewAlias(rv, appendFields, this.triggerTV, currUnit, TaintValueType.ALIAS);
			}
			
			//rv is part of 'triggerTV', but not equal to
			if(this.isPartOfTV(rv, this.triggerTV)){
				ArrayList<SootField> appendFields = new ArrayList<SootField>();
				//rv can be Local, instance field, static field, array ref, cast expr
				if(rv instanceof Local || rv instanceof ArrayRef ||
						rv instanceof CastExpr){
					appendFields.addAll(this.triggerTV.getAccessPath());
				}else if(rv instanceof InstanceFieldRef || 
						rv instanceof StaticFieldRef){
					ArrayList<SootField> accessPath = this.triggerTV.getAccessPath();
					for(int i = 1; i < accessPath.size(); i++){
						appendFields.add(accessPath.get(i));
					}
				}
				this.handleNewAlias(lv, appendFields, this.triggerTV, currUnit, TaintValueType.ALIAS);
			}else if(this.isEqualTV(rv, this.triggerTV)){
				this.handleNewAlias(lv, new ArrayList<SootField>(), this.triggerTV, currUnit, TaintValueType.ALIAS);
			}
		}
	}
	//[end]

	//[start] handleNewAlias
	/**
	 * Found new alias, add it and start forwards problem, the new
	 * alias's dependence is this.triggerTV
	 * 
	 * @param value : Local, instance field, static field, array ref, cast expr
	 * @param appendFields : the fields should append to value
	 * @param dependence
	 * @param activationUnit
	 * @param type : default is alias, if value is a static field ref, then STATIC_FIELD
	 */
	private void handleNewAlias(Value value, ArrayList<SootField> appendFields, TaintValue dependence,
			Unit activationUnit, TaintValueType type){
		TaintValue newTV = null;
		if(value instanceof Local){
			newTV = new TaintValue(type, value, activationUnit, this.methodPath);
		}else if(value instanceof InstanceFieldRef){
			InstanceFieldRef ifr = (InstanceFieldRef) value;
			newTV = new TaintValue(type, ifr.getBase(), activationUnit, this.methodPath);
			newTV.appendSootField(ifr.getField());
		}else if(value instanceof StaticFieldRef){
			StaticFieldRef sfr = (StaticFieldRef) value;
			newTV = new TaintValue(type, null, activationUnit, this.methodPath);
			newTV.appendSootField(sfr.getField());
		}else if(value instanceof ArrayRef){
			ArrayRef ar = (ArrayRef) value;
			newTV = new TaintValue(type, ar.getBase(), activationUnit, this.methodPath);
		}else if(value instanceof CastExpr){
			CastExpr ce = (CastExpr) value;
			newTV = new TaintValue(type, ce.getOp(), activationUnit, this.methodPath);
		}
		assert(newTV != null);
		newTV.setDependence(dependence);
		newTV.appendAllSootField(appendFields);
		if(this.methodPath.getPathState().addTaintValue(newTV)){
			ForwardsProblem fP = new ForwardsProblem(this.units, this.units.indexOf(activationUnit) + 1, 
									this.startIndex, this.methodPath);
			fP.solve();
		}
	}
	//[end]

	//[start] isPartOfTv
	/**
	 * whether value is part of (not equal to) tv
	 * 
	 * @param value : can be Local, instance field, static field, array ref, cast expr
	 * @param tv
	 * @return
	 */
	private boolean isPartOfTV(Value value, TaintValue tv){
		if(value instanceof Local){
			if(tv.baseEquals(value) && tv.getAccessPath().size() > 0){
				return true;
			}
		}else if(value instanceof InstanceFieldRef){
			InstanceFieldRef ifr = (InstanceFieldRef) value;
			if(tv.baseEquals(ifr.getBase())){
				ArrayList<SootField> accessPath = tv.getAccessPath();
				if(accessPath.size() > 1 && accessPath.get(0).equals(ifr.getField())){
					return true;
				}
			}
		}else if(value instanceof StaticFieldRef){
			StaticFieldRef sfr = (StaticFieldRef) value;
			if(tv.isStaticField()){
				ArrayList<SootField> accessPath = tv.getAccessPath();
				if(accessPath.size() > 1 && accessPath.get(0).equals(sfr.getField())){
					return true;
				}
			}
		}else if(value instanceof ArrayRef){
			ArrayRef ar = (ArrayRef) value;
			if(tv.baseEquals(ar.getBase()) && tv.getAccessPath().size() > 0){
				return true;
			}
		}else if(value instanceof CastExpr){
			CastExpr ce = (CastExpr) value;
			if(tv.baseEquals(ce.getOp()) && tv.getAccessPath().size() > 0){
				return true;
			}
		}
		
		return false;
	}
	//[end]

	//[start] isEqualTV
	private boolean isEqualTV(Value value, TaintValue tv){
		if(value instanceof Local){
			if(tv.baseEquals(value) && tv.getAccessPath().size() == 0){
				return true;
			}
		}else if(value instanceof InstanceFieldRef){
			InstanceFieldRef ifr = (InstanceFieldRef) value;
			if(tv.baseEquals(ifr.getBase())){
				ArrayList<SootField> accessPath = tv.getAccessPath();
				if(accessPath.size() == 1 && accessPath.get(0).equals(ifr.getField())){
					return true;
				}
			}
		}else if(value instanceof StaticFieldRef){
			StaticFieldRef sfr = (StaticFieldRef) value;
			if(tv.isStaticField()){
				ArrayList<SootField> accessPath = tv.getAccessPath();
				if(accessPath.size() == 1 && accessPath.get(0).equals(sfr.getField())){
					return true;
				}
			}
		}else if(value instanceof ArrayRef){
			ArrayRef ar = (ArrayRef) value;
			if(tv.baseEquals(ar.getBase()) && tv.getAccessPath().size() == 0){
				return true;
			}
		}else if(value instanceof CastExpr){
			CastExpr ce = (CastExpr) value;
			if(tv.baseEquals(ce.getOp()) && tv.getAccessPath().size() == 0){
				return true;
			}
		}
		return false;
	}
	//[end]

	
	private void handleInvokeExpr(InvokeExpr invokeExpr, Value retValue){
		assert(invokeExpr != null);
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
				if(arg instanceof Constant) continue;
				assert(arg instanceof Local);
				ArrayList<TaintValue> tvs = this.methodPath.getPathState().getTVsBasedOnLocal((Local) arg);
				for(int j = 0; j < tvs.size() && !isTainted; j++){
					TaintValue tv = tvs.get(j);
					if(this.currIndex > tv.getMaxIndexOnDependencePath()){
						//taint retValue and break
						//this.handleNewTaintValue(retValue, new ArrayList<SootField>(), ultimateTV, currUnit, TaintValueType.ALIAS);
						this.taintLVWithoutBP(retValue, currUnit, TaintValueType.TAINT, tv, null, null, null);
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
					if(currIndex > tv.getMaxIndexOnDependencePath()){
						//taint retValue and break
						//this.handleNewTaintValue(retValue, new ArrayList<SootField>(), ultimateTV, currUnit, TaintValueType.ALIAS);
						this.taintLVWithoutBP(retValue, currUnit, TaintValueType.TAINT, tv, null, null, null);
						isTainted = true;
						break;
					}
				}
			}
		}else if(MyWrapper.v().isInKillList(className, subSignature)){
			isInTaintWrapper = true;
			return;
		}
		
		if(!isInTaintWrapper && method != null && !method.isPhantom()){
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
						thisTainted = true;
						initState.addThisTV(thisTV);
					}
				}
				
				ArrayList<ArrayList<TaintValue>> argsTVs = new ArrayList<ArrayList<TaintValue>>(argsCount);
				for(int i = 0; i < argsCount; i++){
					argsTVs.add(new ArrayList<TaintValue>());
				}
				boolean argsTainted = false;
				for(int i = 0; i < argsCount; i++){
					Value arg = args.get(i);
					if(arg instanceof Constant) continue;
					assert(arg instanceof Local);
					ArrayList<TaintValue> argTVs = this.methodPath.getPathState().getTVsBasedOnLocal((Local) arg);
					argsTVs.get(i).addAll(argTVs);
				}
				for(int i = 0; i < argsCount && !argsTainted; i++){
					ArrayList<TaintValue> argTVs = argsTVs.get(i);
					for(int j = 0; j < argTVs.size() && !argsTainted; j++){
						TaintValue argTV = argTVs.get(j);
						argsTainted = true;
						initState.addArgTV(i, argTV);
					}
				}
				
				ArrayList<TaintValue> staticTVs = this.methodPath.getPathState().getStaticTVs();
				Set<SootField> reachableStaticFields = Monster.v().getReachableStaticFields(method);
				boolean staticFieldsReachable = false;
				if(reachableStaticFields != null){
					for(TaintValue staticTV : staticTVs){
						if(reachableStaticFields.contains(staticTV.getAccessPath().get(0))){
							staticFieldsReachable = true;
							initState.addStaticTV(staticTV);
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
					MethodHub newHub = new MethodHub(method, null, MethodHubType.CALLED_BACKWARD, 
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
						//add new produced this's taint values
						newProducedTVs.addAll(this.addNewProducedTVs(thisBase, TaintValueType.ALIAS, newProducedThisTVs, currUnit));
					}
				
					//args
					if(argsCount > 0){
						assert(outThisTVs.size() == argsCount);
						for(int i = 0; i < argsCount; i++){
							Value argValue = args.get(i);
							if(argValue instanceof Constant) continue;
							ArrayList<TaintValue> newArgTVs = PathState.getNewProducedTVs(inArgsTVs.get(i), outArgsTVs.get(i));
							newProducedTVs.addAll(this.addNewProducedTVs(argValue, TaintValueType.ALIAS, newArgTVs, currUnit));
						}
					}
				
					//static fields
					ArrayList<TaintValue> newProducedStaticTVs = PathState.getNewProducedTVs(inStaticTVs, outStaticTVs);
					newProducedTVs.addAll(this.addNewProducedTVs(null, TaintValueType.ALIAS, newProducedStaticTVs, currUnit));
					
					//return value
					if(retValue != null){
						for(TaintValue retTV : retTVs){
							//retValue can be Local, InstanceFieldRef, StaticFieldRef, ArrayRef
							TaintValue newTV = null;
							if(retValue instanceof Local){
								newTV = new TaintValue(TaintValueType.ALIAS, retValue, currUnit, this.methodPath);
							}else if(retValue instanceof InstanceFieldRef){
								InstanceFieldRef ifr = (InstanceFieldRef) retValue;
								newTV = new TaintValue(TaintValueType.ALIAS, ifr.getBase(), currUnit, this.methodPath);
								newTV.appendSootField(ifr.getField());
							}else if(retValue instanceof StaticFieldRef){
								StaticFieldRef sfr = (StaticFieldRef) retValue;
								newTV = new TaintValue(TaintValueType.ALIAS, null, currUnit, this.methodPath);
								newTV.appendSootField(sfr.getField());
							}else if(retValue instanceof ArrayRef){
								ArrayRef ar = (ArrayRef) retValue;
								newTV = new TaintValue(TaintValueType.ALIAS, ar.getBase(), currUnit, this.methodPath);
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
					ForwardsProblem fP = new ForwardsProblem(this.units, this.currIndex + 1, this.startIndex, this.methodPath);
					fP.solve();
				}
			}
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
	
	private boolean taintLVWithoutBP(Value lv, Unit activationUnit, TaintValueType type, 
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
		}else{
			assert(lv instanceof Local);
			newTV = new TaintValue(type, lv, activationUnit, this.methodPath);
		}
		assert(newTV != null);
		newTV.appendAllSootField(rvAccessPath);
		newTV.setDependence(dependence);
		newTV.setInDependence(inDependence);
		newTV.setRetDependence(retDependence);
		added = this.methodPath.getPathState().addTaintValue(newTV);
		return added;
	}
}
