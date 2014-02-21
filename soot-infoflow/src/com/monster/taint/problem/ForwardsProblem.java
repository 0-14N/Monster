package com.monster.taint.problem;

import java.util.ArrayList;

import soot.Local;
import soot.SootField;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;
import soot.jimple.infoflow.util.BaseSelector;

import com.monster.taint.path.MethodPath;
import com.monster.taint.state.MethodState;
import com.monster.taint.state.TaintValue;
import com.monster.taint.state.TaintValueType;

public class ForwardsProblem {
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
				handleInvokeExpr((InvokeExpr) currUnit, null);
			}
			
			if(currUnit instanceof ReturnStmt){
				handleReturnStmt((ReturnStmt) currUnit);
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
			handleInvokeExpr((InvokeExpr) rv, lv);
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
			if(rv instanceof Local){
				
			}else if(rv instanceof StaticFieldRef){
				
			}else if(rv instanceof InstanceFieldRef){
				
			}else if(rv instanceof ArrayRef){
				
			}else if(rv instanceof CastExpr){
				
			}else if(rv instanceof Constant){
				
			}
		}
	}
	
	private void handleInvokeExpr(InvokeExpr invokeExpr, Value retValue){
		
	}
	
	private void handleReturnStmt(ReturnStmt stmt){
		
	}
	
	private void startBackwardsProblem(TaintValue dependence, Unit currUnit){
		int currIndex = this.units.indexOf(currUnit); 
		BackwardsProblem bProblem = new BackwardsProblem(this.units, currIndex - 1, this.methodPath, dependence);
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
			if(accessPath.size() == 0){
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
			}else{
				taintLV(lv, currUnit, TaintValueType.ALIAS, tv, accessPath);
			}
		}
		return tvs.size() > 0;
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
		for(TaintValue tv : tvs){
			ArrayList<SootField> accessPath = tv.getAccessPath();
			if(accessPath.size() == 1){
				int currIndex = this.units.indexOf(currUnit);
				TaintValue ultimateDependence = tv.getUltimateDependence();
				int ultimateIndex = this.units.indexOf(ultimateDependence.getActivationUnit());
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
				taintLV(lv, currUnit, TaintValueType.ALIAS, tv, restFields);
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
		for(TaintValue tv : tvs){
			ArrayList<SootField> accessPath = tv.getAccessPath();
			if(accessPath.size() == 1){
				int currIndex = this.units.indexOf(currUnit);
				TaintValue ultimateDependence = tv.getUltimateDependence();
				int ultimateIndex = this.units.indexOf(ultimateDependence.getActivationUnit());
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
				taintLV(lv, currUnit, TaintValueType.ALIAS, tv, restFields);
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
	private boolean handleCastExpr(Value lv, CastExpr rv, Unit currUnit){
		return handleRVLocal(lv, (Local) rv.getOp(), currUnit);
	}
	
}
