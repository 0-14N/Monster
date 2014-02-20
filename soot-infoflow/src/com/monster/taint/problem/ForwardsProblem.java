package com.monster.taint.problem;

import java.util.ArrayList;

import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ThisRef;

import com.monster.taint.MethodHubType;
import com.monster.taint.path.MethodPath;
import com.monster.taint.state.MethodState;
import com.monster.taint.state.TaintValue;
import com.monster.taint.state.TaintValueType;

public class ForwardsProblem {
	private MethodPath methodPath = null;
	private ArrayList<Unit> units = null;
	private int startIndex = -1;
	private int stopIndex = -1;
	private MethodHubType type;
	
	public ForwardsProblem(ArrayList<Unit> units, int startIndex, int stopIndex, 
			MethodHubType type, MethodPath methodPath){
		this.methodPath = methodPath;
		this.units = units;
		this.startIndex = startIndex;
		this.stopIndex = stopIndex;
		this.type = type;
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
		}
	}
	
	private void handleInvokeExpr(InvokeExpr invokeExpr, Value retValue){
		
	}
	
	private void handleReturnStmt(ReturnStmt stmt){
		
	}
}
