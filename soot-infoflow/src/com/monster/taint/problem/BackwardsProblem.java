package com.monster.taint.problem;

import java.util.ArrayList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.monster.taint.path.MethodPath;
import com.monster.taint.state.TaintValue;

import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;

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
	}
	
	public void solve(){
		while(currIndex >= 0){
			currUnit = this.units.get(currIndex);
		
			//for backwards problem, we only concern AssignStmt and InvokeExpr
			if(currUnit instanceof AssignStmt){
				handleAssignStmt((AssignStmt) currUnit);
			}
			
			if(currUnit instanceof InvokeExpr){
				handleInvokeExpr((InvokeExpr) currUnit, null);
			}
			
			currIndex--;
		}
	}
	
	private void handleAssignStmt(AssignStmt stmt){
		if(this.methodPath.isActivationUnit(stmt)){
			return;
		}
		
		Value lv = stmt.getLeftOp();
		Value rv = stmt.getRightOp();
		
		if(rv instanceof InvokeExpr){
			handleInvokeExpr((InvokeExpr) rv, lv);
		}else{
			
		}
	}
	
	private void handleInvokeExpr(InvokeExpr invokeExpr, Value retValue){
		
	}
}
