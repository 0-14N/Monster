package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.Expr;
import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLIFieldRef;
import com.monster.taint.z3.stmts.atom.ASRExpr;

public class AssignStmtLIFieldRefRExpr{
	private ASLIFieldRef lIFieldRef = null;
	private ASRExpr rExpr = null;
	
	public AssignStmtLIFieldRefRExpr(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, InstanceFieldRef lIFieldRef, Expr rExpr){
		this.lIFieldRef = new ASLIFieldRef(writer, fileGenerator, stmtIdx, lIFieldRef);
		this.rExpr = new ASRExpr(writer, fileGenerator, stmtIdx, rExpr);
	}
	
	public void jet(){
		this.lIFieldRef.jet();
		this.rExpr.jet();
	}
}
