package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.Expr;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLSFieldRef;
import com.monster.taint.z3.stmts.atom.ASRExpr;


public class AssignStmtLSFieldRefRExpr{
	private ASLSFieldRef lSFieldRef = null;
	private ASRExpr rExpr = null;
	
	public AssignStmtLSFieldRefRExpr(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, StaticFieldRef lSFieldRef, Expr rExpr){
		this.lSFieldRef = new ASLSFieldRef(writer, fileGenerator, stmtIdx, lSFieldRef);
		this.rExpr = new ASRExpr(writer, fileGenerator, stmtIdx, rExpr);
	}
	
	public void jet(){
		this.lSFieldRef.jet();
		this.rExpr.jet();
	}
}
