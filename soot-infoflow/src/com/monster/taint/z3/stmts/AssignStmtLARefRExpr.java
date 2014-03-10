package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;
import soot.jimple.Expr;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRExpr;

public class AssignStmtLARefRExpr{
	private ASLARef lARef = null;
	private ASRExpr rExpr = null;
	
	public AssignStmtLARefRExpr(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, ArrayRef lARef, Expr rExpr){
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rExpr = new ASRExpr(writer, fileGenerator, stmtIdx, rExpr);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rExpr.jet();
	}
}
