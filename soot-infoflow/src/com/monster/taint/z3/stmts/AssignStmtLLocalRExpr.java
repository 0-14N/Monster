package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;

import soot.Local;
import soot.jimple.Expr;

public class AssignStmtLLocalRExpr extends AssignStmtLLocal{
	private Expr expr = null;
	
	public AssignStmtLLocalRExpr(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, Expr expr){
		super(writer, fileGenerator, stmtIdx, lLocal);
		this.expr = expr;
	}
	
	public void jet(){
		super.jet();
	}
}
