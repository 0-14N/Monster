package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import soot.jimple.Expr;

import com.monster.taint.z3.SMT2FileGenerator;

public class ASRExpr {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private Expr rExpr = null;
	
	public ASRExpr(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Expr rExpr){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.rExpr = rExpr;
	}
	
	public void jet(){
		
	}
	
	public Expr getRExpr(){
		return this.rExpr;
	}
}
