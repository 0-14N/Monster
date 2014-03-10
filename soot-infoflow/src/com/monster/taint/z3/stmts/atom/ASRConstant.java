package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import soot.jimple.Constant;

import com.monster.taint.z3.SMT2FileGenerator;

public class ASRConstant {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private Constant rConstant = null;
	
	public ASRConstant(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Constant rConstant){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.rConstant = rConstant;
	}
	
	public void jet(){
		
	}
}
