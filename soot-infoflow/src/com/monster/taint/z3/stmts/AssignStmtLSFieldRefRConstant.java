package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.Constant;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLSFieldRef;
import com.monster.taint.z3.stmts.atom.ASRConstant;


public class AssignStmtLSFieldRefRConstant{
	private ASLSFieldRef lSFieldRef = null;
	private ASRConstant rConstant = null;
	
	public AssignStmtLSFieldRefRConstant(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, StaticFieldRef lSFieldRef, Constant rConstant){
		this.lSFieldRef = new ASLSFieldRef(writer, fileGenerator, stmtIdx, lSFieldRef);
		this.rConstant = new ASRConstant(writer, fileGenerator, stmtIdx, rConstant);
	}
	
	public void jet(){
		this.lSFieldRef.jet();
		this.rConstant.jet();
	}
}
