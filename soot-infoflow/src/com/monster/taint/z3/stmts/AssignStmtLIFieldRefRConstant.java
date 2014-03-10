package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.Constant;
import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLIFieldRef;
import com.monster.taint.z3.stmts.atom.ASRConstant;

public class AssignStmtLIFieldRefRConstant{
	private ASLIFieldRef lIFieldRef = null;
	private ASRConstant rConstant = null;
	
	public AssignStmtLIFieldRefRConstant(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, InstanceFieldRef lIFieldRef, Constant rConstant){
		this.lIFieldRef = new ASLIFieldRef(writer, fileGenerator, stmtIdx, lIFieldRef);
		this.rConstant = new ASRConstant(writer, fileGenerator, stmtIdx, rConstant);
	}
	
	public void jet(){
		this.lIFieldRef.jet();
		this.rConstant.jet();
	}
}
