package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.Constant;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLSFieldRef;
import com.monster.taint.z3.stmts.atom.ASRConstant;


public class AssignStmtLSFieldRefRConstant{
	private PrintWriter writer = null;
	private ASLSFieldRef lSFieldRef = null;
	private ASRConstant rConstant = null;
	
	public AssignStmtLSFieldRefRConstant(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, StaticFieldRef lSFieldRef, Constant rConstant){
		this.writer = writer;
		this.lSFieldRef = new ASLSFieldRef(writer, fileGenerator, stmtIdx, lSFieldRef);
		this.rConstant = new ASRConstant(writer, fileGenerator, stmtIdx, rConstant);
	}
	
	public void jet(){
		this.lSFieldRef.jet();
		this.rConstant.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * A.f = "084"
	 * 
	 * (assert (= A_f "084"))
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lSFieldRef.getSFieldRefName());
		sb.append(" ");
		sb.append(rConstant.getConstStr());
		sb.append("))");
		return sb.toString();
	}
}
