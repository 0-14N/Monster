package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;
import soot.jimple.Constant;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRConstant;

public class AssignStmtLARefRConstant{
	private PrintWriter writer = null;
	private ASLARef lARef = null;
	private ASRConstant rConstant = null;
	
	public AssignStmtLARefRConstant(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, ArrayRef lARef, Constant rConstant){
		this.writer = writer;
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rConstant = new ASRConstant(writer, fileGenerator, stmtIdx, rConstant);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rConstant.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * s[i] = null;
	 * -- (assert (= (select s i) ""))
	 * 
	 * a[i] = 42
	 * -- (assert (= (select a i) 42))
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= (select ");
		sb.append(lARef.getARefName());
		sb.append(" ");
		sb.append(lARef.getIdxName());
		sb.append(")");
		sb.append(" ");
		sb.append(rConstant.getConstStr());
		sb.append("))");
		return sb.toString();
	}
}
