package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLSFieldRef;
import com.monster.taint.z3.stmts.atom.ASRSFieldRef;


public class AssignStmtLSFieldRefRSFieldRef{
	private PrintWriter writer = null;
	private ASLSFieldRef lSFieldRef = null;
	private ASRSFieldRef rSFieldRef = null;
	
	public AssignStmtLSFieldRefRSFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, StaticFieldRef lSFieldRef, StaticFieldRef rSFieldRef){
		this.writer = writer;
		this.lSFieldRef = new ASLSFieldRef(writer, fileGenerator, stmtIdx, lSFieldRef);
		this.rSFieldRef = new ASRSFieldRef(writer, fileGenerator, stmtIdx, rSFieldRef);
	}
	
	public void jet(){
		this.lSFieldRef.jet();
		this.rSFieldRef.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * A.f = B.f2
	 * (assert (= A_f B_f2))
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lSFieldRef.getSFieldRefName());
		sb.append(" ");
		sb.append(rSFieldRef.getSFieldRefName());
		sb.append("))");
		return sb.toString();
	}
}
