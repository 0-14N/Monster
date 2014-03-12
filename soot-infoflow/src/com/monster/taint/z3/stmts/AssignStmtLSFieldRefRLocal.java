package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLSFieldRef;
import com.monster.taint.z3.stmts.atom.ASRLocal;


public class AssignStmtLSFieldRefRLocal{
	private PrintWriter writer = null;
	private ASLSFieldRef lSFieldRef = null;
	private ASRLocal rLocal = null;
	
	public AssignStmtLSFieldRefRLocal(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, StaticFieldRef lSFieldRef, Local rLocal){
		this.writer = writer;
		this.lSFieldRef = new ASLSFieldRef(writer, fileGenerator, stmtIdx, lSFieldRef);
		this.rLocal = new ASRLocal(writer, fileGenerator, stmtIdx, rLocal);
	}
	
	public void jet(){
		this.lSFieldRef.jet();
		this.rLocal.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * A.f = r
	 * (assert (= A_f r))
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lSFieldRef.getSFieldRefName());
		sb.append(" ");
		sb.append(rLocal.getRLocalName());
		sb.append("))");
		return sb.toString();
	}
}
