package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRSFieldRef;

public class AssignStmtLARefRSFieldRef{
	private PrintWriter writer = null;
	private ASLARef lARef = null;
	private ASRSFieldRef rSFieldRef = null;
	
	public AssignStmtLARefRSFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, ArrayRef lARef, StaticFieldRef rSFieldRef){
		this.writer = writer;
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rSFieldRef = new ASRSFieldRef(writer, fileGenerator, stmtIdx, rSFieldRef);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rSFieldRef.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * a[i] = A.f
	 * (assert (= (select a i) A_f))
	 * 
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lARef.getLARefStr());
		sb.append(" ");
		sb.append(rSFieldRef.getSFieldRefName());
		sb.append("))");
		return sb.toString();
	}
}
