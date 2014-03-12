package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLSFieldRef;
import com.monster.taint.z3.stmts.atom.ASRARef;


public class AssignStmtLSFieldRefRARef{
	private PrintWriter writer = null;
	private ASLSFieldRef lSFieldRef = null;
	private ASRARef rARef = null;
	
	public AssignStmtLSFieldRefRARef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, StaticFieldRef lSFieldRef, ArrayRef rARef){
		this.writer = writer;
		this.lSFieldRef = new ASLSFieldRef(writer, fileGenerator, stmtIdx, lSFieldRef);
		this.rARef = new ASRARef(writer, fileGenerator, stmtIdx, rARef);
	}
	
	public void jet(){
		this.lSFieldRef.jet();
		this.rARef.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * A.f = a[i]
	 * 
	 * (assert (= A_f (select a i)))
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lSFieldRef.getSFieldRefName());
		sb.append(" ");
		sb.append(rARef.getRARefStr());
		sb.append("))");
		return sb.toString();
	}
}
