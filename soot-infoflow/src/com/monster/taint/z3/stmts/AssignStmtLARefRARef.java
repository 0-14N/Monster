package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRARef;

public class AssignStmtLARefRARef{
	private PrintWriter writer = null;
	private ASLARef lARef = null;
	private ASRARef rARef = null;
	
	public AssignStmtLARefRARef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, ArrayRef lARef, ArrayRef rARef){
		this.writer = writer;
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rARef = new ASRARef(writer, fileGenerator, stmtIdx, rARef);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rARef.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * a[i] = b[j]
	 * (assert (= (select a i) (select b j)))
	 * 
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lARef.getLARefStr());
		sb.append(" ");
		sb.append(rARef.getRARefStr());
		sb.append("))");
		return sb.toString();
	}
}
