package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.ArrayRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRLocal;

public class AssignStmtLARefRLocal{
	private PrintWriter writer = null;
	private ASLARef lARef = null;
	private ASRLocal rLocal = null;
	
	public AssignStmtLARefRLocal(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, ArrayRef lARef, Local rLocal){
		this.writer = writer;
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rLocal = new ASRLocal(writer, fileGenerator, stmtIdx, rLocal);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rLocal.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * a[i] = l
	 * (assert (= (select a i) l))
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lARef.getLARefStr());
		sb.append(" ");
		sb.append(rLocal.getRLocalName());
		sb.append("))");
		return sb.toString();
	}
}
