package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRLocal;

import soot.Local;

public class AssignStmtLLocalRLocal{
	private PrintWriter writer = null;
	
	private ASLLocal lLocal = null;
	private ASRLocal rLocal = null;
	
	public AssignStmtLLocalRLocal(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, Local rLocal){
		this.writer = writer;
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rLocal = new ASRLocal(writer, fileGenerator, stmtIdx, rLocal);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rLocal.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * r1 = r2
	 * (assert (= r1 r2))
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lLocal.getLLocalName());
		sb.append(" ");
		sb.append(rLocal.getRLocalName());
		sb.append("))");
		return sb.toString();
	}
}
