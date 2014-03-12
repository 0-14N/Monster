package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.Constant;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRConstant;

public class AssignStmtLLocalRConstant{
	private PrintWriter writer = null;
	private ASLLocal lLocal = null;
	private ASRConstant rConstant = null;
	
	public AssignStmtLLocalRConstant (PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, Constant rConstant){
		this.writer = writer;
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rConstant = new ASRConstant(writer, fileGenerator, stmtIdx, rConstant);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rConstant.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * r = "084"
	 * (assert (= r "084"))
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lLocal.getLLocalName());
		sb.append(" ");
		sb.append(rConstant.getConstStr());
		sb.append("))");
		return sb.toString();
	}
}
