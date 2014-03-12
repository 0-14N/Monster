package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;
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
		
		writer.println(Z3MiscFunctions.v().getCommonAssertEqual(lLocal.getLLocalName(), rLocal.getRLocalName()));
	}
}
