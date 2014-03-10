package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.Type;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class AssignStmtLLocal {
	protected PrintWriter writer = null;
	protected SMT2FileGenerator fileGenerator = null;
	protected int stmtIdx;
	protected Local lLocal = null;
	protected String lLocalName = null;
	protected Type lType = null;
	protected Z3Type lZ3Type = null;
	
	public AssignStmtLLocal(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, Local lLocal){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.lLocal = lLocal;
		this.stmtIdx = stmtIdx;
	}
	
	protected void declareLeftValue(){
		lLocalName = fileGenerator.getRenameOf(lLocal, true, stmtIdx);
		lType = lLocal.getType();
		lZ3Type = Z3MiscFunctions.v().z3Type(lType);
		//whether new variable declaration need
		if(!fileGenerator.getDeclaredVariables().contains(lLocalName) 
				&& lZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(lLocalName, lZ3Type));
			fileGenerator.getDeclaredVariables().add(lLocalName);
		}
	}
	
	public void jet() {
		declareLeftValue();
	}
}
