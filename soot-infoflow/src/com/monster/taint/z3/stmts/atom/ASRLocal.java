package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import soot.Local;
import soot.Type;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class ASRLocal {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private Local rLocal = null;
	
	private String rLocalName = null;
	private Type rType = null;
	private Z3Type rZ3Type = null;
	
	public ASRLocal(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local rLocal){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.rLocal = rLocal;
	}
	
	public void jet(){
		rLocalName = fileGenerator.getRenameOf(rLocal, false, stmtIdx);
		rType = rLocal.getType();
		rZ3Type = Z3MiscFunctions.v().z3Type(rType);
		if(!fileGenerator.getDeclaredVariables().contains(rLocalName) ){
			writer.println(Z3MiscFunctions.v().getVariableDeclareStmt(rLocalName, rZ3Type));
			fileGenerator.getDeclaredVariables().add(rLocalName);
		}
	}

	public String getRLocalName(){
		return this.rLocalName;
	}
	
	public Local getRLocal(){
		return this.rLocal;
	}
	
	public Z3Type getZ3Type(){
		return this.rZ3Type;
	}
}
