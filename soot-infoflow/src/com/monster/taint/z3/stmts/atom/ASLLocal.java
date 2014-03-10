package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import soot.Local;
import soot.Type;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class ASLLocal {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private Local lLocal = null;
	
	private String lLocalName = null;
	private Type lType = null;
	private Z3Type lZ3Type = null;
	
	public ASLLocal(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, Local lLocal){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.lLocal = lLocal;
		this.stmtIdx = stmtIdx;
	}
	
	public void jet(){
		lLocalName = fileGenerator.getRenameOf(lLocal, true, stmtIdx);
		lType = lLocal.getType();
		lZ3Type = Z3MiscFunctions.v().z3Type(lType);
		if(!fileGenerator.getDeclaredVariables().contains(lLocalName) 
				&& lZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(lLocalName, lZ3Type));
			fileGenerator.getDeclaredVariables().add(lLocalName);
		}
	}

	public Local getLLocal(){
		return this.lLocal;
	}
	
	public String getLLocalName(){
		return this.lLocalName;
	}
	
	public Z3Type getZ3Type(){
		return this.lZ3Type;
	}
}
