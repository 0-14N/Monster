package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

import soot.jimple.ArrayRef;

public class ASLARef {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private ArrayRef lARef = null;
	
	private String aRefName = null;
	private Z3Type lZ3Type = null;
	
	public ASLARef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, ArrayRef lARef){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.lARef = lARef;
	}
	
	public void jet(){
		aRefName = fileGenerator.getRenameOf(lARef, true, stmtIdx);
		lZ3Type = Z3MiscFunctions.v().z3Type(lARef.getBase().getType());
		if(!fileGenerator.getDeclaredVariables().contains(aRefName) 
				&& lZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getArrayDeclareStmt(aRefName, lZ3Type));
			fileGenerator.getDeclaredVariables().add(aRefName);
		}
	}
}
