package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class ASLSFieldRef {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private StaticFieldRef lSFieldRef = null;
	
	private String sFieldRefName = null;
	private Z3Type lZ3Type = null;
	
	public ASLSFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, StaticFieldRef lSFieldRef){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.lSFieldRef = lSFieldRef;
	}
	
	public void jet(){
		sFieldRefName = fileGenerator.getRenameOf(lSFieldRef, true, stmtIdx);
		lZ3Type = Z3MiscFunctions.v().z3Type(lSFieldRef.getField().getType());
		if(!fileGenerator.getDeclaredVariables().contains(sFieldRefName)
				&& lZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(sFieldRefName, lZ3Type));
					fileGenerator.getDeclaredVariables().add(sFieldRefName);
		}
	}
}
