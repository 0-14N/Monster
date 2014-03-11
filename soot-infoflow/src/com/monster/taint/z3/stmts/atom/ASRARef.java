package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class ASRARef {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private ArrayRef rARef = null;
	
	private String aRefName = null;
	private Z3Type rZ3Type = null;
	
	public ASRARef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, ArrayRef rARef){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.rARef = rARef;
	}
	
	public void jet(){
		aRefName = fileGenerator.getRenameOf(rARef, false, stmtIdx);
		rZ3Type = Z3MiscFunctions.v().z3Type(rARef.getBase().getType());
		if(!fileGenerator.getDeclaredVariables().contains(aRefName) 
				&& rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getArrayDeclareStmt(aRefName, rZ3Type));
			fileGenerator.getDeclaredVariables().add(aRefName);
		}else if(!fileGenerator.getDeclaredVariables().contains(aRefName) 
				&& rZ3Type == Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getArrayDeclareStmt(aRefName, Z3Type.Z3String));
			fileGenerator.getDeclaredVariables().add(aRefName);
		}
	}
	
	public ArrayRef getRARef(){
		return this.rARef;
	}
	
	public Z3Type getRZ3Type(){
		return this.rZ3Type;
	}
	
	public String getARefName(){
		return this.aRefName;
	}
}
