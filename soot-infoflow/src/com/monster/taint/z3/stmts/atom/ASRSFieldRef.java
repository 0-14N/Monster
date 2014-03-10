package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class ASRSFieldRef {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private StaticFieldRef rSFieldRef = null;
	
	private String sFieldRefName = null;
	private Z3Type rZ3Type = null;
	
	public ASRSFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, StaticFieldRef rSFieldRef){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.rSFieldRef = rSFieldRef;
	}
	
	public void jet(){
		sFieldRefName = fileGenerator.getRenameOf(rSFieldRef, false, stmtIdx);
		rZ3Type = Z3MiscFunctions.v().z3Type(rSFieldRef.getField().getType());
		if(!fileGenerator.getDeclaredVariables().contains(sFieldRefName)
				&& rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(sFieldRefName, rZ3Type));
					fileGenerator.getDeclaredVariables().add(sFieldRefName);
		}
	}
	
	public StaticFieldRef getRSFieldRef(){
		return this.rSFieldRef;
	}
	
	public Z3Type getRZ3Type(){
		return this.rZ3Type;
	}
	
	public String getSFieldRefName(){
		return this.sFieldRefName;
	}
}
