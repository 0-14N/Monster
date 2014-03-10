package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class ASRIFieldRef {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private InstanceFieldRef rIFieldRef = null;
	
	private Z3Type rZ3Type = null;
	private String iFieldRefName = null;
	
	public ASRIFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, InstanceFieldRef rIFieldRef){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.rIFieldRef = rIFieldRef;
	}
	
	public void jet(){
		rZ3Type = Z3MiscFunctions.v().z3Type(rIFieldRef.getField().getType());
		iFieldRefName = fileGenerator.getRenameOf(rIFieldRef, false, stmtIdx);
		if(!fileGenerator.getDeclaredVariables().contains(iFieldRefName)
				&& rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(iFieldRefName, rZ3Type));
			fileGenerator.getDeclaredVariables().add(iFieldRefName);
		}
	}

	public Z3Type getRZ3Type(){
		return this.rZ3Type;
	}
	
	public String getIFieldRefName() {
		return iFieldRefName;
	}

	public InstanceFieldRef getRIFieldRef(){
		return this.rIFieldRef;
	}
}
