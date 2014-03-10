package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

import soot.jimple.InstanceFieldRef;

public class ASLIFieldRef {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private InstanceFieldRef lIFieldRef = null;
	
	private Z3Type lZ3Type = null;
	private String iFieldRefName = null;
	
	public ASLIFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, InstanceFieldRef lIFieldRef){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.lIFieldRef = lIFieldRef;
	}
	
	public void jet(){
		lZ3Type = Z3MiscFunctions.v().z3Type(lIFieldRef.getField().getType());
		iFieldRefName = fileGenerator.getRenameOf(lIFieldRef, true, stmtIdx);
		if(!fileGenerator.getDeclaredVariables().contains(iFieldRefName)
				&& lZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(iFieldRefName, lZ3Type));
			fileGenerator.getDeclaredVariables().add(iFieldRefName);
		}
	}
}
