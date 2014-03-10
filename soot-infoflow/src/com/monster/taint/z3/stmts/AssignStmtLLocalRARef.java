package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

import soot.Local;
import soot.jimple.ArrayRef;

public class AssignStmtLLocalRARef extends AssignStmtLLocal{
	private ArrayRef aRef = null;
	private String aRefName = null;
	private Z3Type rZ3Type = null;
	
	public AssignStmtLLocalRARef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, Local lLocal, ArrayRef aRef){
		super(writer, fileGenerator, stmtIdx, lLocal);
		this.aRef = aRef;
	}
	
	public void jet(){
		super.jet();
		aRefName = fileGenerator.getRenameOf(aRef, false, stmtIdx);
		rZ3Type = Z3MiscFunctions.v().z3Type(aRef.getBase().getType());
		if(!fileGenerator.getDeclaredVariables().contains(aRefName) 
				&& rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getArrayDeclareStmt(aRefName, rZ3Type));
			fileGenerator.getDeclaredVariables().add(aRefName);
		}
		if(rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getAssertLocalEqualArrayRef(lLocalName, aRefName, aRef.getIndex()));
		}
	}
	
}
