package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class AssignStmtLLocalRSFieldRef extends AssignStmtLLocal{
	private StaticFieldRef sFieldRef = null;
	private String sFieldRefName = null;
	private Z3Type rZ3Type = null;
	
	public AssignStmtLLocalRSFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, StaticFieldRef sFieldRef){
		super(writer, fileGenerator, stmtIdx, lLocal);
		this.sFieldRef = sFieldRef;
	}
	
	public void jet(){
		super.jet();
		sFieldRefName = fileGenerator.getRenameOf(sFieldRef, false, stmtIdx);
		rZ3Type = Z3MiscFunctions.v().z3Type(sFieldRef.getField().getType());
		if(!fileGenerator.getDeclaredVariables().contains(sFieldRefName)
				&& rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(sFieldRefName, rZ3Type));
					fileGenerator.getDeclaredVariables().add(sFieldRefName);
		}
		if(rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getCommonAssertEqual(lLocalName, sFieldRefName));
		}
	}
}
