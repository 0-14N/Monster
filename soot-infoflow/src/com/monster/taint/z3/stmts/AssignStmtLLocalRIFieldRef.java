package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class AssignStmtLLocalRIFieldRef extends AssignStmtLLocal{
	private InstanceFieldRef iFieldRef = null;
	private Z3Type rZ3Type = null;
	private String iFieldRefName = null;
	
	public AssignStmtLLocalRIFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, InstanceFieldRef iFieldRef){
		super(writer, fileGenerator, stmtIdx, lLocal);
		this.iFieldRef = iFieldRef;
	}
	
	public void jet(){
		super.jet();
		rZ3Type = Z3MiscFunctions.v().z3Type(iFieldRef.getField().getType());
		iFieldRefName = fileGenerator.getRenameOf(iFieldRef, false, stmtIdx);
		if(!fileGenerator.getDeclaredVariables().contains(iFieldRefName)
				&& rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(iFieldRefName, rZ3Type));
			fileGenerator.getDeclaredVariables().add(iFieldRefName);
		}
		if(rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getCommonAssertEqual(lLocalName, iFieldRefName));
		}
	}
}
