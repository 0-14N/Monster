package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

import soot.Local;

public class AssignStmtLLocalRLocal extends AssignStmtLLocal{
	private Local rLocal = null;
	private String rLocalName = null;
	private Z3Type rZ3Type = null;
	
	public AssignStmtLLocalRLocal(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, Local rLocal){
		super(writer, fileGenerator, stmtIdx, lLocal);
		this.rLocal = rLocal;
	}
	
	public void jet(){
		super.jet();
		rLocalName = fileGenerator.getRenameOf(rLocal, false, stmtIdx);
		rZ3Type = Z3MiscFunctions.v().z3Type(rLocal.getType());
		if(!fileGenerator.getDeclaredVariables().contains(rLocalName) 
				&& rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(rLocalName, rZ3Type));
			fileGenerator.getDeclaredVariables().add(rLocalName);
		}
		if(rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getCommonAssertEqual(lLocalName, rLocalName));
		}
	}
}
