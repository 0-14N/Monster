package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRLocal;

import soot.Local;

public class AssignStmtLLocalRLocal{
	private ASLLocal lLocal = null;
	private ASRLocal rLocal = null;
	
	public AssignStmtLLocalRLocal(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, Local rLocal){
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rLocal = new ASRLocal(writer, fileGenerator, stmtIdx, rLocal);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rLocal.jet();
		/*
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
		*/
	}
}
