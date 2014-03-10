package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRSFieldRef;

public class AssignStmtLLocalRSFieldRef{
	private ASLLocal lLocal = null;
	private ASRSFieldRef rSFieldRef = null;
	
	public AssignStmtLLocalRSFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, StaticFieldRef rSFieldRef){
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rSFieldRef = new ASRSFieldRef(writer, fileGenerator, stmtIdx, rSFieldRef);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rSFieldRef.jet();
		/*
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
		*/
	}
}
