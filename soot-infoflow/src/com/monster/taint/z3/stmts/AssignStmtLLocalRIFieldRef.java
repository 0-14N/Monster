package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRIFieldRef;

public class AssignStmtLLocalRIFieldRef{
	private ASLLocal lLocal = null;
	private ASRIFieldRef rIFieldRef = null;
	
	public AssignStmtLLocalRIFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, InstanceFieldRef rIFieldRef){
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rIFieldRef = new ASRIFieldRef(writer, fileGenerator, stmtIdx, rIFieldRef);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rIFieldRef.jet();
		/*
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
		*/
	}
}
