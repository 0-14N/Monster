package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLSFieldRef;
import com.monster.taint.z3.stmts.atom.ASRLocal;


public class AssignStmtLSFieldRefRLocal{
	private ASLSFieldRef lSFieldRef = null;
	private ASRLocal rLocal = null;
	
	public AssignStmtLSFieldRefRLocal(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, StaticFieldRef lSFieldRef, Local rLocal){
		this.lSFieldRef = new ASLSFieldRef(writer, fileGenerator, stmtIdx, lSFieldRef);
		this.rLocal = new ASRLocal(writer, fileGenerator, stmtIdx, rLocal);
	}
	
	public void jet(){
		this.lSFieldRef.jet();
		this.rLocal.jet();
	}
}
