package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.ArrayRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRLocal;

public class AssignStmtLARefRLocal{
	private ASLARef lARef = null;
	private ASRLocal rLocal = null;
	
	public AssignStmtLARefRLocal(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, ArrayRef lARef, Local rLocal){
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rLocal = new ASRLocal(writer, fileGenerator, stmtIdx, rLocal);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rLocal.jet();
		
	}
}
