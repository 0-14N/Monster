package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRSFieldRef;

public class AssignStmtLARefRSFieldRef{
	private ASLARef lARef = null;
	private ASRSFieldRef rSFieldRef = null;
	
	public AssignStmtLARefRSFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, ArrayRef lARef, StaticFieldRef rSFieldRef){
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rSFieldRef = new ASRSFieldRef(writer, fileGenerator, stmtIdx, rSFieldRef);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rSFieldRef.jet();
	}
}
