package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRARef;

public class AssignStmtLARefRARef{
	private ASLARef lARef = null;
	private ASRARef rARef = null;
	
	public AssignStmtLARefRARef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, ArrayRef lARef, ArrayRef rARef){
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rARef = new ASRARef(writer, fileGenerator, stmtIdx, rARef);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rARef.jet();
		
		
	}
}
