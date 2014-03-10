package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLSFieldRef;
import com.monster.taint.z3.stmts.atom.ASRARef;


public class AssignStmtLSFieldRefRARef{
	private ASLSFieldRef lSFieldRef = null;
	private ASRARef rARef = null;
	
	public AssignStmtLSFieldRefRARef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, StaticFieldRef lSFieldRef, ArrayRef rARef){
		this.lSFieldRef = new ASLSFieldRef(writer, fileGenerator, stmtIdx, lSFieldRef);
		this.rARef = new ASRARef(writer, fileGenerator, stmtIdx, rARef);
	}
	
	public void jet(){
		this.lSFieldRef.jet();
		this.rARef.jet();
	}
}
