package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.InstanceFieldRef;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLSFieldRef;
import com.monster.taint.z3.stmts.atom.ASRIFieldRef;


public class AssignStmtLSFieldRefRIFieldRef{
	private ASLSFieldRef lSFieldRef = null;
	private ASRIFieldRef rIFieldRef = null;
	
	public AssignStmtLSFieldRefRIFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, StaticFieldRef lSFieldRef, InstanceFieldRef rIFieldRef){
		this.lSFieldRef = new ASLSFieldRef(writer, fileGenerator, stmtIdx, lSFieldRef);
		this.rIFieldRef = new ASRIFieldRef(writer, fileGenerator, stmtIdx, rIFieldRef);
	}
	
	public void jet(){
		this.lSFieldRef.jet();
		this.rIFieldRef.jet();
	}
}
