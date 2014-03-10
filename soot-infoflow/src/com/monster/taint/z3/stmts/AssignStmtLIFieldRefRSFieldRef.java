package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.InstanceFieldRef;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLIFieldRef;
import com.monster.taint.z3.stmts.atom.ASRSFieldRef;

public class AssignStmtLIFieldRefRSFieldRef{
	private ASLIFieldRef lIFieldRef = null;
	private ASRSFieldRef rSFieldRef = null;
	
	public AssignStmtLIFieldRefRSFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, InstanceFieldRef lIFieldRef, StaticFieldRef rSFieldRef){
		this.lIFieldRef = new ASLIFieldRef(writer, fileGenerator, stmtIdx, lIFieldRef);
		this.rSFieldRef = new ASRSFieldRef(writer, fileGenerator, stmtIdx, rSFieldRef);
	}
	
	public void jet(){
		this.lIFieldRef.jet();
		this.rSFieldRef.jet();
	}
}
