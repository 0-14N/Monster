package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLIFieldRef;
import com.monster.taint.z3.stmts.atom.ASRIFieldRef;

public class AssignStmtLIFieldRefRIFieldRef{
	private ASLIFieldRef lIFieldRef = null;
	private ASRIFieldRef rIFieldRef = null;
	
	public AssignStmtLIFieldRefRIFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, InstanceFieldRef lIFieldRef, InstanceFieldRef rIFieldRef){
		this.lIFieldRef = new ASLIFieldRef(writer, fileGenerator, stmtIdx, lIFieldRef);
		this.rIFieldRef = new ASRIFieldRef(writer, fileGenerator, stmtIdx, rIFieldRef);
	}
	
	public void jet(){
		this.lIFieldRef.jet();
		this.rIFieldRef.jet();
	}
}
