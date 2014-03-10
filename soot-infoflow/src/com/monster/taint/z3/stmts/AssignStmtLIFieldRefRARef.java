package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;
import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLIFieldRef;
import com.monster.taint.z3.stmts.atom.ASRARef;

public class AssignStmtLIFieldRefRARef{
	private ASLIFieldRef lIFieldRef = null;
	private ASRARef rARef = null;
	
	public AssignStmtLIFieldRefRARef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, InstanceFieldRef lIFieldRef, ArrayRef rARef){
		this.lIFieldRef = new ASLIFieldRef(writer, fileGenerator, stmtIdx, lIFieldRef);
		this.rARef = new ASRARef(writer, fileGenerator, stmtIdx, rARef);
	}
	
	public void jet(){
		this.lIFieldRef.jet();
		this.rARef.jet();
	}
}
