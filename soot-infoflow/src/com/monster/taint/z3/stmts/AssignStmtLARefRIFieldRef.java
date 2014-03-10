package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;
import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRIFieldRef;

public class AssignStmtLARefRIFieldRef{
	private ASLARef lARef = null;
	private ASRIFieldRef rIFieldRef = null;
	
	public AssignStmtLARefRIFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, ArrayRef lARef, InstanceFieldRef rIFieldRef){
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rIFieldRef = new ASRIFieldRef(writer, fileGenerator, stmtIdx, rIFieldRef);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rIFieldRef.jet();
	}
}
