package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLIFieldRef;
import com.monster.taint.z3.stmts.atom.ASRLocal;

public class AssignStmtLIFieldRefRLocal{
	private ASLIFieldRef lIFieldRef = null;
	private ASRLocal rLocal = null;
	
	public AssignStmtLIFieldRefRLocal(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, InstanceFieldRef lIFieldRef, Local rLocal){
		this.lIFieldRef = new ASLIFieldRef(writer, fileGenerator, stmtIdx, lIFieldRef);
		this.rLocal = new ASRLocal(writer, fileGenerator, stmtIdx, rLocal);
	}
	
	public void jet(){
		this.lIFieldRef.jet();
		this.rLocal.jet();
	}
}
