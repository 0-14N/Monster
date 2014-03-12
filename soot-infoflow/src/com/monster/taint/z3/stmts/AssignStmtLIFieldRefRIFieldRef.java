package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLIFieldRef;
import com.monster.taint.z3.stmts.atom.ASRIFieldRef;

public class AssignStmtLIFieldRefRIFieldRef{
	private PrintWriter writer = null;
	private ASLIFieldRef lIFieldRef = null;
	private ASRIFieldRef rIFieldRef = null;
	
	public AssignStmtLIFieldRefRIFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, InstanceFieldRef lIFieldRef, InstanceFieldRef rIFieldRef){
		this.writer = writer;
		this.lIFieldRef = new ASLIFieldRef(writer, fileGenerator, stmtIdx, lIFieldRef);
		this.rIFieldRef = new ASRIFieldRef(writer, fileGenerator, stmtIdx, rIFieldRef);
	}
	
	public void jet(){
		this.lIFieldRef.jet();
		this.rIFieldRef.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * a.f = b.f
	 * (assert (= a_f b_f))
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lIFieldRef.getIFieldRefName());
		sb.append(" ");
		sb.append(rIFieldRef.getIFieldRefName());
		sb.append("))");
		return sb.toString();
	}
	
}
