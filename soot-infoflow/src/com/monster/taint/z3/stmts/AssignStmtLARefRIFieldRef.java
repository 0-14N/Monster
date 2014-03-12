package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.jimple.ArrayRef;
import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRIFieldRef;

public class AssignStmtLARefRIFieldRef{
	private PrintWriter writer = null;
	private ASLARef lARef = null;
	private ASRIFieldRef rIFieldRef = null;
	
	public AssignStmtLARefRIFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, ArrayRef lARef, InstanceFieldRef rIFieldRef){
		this.writer = writer;
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rIFieldRef = new ASRIFieldRef(writer, fileGenerator, stmtIdx, rIFieldRef);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rIFieldRef.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * a[i] = c.f
	 * (assert (= (select a i) c_f))
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lARef.getLARefStr());
		sb.append(" ");
		sb.append(rIFieldRef.getIFieldRefName());
		sb.append("))");
		return sb.toString();
	}
}
