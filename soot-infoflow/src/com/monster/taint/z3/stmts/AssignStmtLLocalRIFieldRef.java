package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRIFieldRef;

public class AssignStmtLLocalRIFieldRef{
	private PrintWriter writer = null;
	private ASLLocal lLocal = null;
	private ASRIFieldRef rIFieldRef = null;
	
	public AssignStmtLLocalRIFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, InstanceFieldRef rIFieldRef){
		this.writer = writer;
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rIFieldRef = new ASRIFieldRef(writer, fileGenerator, stmtIdx, rIFieldRef);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rIFieldRef.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * r = a.f
	 * (assert (= r a_f))
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lLocal.getLLocalName());
		sb.append(" ");
		sb.append(rIFieldRef.getIFieldRefName());
		sb.append("))");
		return sb.toString();
	}
}
