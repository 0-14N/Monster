package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRARef;

import soot.Local;
import soot.jimple.ArrayRef;

public class AssignStmtLLocalRARef{
	private PrintWriter writer = null;
	private ASLLocal lLocal = null;
	private ASRARef rARef = null;
	
	
	public AssignStmtLLocalRARef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, Local lLocal, ArrayRef rARef){
		this.writer = writer;
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rARef = new ASRARef(writer, fileGenerator, stmtIdx, rARef);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rARef.jet();
		
		writer.println(getAssertStr());
	}

	/**
	 * r = a[i]
	 * (assert (= r (select a i))) 
	 * @return
	 */
	private String getAssertStr(){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lLocal.getLLocalName());
		sb.append(" ");
		sb.append(rARef.getRARefStr());
		sb.append("))");
		return sb.toString();
	}
	
}
