package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRARef;

import soot.Local;
import soot.jimple.ArrayRef;

public class AssignStmtLLocalRARef{
	private ASLLocal lLocal = null;
	private ASRARef rARef = null;
	
	
	public AssignStmtLLocalRARef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, Local lLocal, ArrayRef rARef){
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rARef = new ASRARef(writer, fileGenerator, stmtIdx, rARef);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rARef.jet();
		//if(rZ3Type != Z3Type.Z3Unknown){
			//writer.println(Z3MiscFunctions.v().getAssertLocalEqualArrayRef(lLocalName, aRefName, aRef.getIndex()));
		//}
	}
	
}
