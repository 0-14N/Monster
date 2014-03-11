package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;
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
		
		Z3Type lZ3Type = lLocal.getZ3Type();
		Z3Type rZ3Type = rARef.getRZ3Type();
		
		if(lZ3Type != Z3Type.Z3Unknown && rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getAssertLocalEqualArrayRef(lLocal.getLLocalName(), 
					rARef.getARefName(), rARef.getRARef().getIndex()));
		}
	}
	
}
