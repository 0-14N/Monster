package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRSFieldRef;

public class AssignStmtLLocalRSFieldRef{
	private PrintWriter writer = null;
	private ASLLocal lLocal = null;
	private ASRSFieldRef rSFieldRef = null;
	
	public AssignStmtLLocalRSFieldRef(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, StaticFieldRef rSFieldRef){
		this.writer = writer;
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rSFieldRef = new ASRSFieldRef(writer, fileGenerator, stmtIdx, rSFieldRef);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rSFieldRef.jet();
		Z3Type lZ3Type = lLocal.getZ3Type();
		Z3Type rZ3Type = rSFieldRef.getRZ3Type();
		if(lZ3Type != Z3Type.Z3Unknown && rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getCommonAssertEqual(lLocal.getLLocalName(), rSFieldRef.getSFieldRefName()));
		}
	}
}
