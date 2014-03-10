package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.InstanceFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;
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
		
		Z3Type lZ3Type = lLocal.getZ3Type();
		Z3Type rZ3Type = rIFieldRef.getRZ3Type();
		
		if(lZ3Type != Z3Type.Z3Unknown && rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getCommonAssertEqual(lLocal.getLLocalName(), rIFieldRef.getIFieldRefName()));
		}
	}
}
