package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.Constant;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRConstant;

public class AssignStmtLLocalRConstant{
	private ASLLocal lLocal = null;
	private ASRConstant rConstant = null;
	
	public AssignStmtLLocalRConstant (PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, Constant rConstant){
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rConstant = new ASRConstant(writer, fileGenerator, stmtIdx, rConstant);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rConstant.jet();
		/*
		rZ3Type = Z3MiscFunctions.v().z3Type(constant.getType());
		if(rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getAssertLocalEqualConst(lLocalName, rZ3Type, constant));
		}
		*/
	}
}
