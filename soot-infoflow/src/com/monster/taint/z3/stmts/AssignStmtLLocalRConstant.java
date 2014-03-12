package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.Constant;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRConstant;

public class AssignStmtLLocalRConstant{
	private PrintWriter writer = null;
	private ASLLocal lLocal = null;
	private ASRConstant rConstant = null;
	
	public AssignStmtLLocalRConstant (PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, Constant rConstant){
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rConstant = new ASRConstant(writer, fileGenerator, stmtIdx, rConstant);
		this.writer = writer;
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rConstant.jet();
		Z3Type rZ3Type = Z3MiscFunctions.v().z3Type(rConstant.getConstant().getType());
		writer.println(Z3MiscFunctions.v().getAssertLocalEqualConst(lLocal.getLLocalName(), 
					rZ3Type, rConstant.getConstant()));
	}
}
