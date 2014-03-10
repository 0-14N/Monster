package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Local;
import soot.jimple.Constant;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class AssignStmtLLocalRConstant extends AssignStmtLLocal{
	private Constant constant = null;
	private Z3Type rZ3Type = null;
	
	public AssignStmtLLocalRConstant (PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, Constant constant){
		super(writer, fileGenerator, stmtIdx, lLocal);
		this.constant = constant;
	}
	
	public void jet(){
		super.jet();
		rZ3Type = Z3MiscFunctions.v().z3Type(constant.getType());
		if(rZ3Type != Z3Type.Z3Unknown){
			writer.println(Z3MiscFunctions.v().getAssertLocalEqualConst(lLocalName, rZ3Type, constant));
		}
	}
}
