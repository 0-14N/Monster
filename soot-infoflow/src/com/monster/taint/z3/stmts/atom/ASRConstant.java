package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;

import soot.jimple.Constant;
import soot.jimple.NullConstant;

import com.monster.taint.z3.SMT2FileGenerator;

public class ASRConstant {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private Constant rConstant = null;
	private String constStr = null;
	
	public ASRConstant(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Constant rConstant){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.rConstant = rConstant;
	}

	/**
	 * initialize constStr
	 */
	public void jet(){
		//constant = double_constant | float_constant | int_constant | long_constant |
		//string_constant | null_constant;
		if(rConstant instanceof NullConstant){
			constStr = "\"\"";
		}else{
			constStr = rConstant.toString();
		}
	}
	
	public Constant getConstant(){
		return this.rConstant;
	}
	
	public String getConstStr(){
		return this.constStr;
	}
}
