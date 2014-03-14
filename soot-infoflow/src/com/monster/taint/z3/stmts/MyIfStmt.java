package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3MiscFunctions;
import com.monster.taint.z3.Z3Type;

import soot.Value;
import soot.jimple.ConditionExpr;
import soot.jimple.EqExpr;
import soot.jimple.GeExpr;
import soot.jimple.GtExpr;
import soot.jimple.LeExpr;
import soot.jimple.LtExpr;
import soot.jimple.NeExpr;

public class MyIfStmt {
	private SMT2FileGenerator fileGenerator = null;
	private PrintWriter writer = null;
	private boolean satisfied = false;
	private ConditionExpr conditionExpr = null;
	private int stmtIdx = 0;
	
	public MyIfStmt(SMT2FileGenerator fileGenerator, PrintWriter writer, boolean satisfied,
			ConditionExpr conditionExpr, int stmtIdx){
		this.fileGenerator = fileGenerator;
		this.writer = writer;
		this.satisfied = satisfied;
		this.conditionExpr = conditionExpr;
		this.stmtIdx = stmtIdx;
	}

	/**
	 * condition = eq_expr | ge_expr | le_expr | lt_expr | ne_expr | gt_expr;
	 * eq_expr = immediate "==" immediate; **the immediate maybe a null constant
	 * ge_expr = immediate ">=" immediate; 
	 * gt_expr = immediate ">" immediate; 
	 * le_expr = immediate "<=" immediate; 
	 * lt_expr = immediate "<" immediate;
	 * ne_expr = immediate "!=" immediate; **the immediate maybe a null constant
	 */
	public void jet(){
		Value op1 = conditionExpr.getOp1();
		Value op2 = conditionExpr.getOp2();
		if(conditionExpr instanceof EqExpr){
			if(satisfied){
				jetEq(op1, op2);
			}else{
				jetNe(op1, op2);
			}
		}else if(conditionExpr instanceof GeExpr){
			if(satisfied){
				jetGe(op1, op2);
			}else{
				jetLt(op1, op2);
			}
		}else if(conditionExpr instanceof GtExpr){
			if(satisfied){
				jetGt(op1, op2);
			}else{
				jetLe(op1, op2);
			}
		}else if(conditionExpr instanceof LeExpr){
			if(satisfied){
				jetLe(op1, op2);
			}else{
				jetGe(op1, op2);
			}
		}else if(conditionExpr instanceof LtExpr){
			if(satisfied){
				jetLt(op1, op2);
			}else{
				jetGe(op1, op2);
			}
		}else if(conditionExpr instanceof NeExpr){
			if(satisfied){
				jetNe(op1, op2);
			}else{
				jetEq(op1, op2);
			}
		}
		this.writer.println("(check-sat)");
	}

	/**
	 * if a == b
	 * (assert (= a b))
	 * if z == 0
	 * (assert (= z false))
	 * """ In the Java virtual machine, false is represented by integer zero and true by any non-zero integer"""
	 * @param op1
	 * @param op2
	 */
	private void jetEq(Value op1, Value op2){
		StringBuilder sb = new StringBuilder();
		String op1Name = this.fileGenerator.getRenameOf(op1, false, stmtIdx);
		String op2Name = this.fileGenerator.getRenameOf(op2, false, stmtIdx);
		sb.append("(assert (= ");
		sb.append(op1Name);
		sb.append(" ");
		if(Z3MiscFunctions.v().z3Type(op1.getType()) == Z3Type.Z3Boolean
				&& Z3MiscFunctions.v().z3Type(op2.getType()) != Z3Type.Z3Boolean){
			assert(op2Name.equals("0"));
			sb.append("false");
		}else{
			sb.append(op2Name);
		}
		sb.append("))");
		this.writer.println(sb.toString());
	}

	/**
	 * if a >= b 
	 * (assert (>= a b))
	 * @param op1
	 * @param op2
	 */
	private void jetGe(Value op1, Value op2){
		StringBuilder sb = new StringBuilder();
		String op1Name = this.fileGenerator.getRenameOf(op1, false, stmtIdx);
		String op2Name = this.fileGenerator.getRenameOf(op2, false, stmtIdx);
		sb.append("(assert (>= ");
		sb.append(op1Name);
		sb.append(" ");
		sb.append(op2Name);
		sb.append("))");
		this.writer.println(sb.toString());
	}
	
	private void jetGt(Value op1, Value op2){
		StringBuilder sb = new StringBuilder();
		String op1Name = this.fileGenerator.getRenameOf(op1, false, stmtIdx);
		String op2Name = this.fileGenerator.getRenameOf(op2, false, stmtIdx);
		sb.append("(assert (> ");
		sb.append(op1Name);
		sb.append(" ");
		sb.append(op2Name);
		sb.append("))");
		this.writer.println(sb.toString());
	}
	
	private void jetLe(Value op1, Value op2){
		StringBuilder sb = new StringBuilder();
		String op1Name = this.fileGenerator.getRenameOf(op1, false, stmtIdx);
		String op2Name = this.fileGenerator.getRenameOf(op2, false, stmtIdx);
		sb.append("(assert (<= ");
		sb.append(op1Name);
		sb.append(" ");
		sb.append(op2Name);
		sb.append("))");
		this.writer.println(sb.toString());
	}
	
	private void jetLt(Value op1, Value op2){
		StringBuilder sb = new StringBuilder();
		String op1Name = this.fileGenerator.getRenameOf(op1, false, stmtIdx);
		String op2Name = this.fileGenerator.getRenameOf(op2, false, stmtIdx);
		sb.append("(assert (< ");
		sb.append(op1Name);
		sb.append(" ");
		sb.append(op2Name);
		sb.append("))");
		this.writer.println(sb.toString());
	}

	/**
	 * if a != b
	 * (assert (not (= a b)))
	 * @param op1
	 * @param op2
	 */
	private void jetNe(Value op1, Value op2){
		StringBuilder sb = new StringBuilder();
		String op1Name = this.fileGenerator.getRenameOf(op1, false, stmtIdx);
		String op2Name = this.fileGenerator.getRenameOf(op2, false, stmtIdx);
		sb.append("(assert (not (= ");
		sb.append(op1Name);
		sb.append(" ");
		if(Z3MiscFunctions.v().z3Type(op1.getType()) == Z3Type.Z3Boolean
				&& Z3MiscFunctions.v().z3Type(op2.getType()) != Z3Type.Z3Boolean){
			assert(op2Name.equals("0"));
			sb.append("false");
		}else{
			sb.append(op2Name);
		}
		sb.append(")))");
		this.writer.println(sb.toString());
	}
}
