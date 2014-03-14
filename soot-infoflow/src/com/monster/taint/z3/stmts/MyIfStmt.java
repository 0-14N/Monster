package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3MiscFunctions;
import com.monster.taint.z3.Z3Type;

import soot.Local;
import soot.Value;
import soot.jimple.ConditionExpr;
import soot.jimple.Constant;
import soot.jimple.EqExpr;
import soot.jimple.GeExpr;
import soot.jimple.GtExpr;
import soot.jimple.LeExpr;
import soot.jimple.LtExpr;
import soot.jimple.NeExpr;
import soot.jimple.NullConstant;
import soot.jimple.NumericConstant;

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
		Z3Type op1Z3Type = Z3MiscFunctions.v().z3Type(op1.getType());
		Z3Type op2Z3Type = Z3MiscFunctions.v().z3Type(op2.getType());
		String op1Name = fileGenerator.getRenameOf(op1, false, stmtIdx);
		String op2Name = fileGenerator.getRenameOf(op2, false, stmtIdx);
	
		if(op1 instanceof Local && !fileGenerator.getDeclaredVariables().contains(op1Name)){
			writer.println(Z3MiscFunctions.v().getVariableDeclareStmt(op1Name, op1Z3Type));
			fileGenerator.getDeclaredVariables().add(op1Name);
		}
		
		if(op2 instanceof Local && !fileGenerator.getDeclaredVariables().contains(op2Name)){
			writer.println(Z3MiscFunctions.v().getVariableDeclareStmt(op2Name, op2Z3Type));
			fileGenerator.getDeclaredVariables().add(op2Name);
		}
		
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
	 * 
	 * if z == 0
	 * (assert (= z false))
	 * 
	 * ***special cases for array type variables and null****
	 * String[]/UnknownArray:
	 * (declare-const a (Array Int String) )
	 * if a == null
	 * 
	 * Int[]:
	 * (declare-const a (Array Int Int))
	 * if a == null
	 * 
	 * Real[]: 
	 * 
	 * Bool[]:
	 * ======(assert (= true true))
	 * """ In the Java virtual machine, false is represented by integer zero and true by any non-zero integer"""
	 * @param op1
	 * @param op2
	 */
	private void jetEq(Value op1, Value op2){
		StringBuilder sb = new StringBuilder();
		String op1Name = this.fileGenerator.getRenameOf(op1, false, stmtIdx);
		String op2Name = this.fileGenerator.getRenameOf(op2, false, stmtIdx);
		Z3Type op1Z3Type = Z3MiscFunctions.v().z3Type(op1.getType());
		Z3Type op2Z3Type = Z3MiscFunctions.v().z3Type(op2.getType());
		
		//handle the special cases
		if(Z3MiscFunctions.v().isArrayType(op1.getType()) && op2 instanceof Constant){
			assert(op2 instanceof NullConstant);
			sb.append("(assert (= true true))");
		}else{
			sb.append("(assert (= ");
			sb.append(op1Name);
			sb.append(" ");
			if(op1Z3Type == Z3Type.Z3Boolean && op2Z3Type != Z3Type.Z3Boolean){
				assert(op2Name.equals("0"));
				sb.append("false");
			}else{
				//$i0 == -1
				//(assert (= $i0 (- 0 1)))
				if(op2 instanceof NumericConstant && op2Name.startsWith("-")){
					sb.append("(- 0 ");
					sb.append(op2Name.substring(1));
					sb.append(")");
				}else{
					sb.append(op2Name);
				}
			}
			sb.append("))");
		}
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
		//$i0 >= -1
		//(assert (>= $i0 (- 0 1)))
		if(op2 instanceof NumericConstant && op2Name.startsWith("-")){
			sb.append("(- 0 ");
			sb.append(op2Name.substring(1));
			sb.append(")");
		}else{
			sb.append(op2Name);
		}
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
		//$i0 > -1
		//(assert (> $i0 (- 0 1)))
		if(op2 instanceof NumericConstant && op2Name.startsWith("-")){
			sb.append("(- 0 ");
			sb.append(op2Name.substring(1));
			sb.append(")");
		}else{
			sb.append(op2Name);
		}
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
		//$i0 <= -1
		//(assert (<= $i0 (- 0 1)))
		if(op2 instanceof NumericConstant && op2Name.startsWith("-")){
			sb.append("(- 0 ");
			sb.append(op2Name.substring(1));
			sb.append(")");
		}else{
			sb.append(op2Name);
		}
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
		//$i0 < -1
		//(assert (< $i0 (- 0 1)))
		if(op2 instanceof NumericConstant && op2Name.startsWith("-")){
			sb.append("(- 0 ");
			sb.append(op2Name.substring(1));
			sb.append(")");
		}else{
			sb.append(op2Name);
		}
		sb.append("))");
		this.writer.println(sb.toString());
	}

	/**
	 * if a != b
	 * (assert (not (= a b)))
	 * 
	 * ***special cases for array type variables and null****
	 * String[]/UnknownArray:
	 * (declare-const a (Array Int String) )
	 * if a != null
	 * (assert (not (= (select a 0) "shoon")))
	 * 
	 * Int[]:
	 * (declare-const a (Array Int Int))
	 * if a != null
	 * (assert (not (= (select a 0) 42)))
	 * 
	 * Real[]: 42.0 
	 * 
	 * Bool[]:
	 * (assert (or (select b 0) (select b 0)))
	 * @param op1
	 * @param op2
	 */
	private void jetNe(Value op1, Value op2){
		StringBuilder sb = new StringBuilder();
		String op1Name = this.fileGenerator.getRenameOf(op1, false, stmtIdx);
		String op2Name = this.fileGenerator.getRenameOf(op2, false, stmtIdx);
		Z3Type op1Z3Type = Z3MiscFunctions.v().z3Type(op1.getType());
		Z3Type op2Z3Type = Z3MiscFunctions.v().z3Type(op2.getType());
		
		//handle the special cases
		if(Z3MiscFunctions.v().isArrayType(op1.getType()) && op2 instanceof Constant){
			assert(op2 instanceof NullConstant);
			if(op1Z3Type == Z3Type.Z3BooleanArray){
				sb.append("(assert (or (select ");
				sb.append(op1Name);
				sb.append(" 0) (select ");
				sb.append(op1Name);
				sb.append(" 0)))");
			}else{
				sb.append("(assert (not (= (select ");
				sb.append(op1Name);
				sb.append(" 0) ");
				if(op1Z3Type == Z3Type.Z3StringArray || op1Z3Type == Z3Type.Z3UnKnownArray){
					sb.append("\"shoon\"");
				}else if(op1Z3Type == Z3Type.Z3IntArray){
					sb.append("42");
				}else if(op1Z3Type == Z3Type.Z3RealArray){
					sb.append("42.0");
				}
				sb.append(")))");
			}
		}else{
			sb.append("(assert (not (= ");
			sb.append(op1Name);
			sb.append(" ");
			if(op1Z3Type == Z3Type.Z3Boolean && op2Z3Type != Z3Type.Z3Boolean){
				assert(op2Name.equals("0"));
				sb.append("false");
			}else{
				//$i0 != -1
				//(assert (not (= $i0 (- 0 1))))
				if(op2 instanceof NumericConstant && op2Name.startsWith("-")){
					sb.append("(- 0 ");
					sb.append(op2Name.substring(1));
					sb.append(")");
				}else{
					sb.append(op2Name);
				}
			}
			sb.append(")))");
		}
		this.writer.println(sb.toString());
	}
}
