package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRExpr;

import soot.Local;
import soot.jimple.Expr;

/**
 * expr = binop_expr* | cast_expr* | instance_of_expr | invoke_expr* 
 * | new_array_expr* | new_expr* | new_multi_array_expr | unop_expr*;
 * 
 * 
 * unop_expr = length_expr* | neg_expr*;
 * @author chenxiong
 *
 */
public class AssignStmtLLocalRExpr{
	private ASLLocal lLocal = null;
	private ASRExpr rExpr = null;
	
	public AssignStmtLLocalRExpr(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, Expr rExpr){
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rExpr = new ASRExpr(writer, fileGenerator, stmtIdx, rExpr);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rExpr.jet();
		/*
		exprType = Z3MiscFunctions.v().getExprType(expr);
		switch(exprType){
			case BINOP:
				break;
			case CAST:
				break;
			case INVOKE:
				break;
			case NEWARRAY:
				break;
			case NEWEXPR:
				break;
			case UNOP:
				break;
		}
		*/
	}

	/**
	 * binop_expr = add_expr* | and_expr* | cmp_expr | cmpg_expr | cmpl_expr | div_expr * 
	 * | eq_expr* | ge_expr* | gt_expr* | le_expr* | lt_expr* | mul_expr* | ne_expr* 
	 * | or_expr* | rem_expr* | shl_expr | shr_expr | sub_expr* | ushr_expr | xor_expr;
	 * 
	 * the starred are concerned
	 */
	//private void parseBinop(){
		/*
		BinopExpr binopExpr = (BinopExpr) expr;
		Value op1 = binopExpr.getOp1();
		Value op2 = binopExpr.getOp2();
		BinopExprType binopType = Z3MiscFunctions.v().getBinopExprType(binopExpr);
		*/
		
	//}
}
