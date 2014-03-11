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
	}

}
