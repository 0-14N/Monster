package com.monster.taint.z3.stmts.atom;

/**
 * 
 * binop_expr = add_expr* | and_expr* | cmp_expr | cmpg_expr | cmpl_expr | div_expr * 
 * | eq_expr* | ge_expr* | gt_expr* | le_expr* | lt_expr* | mul_expr* | ne_expr* 
 * | or_expr* | rem_expr* | shl_expr | shr_expr | sub_expr* | ushr_expr | xor_expr;
 * 
 * @author chenxiong
 *
 */
public enum BinopExprType {
	ADD, AND, CMP, CMPG, CMPL, DIV, 
	EQ, GE, GT, LE, LT, MUL, NE,
	OR, REM, SHL, SHR, SUB, USHR, XOR
}
