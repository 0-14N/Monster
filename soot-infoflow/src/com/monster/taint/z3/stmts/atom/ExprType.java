package com.monster.taint.z3.stmts.atom;
/**
 * expr = binop_expr* | cast_expr* | instance_of_expr | invoke_expr* 
 * | new_array_expr* | new_expr* | new_multi_array_expr | unop_expr*;
 * 
 * @author chenxiong
 *
 */
public enum ExprType {
	BINOP,
	CAST,
	INSTANCEOF,
	INVOKE,
	NEWARRAY,
	NEWEXPR,
	NEWMULIARRAY,
	UNOP
}
