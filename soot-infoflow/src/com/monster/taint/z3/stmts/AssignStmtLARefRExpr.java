package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import soot.Type;
import soot.jimple.ArrayRef;
import soot.jimple.Expr;
import soot.jimple.LengthExpr;
import soot.jimple.UnopExpr;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3MiscFunctions;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.stmts.atom.ASLARef;
import com.monster.taint.z3.stmts.atom.ASRExpr;

public class AssignStmtLARefRExpr{
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private ASLARef lARef = null;
	private ASRExpr rExpr = null;
	
	public AssignStmtLARefRExpr(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, ArrayRef lARef, Expr rExpr){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.lARef = new ASLARef(writer, fileGenerator, stmtIdx, lARef);
		this.rExpr = new ASRExpr(writer, fileGenerator, stmtIdx, rExpr);
	}
	
	public void jet(){
		this.lARef.jet();
		this.rExpr.jet();
	
		if(rExpr.isNewExpr()){
			return;
		}
		
		writer.println(getAssertStr());
	}

	/** expr = binop_expr | cast_expr | instance_of_expr | invoke_expr 
	 * | new_array_expr | new_expr | new_multi_array_expr | unop_expr;
	 * 
	 * 1. a[i] = c + d  
	 * @return
	 */
	private String getAssertStr(){
		//special cases: cast_expr, new_array_expr, unop_expr
		Expr expr = rExpr.getRExpr();
		if(expr instanceof UnopExpr){
			UnopExpr unopExpr = (UnopExpr) expr;
			if(unopExpr instanceof LengthExpr){
				return specialLengthExprStr((LengthExpr) unopExpr);
			}
		}
		
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lARef.getLARefStr());
		sb.append(" ");
		sb.append(rExpr.getExprStr());
		sb.append("))");
		return sb.toString();
	}

	/**
	 *	a[i] = lengthof "084"
	 *  (assert (= (select a i) (Length x)))
	 *  a[i] = lengthof array 
	 *  
	 * @param lengthExpr
	 * @return
	 */
	private String specialLengthExprStr(LengthExpr lengthExpr){
		StringBuilder sb = new StringBuilder();
		Type type = lengthExpr.getOp().getType();
		if(Z3MiscFunctions.v().isArrayType(type)){
			sb.append("(assert (= ");
			sb.append(lARef.getLARefStr());
			sb.append(" ");
			sb.append(fileGenerator.getArraySizeMap().get(rExpr.getExprStr()));
			sb.append("))");
		}else{
			assert(Z3MiscFunctions.v().z3Type(type) == Z3Type.Z3String);
			sb.append("(assert (= ");
			sb.append(lARef.getLARefStr());
			sb.append(" ");
			sb.append("(Length ");
			sb.append(rExpr.getExprStr());
			sb.append(")");
			sb.append("))");
		}
		return sb.toString();
	}
}
