package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3MiscFunctions;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRExpr;

import soot.Local;
import soot.jimple.CastExpr;
import soot.jimple.Expr;
import soot.jimple.LengthExpr;
import soot.jimple.NewArrayExpr;

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
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private ASLLocal lLocal = null;
	private ASRExpr rExpr = null;
	
	public AssignStmtLLocalRExpr(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Local lLocal, Expr rExpr){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rExpr = new ASRExpr(writer, fileGenerator, stmtIdx, rExpr);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rExpr.jet();
		
		if(rExpr.isNewExpr()){
			return;
		}
		
		writer.println(getAssertStr());
	}
	
	
	/**
	 * expr = binop_expr | cast_expr | instance_of_expr | invoke_expr 
	 * | new_array_expr | new_expr | new_multi_array_expr | unop_expr;
	 * @return
	 */
	private String getAssertStr(){
		Expr expr = rExpr.getRExpr();
		
		if(expr instanceof CastExpr){
			return specialCastExprStr((CastExpr) expr);
		}
		
		if(expr instanceof NewArrayExpr){
			return specialNewArrayExprStr((NewArrayExpr) expr);
		}
		
		if(expr instanceof LengthExpr){
			return specialLengthExprStr((LengthExpr) expr);
		}
		
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(lLocal.getLLocalName());
		sb.append(" ");
		sb.append(rExpr.getExprStr());
		sb.append("))");
		return sb.toString();
	}

	/**
	 * $r10 = (java.lang.Object[]) $r11
	 * $r11 is not array type
	 * (assert (= (select $r10 0) $r11))
	 * @param castExpr
	 * @return
	 */
	private String specialCastExprStr(CastExpr castExpr){
		StringBuilder sb = new StringBuilder();
		
		if(Z3MiscFunctions.v().isArrayType(castExpr.getCastType()) &&
				!Z3MiscFunctions.v().isArrayType(castExpr.getOp().getType())){
			sb.append("(assert (= ");
			sb.append("(select ");
			sb.append(lLocal.getLLocalName());
			sb.append(" 0)");
			sb.append(" ");
			sb.append(rExpr.getExprStr());
			sb.append("))");
		}else{
			sb.append("(assert (= ");
			sb.append(lLocal.getLLocalName());
			sb.append(" ");
			sb.append(rExpr.getExprStr());
			sb.append("))");
		}
		
		return sb.toString();
	}

	/**
	 * ;$r13 = newarray (android.telephony.SmsMessage)[$i1]
	 * 
	 * @param newArrayExpr
	 * @return
	 */
	private String specialNewArrayExprStr(NewArrayExpr newArrayExpr){
		StringBuilder sb = new StringBuilder();
		sb.append(";length of array ");
		sb.append(lLocal.getLLocalName());
		sb.append(" is ");
		sb.append(rExpr.getExprStr());
		
		fileGenerator.getArraySizeMap().put(lLocal.getLLocalName(), rExpr.getExprStr());
		return sb.toString();
	}

	/**
	 * $i1 = lengthof $r10 
	 * (assert (= $i1 map.get(..)))
	 * @param lengthExpr
	 * @return
	 */
	private String specialLengthExprStr(LengthExpr lengthExpr){
		StringBuilder sb = new StringBuilder();
		String length = fileGenerator.getArraySizeMap().get(rExpr.getExprStr());
		if(length == null){
			length = "1";
		}
		sb.append("(assert (= ");
		sb.append(lLocal.getLLocalName());
		sb.append(" ");
		sb.append(length);
		sb.append("))");
		return sb.toString();
	}
}
