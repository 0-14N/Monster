package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;
import java.util.List;

import soot.Local;
import soot.SootMethodRef;
import soot.Type;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
import soot.jimple.BinopExpr;
import soot.jimple.Expr;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.StaticFieldRef;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class ASRExpr {
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx;
	private Expr rExpr = null;
	private String exprStr = null;
	private ExprType exprType = null;
	
	public ASRExpr(PrintWriter writer, SMT2FileGenerator fileGenerator, 
			int stmtIdx, Expr rExpr){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.rExpr = rExpr;
	}
	
	public void jet(){
		//new introduced variables
		List<ValueBox> useBoxes = rExpr.getUseBoxes();
		for(ValueBox useBox : useBoxes){
			Value value = useBox.getValue();
			Z3Type z3Type = null;
			String varStr = fileGenerator.getRenameOf(value, false, stmtIdx);
			if(value instanceof Local){
				z3Type = Z3MiscFunctions.v().z3Type(value.getType());
				if(z3Type != Z3Type.Z3Unknown && 
						!fileGenerator.getDeclaredVariables().contains(varStr)){
					writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(varStr, z3Type));
					fileGenerator.getDeclaredVariables().add(varStr);
				}else if(z3Type == Z3Type.Z3Unknown && 
						!fileGenerator.getDeclaredVariables().contains(varStr)){
					writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(varStr, Z3Type.Z3String));
					fileGenerator.getDeclaredVariables().add(varStr);
				}
			}else if(value instanceof InstanceFieldRef){
				InstanceFieldRef iFRef = (InstanceFieldRef) value;
				z3Type = Z3MiscFunctions.v().z3Type(iFRef.getField().getType());
				if(z3Type != Z3Type.Z3Unknown &&
						!fileGenerator.getDeclaredVariables().contains(varStr)){
					writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(varStr, z3Type));
					fileGenerator.getDeclaredVariables().add(varStr);
				}else if(z3Type == Z3Type.Z3Unknown && 
						!fileGenerator.getDeclaredVariables().contains(varStr)){
					writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(varStr, Z3Type.Z3String));
					fileGenerator.getDeclaredVariables().add(varStr);
				}
			}else if(value instanceof StaticFieldRef){
				StaticFieldRef sFRef = (StaticFieldRef) value;
				z3Type = Z3MiscFunctions.v().z3Type(sFRef.getField().getType());
				if(z3Type != Z3Type.Z3Unknown &&
						!fileGenerator.getDeclaredVariables().contains(varStr)){
					writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(varStr, z3Type));
					fileGenerator.getDeclaredVariables().add(varStr);
				}else if(z3Type == Z3Type.Z3Unknown && 
						!fileGenerator.getDeclaredVariables().contains(varStr)){
					writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(varStr, Z3Type.Z3String));
					fileGenerator.getDeclaredVariables().add(varStr);
				}
			}else if(value instanceof ArrayRef){
				ArrayRef aRef = (ArrayRef) value;
				z3Type = Z3MiscFunctions.v().z3Type(aRef.getBase().getType());
				if(z3Type != Z3Type.Z3Unknown &&
						!fileGenerator.getDeclaredVariables().contains(varStr)){
					writer.println(Z3MiscFunctions.v().getArrayDeclareStmt(varStr, z3Type));
					fileGenerator.getDeclaredVariables().add(varStr);
				}else if(z3Type == Z3Type.Z3Unknown && 
						!fileGenerator.getDeclaredVariables().contains(varStr)){
					writer.println(Z3MiscFunctions.v().getPrimeTypeDeclareStmt(varStr, Z3Type.Z3String));
					fileGenerator.getDeclaredVariables().add(varStr);
				}
			}
		}
		
		//new introduced functions
		if(rExpr instanceof InvokeExpr){
			jetFunctions();
		}
		
		//jet expr string
		jetExprStr();
	}

	/**
	 * <android.content.Intent: java.lang.String getAction()>
	 * (declare-fun android_content_Intent$$java_lang_String$$void$$getAction () String)
	 */
	private void jetFunctions(){
		InvokeExpr invokeExpr = (InvokeExpr) rExpr;
		StringBuilder funSB = new StringBuilder();	
		SootMethodRef methodRef = invokeExpr.getMethodRef();
		
		funSB.append(methodRef.declaringClass().getName().replace(".", "_"));
		funSB.append("$$");
		funSB.append(methodRef.returnType().toString().replace(".", "_"));
		funSB.append("$$");
		for(Type paramType : methodRef.parameterTypes()){
			funSB.append(paramType.toString().replace(".", "_"));
			funSB.append("$");
		}
		funSB.append(methodRef.name());
		
		String funStr = funSB.toString();
		if(!fileGenerator.getDeclaredFunctions().contains(funStr)){
			writer.println(Z3MiscFunctions.v().getFuncDeclareStmt(funStr, 
					methodRef.parameterTypes(), methodRef.returnType()));
			fileGenerator.getDeclaredFunctions().add(funStr);
		}
	}
	
	public Expr getRExpr(){
		return this.rExpr;
	}
	
	private void jetExprStr(){
		//expr = binop_expr* | cast_expr* | instance_of_expr | invoke_expr* 
		//| new_array_expr* | new_expr* | new_multi_array_expr | unop_expr*;
		exprType = Z3MiscFunctions.v().getExprType(rExpr);
		switch(exprType){
			case BINOP:
				jetBinopExprStr();
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
	}
	
	public String getExprStr(){
		return this.exprStr;
	}
	

	
	/**
	 * binop_expr = add_expr* | and_expr* | cmp_expr | cmpg_expr | cmpl_expr | div_expr * 
	 * | eq_expr* | ge_expr* | gt_expr* | le_expr* | lt_expr* | mul_expr* | ne_expr* 
	 * | or_expr* | rem_expr* | shl_expr | shr_expr | sub_expr* | ushr_expr | xor_expr;
	 * 
	 * the starred are concerned
	 */
	private void jetBinopExprStr(){
		BinopExpr binopExpr = (BinopExpr) rExpr;
		Value op1 = binopExpr.getOp1();
		Value op2 = binopExpr.getOp2();
		Z3Type op1Z3Type = Z3MiscFunctions.v().z3Type(op1.getType());
		Z3Type op2Z3Type = Z3MiscFunctions.v().z3Type(op2.getType());
		StringBuilder sb = new StringBuilder();
		
		BinopExprType binopType = Z3MiscFunctions.v().getBinopExprType(binopExpr);
		switch(binopType){
		//[start]ADD
		case ADD:
			//add_expr = immediate "+" immediate;
			//immediate = constant | local;
			//only Int, Real, String can ADD
			//Exceptional Cases: "084" + 42; we exclude them
			assert((op1Z3Type == Z3Type.Z3String && op2Z3Type == Z3Type.Z3String) ||
					(op1Z3Type != Z3Type.Z3String && op2Z3Type != Z3Type.Z3String));
			if(op1Z3Type == Z3Type.Z3String ){
				//( Concat "te" y1 )
				sb.append("( Concat ");
			}else{
				//(+ 2 i2)
				sb.append("(+ ");
			}
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append(" )");
			this.exprStr = sb.toString();
			break;
		//[end]ADD
		case AND:
			//and_expr = immediate "&" immediate;
			//TODO
			assert(false) : "AND Expr";
			break;
		//[start] DIV
		case DIV:
			//div_expr = immediate "/" immediate;
			//(div a b) integer division
			//(/ a b) float division
			if(op1Z3Type == Z3Type.Z3Real || op2Z3Type == Z3Type.Z3Real){
				sb.append("(/ ");
			}else{
				sb.append("(div ");
			}
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append(")");
			this.exprStr = sb.toString();
			break;
		//[end] DIV
		case EQ:
			//eq_expr = immediate "==" immediate;
			//b = r1 == r2
			//(assert (= b (= r1 r2)))
			sb.append("(= ");
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append(")");
			this.exprStr = sb.toString();
			break;
		case GE:
			//ge_expr = immediate ">=" immediate;
			//b = r1 >= r2
			//(assert (= b (>= r1 r2)))
			sb.append("(>= ");
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append(")");
			this.exprStr = sb.toString();
			break;
		case GT:
			//gt_expr = immediate ">" immediate;
			//b = r1 > r2
			//(assert (= b (> r1 r2)))
			sb.append("(> ");
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append(")");
			this.exprStr = sb.toString();
			break;
		case LE:
			//le_expr = immediate "<=" immediate;
			//b = r1 <= r2
			//(assert (= b (<= r1 r2)))
			sb.append("(<= ");
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append(")");
			this.exprStr = sb.toString();
			break;
		case LT:
			//lt_expr = immediate "<" immediate;
			//b = r1 < r2
			//(assert (= b (< r1 r2)))
			sb.append("(< ");
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append(")");
			this.exprStr = sb.toString();
			break;
		case MUL:
			//mul_expr = immediate "*" immediate;
			//(* op1 op2)
			sb.append("(* ");
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append(")");
			this.exprStr = sb.toString();
			break;
		case NE:
			//ne_expr = immediate "!=" immediate;
			//(not (= op1 op2))
			sb.append("(not (= ");
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append("))");
			this.exprStr = sb.toString();
			break;
		case OR:
			//or_expr = immediate "|" immediate;
			//TODO
			assert(false) : "OR Expr";
			break;
		case REM:
			//rem_expr = immediate "%" immediate;
			//(rem op1 op2)
			sb.append("(rem ");
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append(")");
			this.exprStr = sb.toString();
			break;
		case SUB:
			//sub_expr = immediate "-" immediate;
			//(- op1 op2)
			sb.append("(- ");
			if(op1 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op1, false, this.stmtIdx));
			}else{
				sb.append(op1.toString());
			}
			sb.append(" ");
			if(op2 instanceof Local){
				sb.append(fileGenerator.getRenameOf(op2, false, this.stmtIdx));
			}else{
				sb.append(op2.toString());
			}
			sb.append(")");
			this.exprStr = sb.toString();
			break;
		}
	}
}
