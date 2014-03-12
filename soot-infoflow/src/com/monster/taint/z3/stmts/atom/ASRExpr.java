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
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.Expr;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.VirtualInvokeExpr;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;

public class ASRExpr {
	private final String STRING_CLASS = "java.lang.String";
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
	 * r5 = r2.getAction()
	 * (declare-variable r2 String)
	 * (declare-fun android_content_Intent$$java_lang_String$$void$$getAction (String) String)
	 * (assert (= r5 f...$$getAction(r2)))
	 */
	private void jetFunctions(){
		InvokeExpr invokeExpr = (InvokeExpr) rExpr;
		SootMethodRef methodRef = invokeExpr.getMethodRef();
		
		//if this is a java.lang.String.func, we don't need to declare it
		if(methodRef.declaringClass().getName().equals(STRING_CLASS)){
			return;
		}
		
		String funStr = constructFunStr(invokeExpr);
		Type thisType = null;
		if(!fileGenerator.getDeclaredFunctions().contains(funStr)){
			if(invokeExpr instanceof StaticInvokeExpr){
				writer.println(Z3MiscFunctions.v().getFuncDeclareStmt(funStr, thisType,
						methodRef.parameterTypes(), methodRef.returnType()));
			}else{
				if(invokeExpr instanceof InterfaceInvokeExpr){
					thisType = ((InterfaceInvokeExpr) invokeExpr).getBase().getType();
				}else if(invokeExpr instanceof SpecialInvokeExpr){
					thisType = ((SpecialInvokeExpr) invokeExpr).getBase().getType();
				}else if(invokeExpr instanceof VirtualInvokeExpr){
					thisType = ((VirtualInvokeExpr) invokeExpr).getBase().getType();
				}
				writer.println(Z3MiscFunctions.v().getFuncDeclareStmt(funStr, thisType,
						methodRef.parameterTypes(), methodRef.returnType()));
			}
			fileGenerator.getDeclaredFunctions().add(funStr);
		}
	}
	
	private String constructFunStr(InvokeExpr invokeExpr){
		StringBuilder funSB = new StringBuilder();
		SootMethodRef methodRef = invokeExpr.getMethodRef();
		Type thisType = null;
		
		if(invokeExpr instanceof InterfaceInvokeExpr){
			thisType = ((InterfaceInvokeExpr) invokeExpr).getBase().getType();
		}else if(invokeExpr instanceof SpecialInvokeExpr){
			thisType = ((SpecialInvokeExpr) invokeExpr).getBase().getType();
		}else if(invokeExpr instanceof VirtualInvokeExpr){
			thisType = ((VirtualInvokeExpr) invokeExpr).getBase().getType();
		}
	
		//class name
		funSB.append(methodRef.declaringClass().getName().replace(".", "_"));
		funSB.append("$$");
		//return type
		funSB.append(methodRef.returnType().toString().replace(".", "_"));
		//parameter and this types
		funSB.append("$$");
		//this type
		if(thisType != null){
			funSB.append(thisType.toString().replace(".", "_"));
			funSB.append("$");
		}
		for(Type paramType : methodRef.parameterTypes()){
			funSB.append(paramType.toString().replace(".", "_"));
			funSB.append("$");
		}
		funSB.append(methodRef.name());
		return funSB.toString();
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
				jetCastExprStr();
				break;
			case INVOKE:
				jetInvokeExpr();
				break;
			case NEWARRAY:
				jetNewArrayExpr();
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
	 * new_array_expr = "new" type "[" immediate "]"; 
	 * 
	 */
	private void jetNewArrayExpr(){
		
	}

	/*
	 * 1. we model java.lang.String's methods
	 * 2. for other methods, just call them
	 * 
	 * for examples: 
	 * 1. b = s1.contains(s2)
	 * 	(assert (= b (Contains s1 s2)))
	 * 
	 * 2. b = r2.get(s)
	 *  (assert (= b get(r2 s)))
	 *	see this.jetFunctions for more 
	 *	
	 * invoke_expr = interface_invoke_expr | special_invoke_expr | static_invoke_expr |
     * virtual_invoke_expr; 
	 */
	private void jetInvokeExpr(){
		InvokeExpr invokeExpr = (InvokeExpr) rExpr;
		SootMethodRef methodRef = invokeExpr.getMethodRef();
		if(methodRef.declaringClass().getName().equals(STRING_CLASS)){
			//TODO
		}else{
			Value thisBase = null;
			if(invokeExpr instanceof InterfaceInvokeExpr){
				thisBase = ((InterfaceInvokeExpr) invokeExpr).getBase();
			}else if(invokeExpr instanceof SpecialInvokeExpr){
				thisBase = ((SpecialInvokeExpr) invokeExpr).getBase();
			}else if(invokeExpr instanceof VirtualInvokeExpr){
				thisBase = ((VirtualInvokeExpr) invokeExpr).getBase();
			}
			String funStr = constructFunStr(invokeExpr);
			StringBuilder sb = new StringBuilder();
			sb.append(funStr);
			sb.append("(");
			
			if(thisBase != null){
				String thisBaseName = fileGenerator.getRenameOf(thisBase, false, this.stmtIdx);
				sb.append(thisBaseName);
				sb.append(" ");
			}
			
			for(Value param : invokeExpr.getArgs()){
				if(param instanceof Constant){
					sb.append(param.toString());
				}else{
					String paramName = fileGenerator.getRenameOf(param, false, this.stmtIdx);
					sb.append(paramName);
				}
				sb.append(" ");
			}
			
			sb.append(")");
			this.exprStr = sb.toString();
		}
	}

	/**
	 *	cast_expr = "(" type ")" immediate; 
	 *  a = (type) b
	 *  (assert (= a b))
	 */
	private void jetCastExprStr(){
		CastExpr castExpr = (CastExpr) rExpr;
		Value immValue = castExpr.getOp();
		if(immValue instanceof Local){
			this.exprStr = fileGenerator.getRenameOf(immValue, false, this.stmtIdx);
		}else{
			this.exprStr = immValue.toString();
		}
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
		//[start] EQ
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
		//[end] EQ
		//[start] GE
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
		//[end] GE
		//[start] GT
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
		//[end] GT
		//[start] LE
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
		//[end] LE
		//[start] LT
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
		//[end] LT
		//[start] MUL
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
		//[end] MUL
		//[start] NE
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
		//[end] NE
		case OR:
			//or_expr = immediate "|" immediate;
			//TODO
			assert(false) : "OR Expr";
			break;
		//[start] REM
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
		//[end] REM
		//[start] SUB
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
		//[end] SUB
		}
	}
}
