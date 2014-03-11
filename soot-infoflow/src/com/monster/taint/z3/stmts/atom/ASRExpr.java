package com.monster.taint.z3.stmts.atom;

import java.io.PrintWriter;
import java.util.List;

import soot.Local;
import soot.SootMethodRef;
import soot.Type;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
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
}
