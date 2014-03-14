package com.monster.taint.z3;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.ConditionExpr;
import soot.jimple.Constant;
import soot.jimple.Expr;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeStmt;
import soot.jimple.NullConstant;
import soot.jimple.StaticFieldRef;

import com.monster.taint.path.MethodPath;
import com.monster.taint.z3.stmts.AssignStmtLARefRARef;
import com.monster.taint.z3.stmts.AssignStmtLARefRConstant;
import com.monster.taint.z3.stmts.AssignStmtLARefRExpr;
import com.monster.taint.z3.stmts.AssignStmtLARefRIFieldRef;
import com.monster.taint.z3.stmts.AssignStmtLARefRLocal;
import com.monster.taint.z3.stmts.AssignStmtLARefRSFieldRef;
import com.monster.taint.z3.stmts.AssignStmtLIFieldRefRARef;
import com.monster.taint.z3.stmts.AssignStmtLIFieldRefRConstant;
import com.monster.taint.z3.stmts.AssignStmtLIFieldRefRExpr;
import com.monster.taint.z3.stmts.AssignStmtLIFieldRefRIFieldRef;
import com.monster.taint.z3.stmts.AssignStmtLIFieldRefRLocal;
import com.monster.taint.z3.stmts.AssignStmtLIFieldRefRSFieldRef;
import com.monster.taint.z3.stmts.AssignStmtLLocalRARef;
import com.monster.taint.z3.stmts.AssignStmtLLocalRConstant;
import com.monster.taint.z3.stmts.AssignStmtLLocalRExpr;
import com.monster.taint.z3.stmts.AssignStmtLLocalRIFieldRef;
import com.monster.taint.z3.stmts.AssignStmtLLocalRLocal;
import com.monster.taint.z3.stmts.AssignStmtLLocalRSFieldRef;
import com.monster.taint.z3.stmts.AssignStmtLSFieldRefRARef;
import com.monster.taint.z3.stmts.AssignStmtLSFieldRefRConstant;
import com.monster.taint.z3.stmts.AssignStmtLSFieldRefRExpr;
import com.monster.taint.z3.stmts.AssignStmtLSFieldRefRIFieldRef;
import com.monster.taint.z3.stmts.AssignStmtLSFieldRefRLocal;
import com.monster.taint.z3.stmts.AssignStmtLSFieldRefRSFieldRef;
import com.monster.taint.z3.stmts.MyIfStmt;

/**
 * The patterns we can handle currently:
 * @1 $r2 := @parameter2: android.content.Intent
 * 		-- ignored, comment it ";ignored ..."
 * 
 * @2 $r2 := @parameter2: java.lang.String
 * 		-- (declare-variable r2 String)
 * 
 * @3 $r5 = virtualinvoke $r2.<android.content.Intent: java.lang.String getAction()>()"
 * 		-- (declare-variable r5 String) 
 * 		   (declare-fun Intent_getAction_String_void () String)
 * 		   (assert (= r5 Intent_getAction_String_void) )
 * 
 * @4 $z0 = virtualinvoke $r4.<java.lang.String: boolean equals(java.lang.Object)>($r5)
 * 			if $z0 == 0 goto $z0 = 0
 *		-- true: 	(assert (= (= r4 r5) true) )
 *		-- false: 	(assert (= (= r4 r5) false) )
 *
 * @5 $r6 = virtualinvoke $r2.<android.content.Intent: android.os.Bundle getExtras()>()
 * 		-- ignored, comment it ";ignored ..."
 * 
 * @6 $r11 = virtualinvoke $r6.<android.os.Bundle: java.lang.Object get(java.lang.String)>("pdus")
 * 		-- 	(declare-fun Bundle_get_String_String (String) String)
 * 		--  (declare-variable r11 String)
 * 		--	(assert (= r11 (Bundle_get_String_String "pdus")) )
 *	
 * @7 r10 = (java.lang.Object[]) $r11
 *		--	(declare-variable r10 String)
 *		--	(assert (= r10 r11) ) 
 *
 * @8 $r10 = (java.lang.Object[]) $r10"
 * 		--	(declare-variable r10 String)
 * 		--	(assert (= r10 r10) )
 * 
 * @9 $i1 = lengthof $r10
 * 		--	(declare-variable i1 Int)
 * 		--	(assert (= i1 (Length r10)) )
 * 
 * @10 $i0 = 0
 * 		-- (declare-variable i0 Int)
 *		-- (assert (= i0 0) )
 *
 * @11 $i0 = $i0 + 1
 * 	   $i0 = $i0 + 1
 * 		-- (declare-variable i0_redefine_1 Int)
 * 		-- (assert (= i0_redefine_1 (+ i0 1)) )
 * 		-- (declare_variable i0_redefine_2 Int)
 * 		-- (assert (= i0_redefine_2 (+ i0_redefine_1 1)) )
 * 
 * 
 * @author chenxiong
 *
 */
public class SMT2FileGenerator {
	private Logger logger = LoggerFactory.getLogger(getClass());
	private final boolean debug = false;
	private final String SMT2_DIR = "../monster-out/smt2/";
	
	private static SMT2FileGenerator instance = null;
	
	//we use a map to record the variables need to rename, key is the variable andk
	//value is a list of unit indexes at which the variable should be renamed
	HashMap<Value, ArrayList<Integer>> renamesMap = null;
	//the declared variables names
	ArrayList<String> declaredVariables = null;
	//the declared functions
	ArrayList<String> declaredFunctions = null;
	//array size map
	HashMap<String, String> arraySizeMap = null;
	
	private SMT2FileGenerator(){}
	
	public static SMT2FileGenerator v(){
		if(instance == null){
			instance = new SMT2FileGenerator();
		}
		return instance;
	}

	/**
	 * generate the smt2 format file according to the 'constraintList'
	 * 
	 * @param constraintList
	 * @param methodPath
	 * @throws IOException
	 */
	public void generateSMT2File(ArrayList<Constraint> constraintList, MethodPath methodPath,
			ArrayList<Unit> allRelatedUnits) throws IOException{
		SootMethod method = methodPath.getMethodHub().getMethod();
		String fileName = method.getDeclaringClass().getName() + "-" + method.getName() + 
				"-" + methodPath.getPathID() + ".smt";
		PrintWriter smt2Writer = new PrintWriter(SMT2_DIR + fileName, "UTF-8");
	
		renamesMap = new HashMap<Value, ArrayList<Integer>>();
		declaredVariables = new ArrayList<String>();
		declaredFunctions = new ArrayList<String>();
		arraySizeMap = new HashMap<String, String>();
		
		//first, we should handle the case (e.g.'i0 = i0 + 1') in which the
		//defboxes and useboxes share certain same values
		handleRedefinedValues(allRelatedUnits);
	
		//test
		if(debug){
			smt2Writer.println("***********************");
			Iterator<Entry<Value, ArrayList<Integer>>> iter = renamesMap.entrySet().iterator();
			while(iter.hasNext()){
				Entry<Value, ArrayList<Integer>> entry = iter.next();
				Value kValue = entry.getKey();
				ArrayList<Integer> vLineNumbers = entry.getValue();
				smt2Writer.print(kValue.toString() + ": ");
				for(Integer lineNumber : vLineNumbers){
					smt2Writer.print(" " + lineNumber);
				}
				smt2Writer.println();
			}
			smt2Writer.println("***********************");
			
			for(int i = 0; i < allRelatedUnits.size(); i++){
				Unit unit = allRelatedUnits.get(i);
				smt2Writer.println();
				smt2Writer.println(unit.toString());
				if(unit instanceof AssignStmt){
					AssignStmt assignStmt = (AssignStmt) unit;
					List<ValueBox> defBoxes = assignStmt.getDefBoxes();
					List<ValueBox> useBoxes = assignStmt.getUseBoxes();
					
					for(ValueBox defBox : defBoxes){
						Value defValue = defBox.getValue();
						ArrayList<Integer> defineLineNumbers = getDefineLineNumbers(defValue); 
						if(defineLineNumbers != null){
							int redefineTimes = SSAMiscFunctions.v().getDefRedefineTimes(defineLineNumbers, i);
							if(redefineTimes > 0){
								smt2Writer.print(defValue.toString() + "_redefine_" + redefineTimes);
							}else{
								smt2Writer.print(defValue.toString());
							}
						}
					}
					smt2Writer.print(" = ");
					for(ValueBox useBox : useBoxes){
						Value useValue = useBox.getValue();
						ArrayList<Integer> defineLineNumbers = getDefineLineNumbers(useValue);
						if(defineLineNumbers != null){
							int redefineTimes = SSAMiscFunctions.v().getUseRedefineTimes(defineLineNumbers, i);
							if(redefineTimes > 0){
								smt2Writer.print(useValue.toString() + "_redefine_" + redefineTimes);
							}else{
								smt2Writer.print(useValue.toString());
							}
						}
					}
					smt2Writer.println();
				}
			}
		}
	
		smt2Writer.println(";this path has " + constraintList.size() + " constraints");
		smt2Writer.println();
		
			
			
		//convert unit to smt2 format statement
		for(int i = 0; i < allRelatedUnits.size(); i++){
			Unit unit = allRelatedUnits.get(i);
			smt2Writer.println(";" + unit.toString());
			//we only care about AssignStmt, IfStmt and InvokeStmt
			if(unit instanceof AssignStmt){
				AssignStmt assignStmt = (AssignStmt) unit;
				parseAssignStmt(assignStmt, i, smt2Writer);
			}else if(unit instanceof InvokeStmt){
					
			}else if(unit instanceof IfStmt){
				IfStmt ifStmt = (IfStmt) unit;
				boolean satisfied = false;
				for(Constraint constraint : constraintList){
					if(constraint.ifStmtEquals(ifStmt)){
						satisfied = constraint.isSatisfied();
						break;
					}
				}
				parseIfStmt(ifStmt, satisfied, i, smt2Writer);;
			}
		}
		
		smt2Writer.close();
	}

	/**
	 * condition = eq_expr | ge_expr | le_expr | lt_expr | ne_expr | gt_expr;
	 * eq_expr = immediate "==" immediate; **the immediate maybe a null constant
	 * ge_expr = immediate ">=" immediate; 
	 * gt_expr = immediate ">" immediate; 
	 * le_expr = immediate "<=" immediate; 
	 * lt_expr = immediate "<" immediate;
	 * ne_expr = immediate "!=" immediate; 
	 * @param ifStmt
	 * @param satisfied
	 * @param stmtIdx
	 * @param writer
	 */
	private void parseIfStmt(IfStmt ifStmt, boolean satisfied, int stmtIdx, PrintWriter writer){
		Value conditionValue = ifStmt.getCondition();
		ConditionExpr conditionExpr = (ConditionExpr) conditionValue;
		MyIfStmt myIfStmt = new MyIfStmt(this, writer, satisfied, conditionExpr, stmtIdx);
		myIfStmt.jet();
	}
	
	private void parseAssignStmt(AssignStmt assignStmt, int stmtIdx, PrintWriter writer){
		Value lvalue = assignStmt.getLeftOp();
		Value rvalue = assignStmt.getRightOp();
		//assign_stmt = variable "=" rvalue;
		//variable = array_ref | instance_field_ref | static_field_ref | local;
		if(lvalue instanceof Local){
			Local lLocal = (Local) lvalue;
			
			//rvalue = array_ref | constant | expr | instance_field_ref | local |
			//next_next_stmt_address | static_field_ref
			if(rvalue instanceof Constant){
				Constant constant = (Constant) rvalue;
				AssignStmtLLocalRConstant lLocalRConstant = new AssignStmtLLocalRConstant(writer, this, 
						stmtIdx, lLocal, constant);
				lLocalRConstant.jet();
			}else if(rvalue instanceof Local){
				Local rLocal = (Local) rvalue;
				AssignStmtLLocalRLocal lLocalRLocal = new AssignStmtLLocalRLocal(writer, this, 
						stmtIdx, lLocal, rLocal);
				lLocalRLocal.jet();
			}else if(rvalue instanceof InstanceFieldRef){
				InstanceFieldRef rIFieldRef = (InstanceFieldRef) rvalue;
				AssignStmtLLocalRIFieldRef lLocalRIFieldRef = new AssignStmtLLocalRIFieldRef(writer, this,
						stmtIdx, lLocal, rIFieldRef);
				lLocalRIFieldRef.jet();
			}else if(rvalue instanceof StaticFieldRef){
				StaticFieldRef rSFieldRef = (StaticFieldRef) rvalue;
				AssignStmtLLocalRSFieldRef lLocalRSFieldRef = new AssignStmtLLocalRSFieldRef(writer, this, 
						stmtIdx, lLocal, rSFieldRef);
				lLocalRSFieldRef.jet();
			}else if(rvalue instanceof ArrayRef){
				ArrayRef rARef = (ArrayRef) rvalue;
				AssignStmtLLocalRARef lLocalRARef = new AssignStmtLLocalRARef(writer, this, 
						stmtIdx, lLocal, rARef);
				lLocalRARef.jet();
			}else if(rvalue instanceof Expr){
				Expr rExpr = (Expr) rvalue;
				AssignStmtLLocalRExpr lLocalRExpr = new AssignStmtLLocalRExpr(writer, this, 
						stmtIdx, lLocal, rExpr);
				lLocalRExpr.jet();
			}
		}else if(lvalue instanceof InstanceFieldRef){
			InstanceFieldRef lIFieldRef = (InstanceFieldRef) lvalue;
			
			if(rvalue instanceof Constant){
				Constant rConstant = (Constant) rvalue;
				AssignStmtLIFieldRefRConstant lIFiedlRefRConstant = new AssignStmtLIFieldRefRConstant(writer, 
						this, stmtIdx, lIFieldRef, rConstant);
				lIFiedlRefRConstant.jet();
			}else if(rvalue instanceof Local){
				Local rLocal = (Local) rvalue;
				AssignStmtLIFieldRefRLocal lIFieldRefRLocal = new AssignStmtLIFieldRefRLocal(writer, 
						this, stmtIdx, lIFieldRef, rLocal);
				lIFieldRefRLocal.jet();
			}else if(rvalue instanceof InstanceFieldRef){
				InstanceFieldRef rIFieldRef = (InstanceFieldRef) rvalue;
				AssignStmtLIFieldRefRIFieldRef lIFieldRefRIFieldRef = new AssignStmtLIFieldRefRIFieldRef(writer, 
						this, stmtIdx, lIFieldRef, rIFieldRef);
				lIFieldRefRIFieldRef.jet();
			}else if(rvalue instanceof StaticFieldRef){
				StaticFieldRef rSFieldRef = (StaticFieldRef) rvalue;
				AssignStmtLIFieldRefRSFieldRef lIFieldRefRSFieldRef = new AssignStmtLIFieldRefRSFieldRef(writer, this,
						stmtIdx, lIFieldRef, rSFieldRef);
				lIFieldRefRSFieldRef.jet();
			}else if(rvalue instanceof ArrayRef){
				ArrayRef rARef = (ArrayRef) rvalue;
				AssignStmtLIFieldRefRARef lIFieldRefRARef = new AssignStmtLIFieldRefRARef(writer, this,
						stmtIdx, lIFieldRef, rARef);
				lIFieldRefRARef.jet();
			}else if(rvalue instanceof Expr){
				Expr rExpr = (Expr) rvalue;
				AssignStmtLIFieldRefRExpr lIFieldRefRExpr = new AssignStmtLIFieldRefRExpr(writer, this,
						stmtIdx, lIFieldRef, rExpr);
				lIFieldRefRExpr.jet();
			}
		}else if(lvalue instanceof StaticFieldRef){
			StaticFieldRef lSFieldRef = (StaticFieldRef) lvalue;
			
			if(rvalue instanceof Constant){
				Constant rConstant = (Constant) rvalue;
				AssignStmtLSFieldRefRConstant lSFieldRefRConstant = new AssignStmtLSFieldRefRConstant(writer, 
						this, stmtIdx, lSFieldRef, rConstant);
				lSFieldRefRConstant.jet();
			}else if(rvalue instanceof Local){
				Local rLocal = (Local) rvalue;
				AssignStmtLSFieldRefRLocal lSFieldRefRLocal = new AssignStmtLSFieldRefRLocal(writer, this,
						stmtIdx, lSFieldRef, rLocal);
				lSFieldRefRLocal.jet();
			}else if(rvalue instanceof InstanceFieldRef){
				InstanceFieldRef rIFieldRef = (InstanceFieldRef) rvalue;
				AssignStmtLSFieldRefRIFieldRef lSFieldRefRIFieldRef = new AssignStmtLSFieldRefRIFieldRef(writer, this,
						stmtIdx, lSFieldRef, rIFieldRef);
				lSFieldRefRIFieldRef.jet();
			}else if(rvalue instanceof StaticFieldRef){
				StaticFieldRef rSFieldRef = (StaticFieldRef) rvalue;
				AssignStmtLSFieldRefRSFieldRef lSFieldRefRSFieldRef = new AssignStmtLSFieldRefRSFieldRef(writer, this,
						stmtIdx, lSFieldRef, rSFieldRef);
				lSFieldRefRSFieldRef.jet();
			}else if(rvalue instanceof ArrayRef){
				ArrayRef rARef = (ArrayRef) rvalue;
				AssignStmtLSFieldRefRARef lSFieldRefRARef = new AssignStmtLSFieldRefRARef(writer, this,
						stmtIdx, lSFieldRef, rARef);
				lSFieldRefRARef.jet();
			}else if(rvalue instanceof Expr){
				Expr rExpr = (Expr) rvalue;
				AssignStmtLSFieldRefRExpr lSFieldRefRExpr = new AssignStmtLSFieldRefRExpr(writer, this,
						stmtIdx, lSFieldRef, rExpr);
				lSFieldRefRExpr.jet();
			}
		}else if(lvalue instanceof ArrayRef){
			ArrayRef lARef = (ArrayRef) lvalue;
			
			if(rvalue instanceof Constant){
				Constant rConstant = (Constant) rvalue;
				AssignStmtLARefRConstant lARefRConstant = new AssignStmtLARefRConstant(writer, this,
						stmtIdx, lARef, rConstant);
				lARefRConstant.jet();
			}else if(rvalue instanceof Local){
				Local rLocal = (Local) rvalue;
				AssignStmtLARefRLocal lARefRLocal = new AssignStmtLARefRLocal(writer, this,
						stmtIdx, lARef, rLocal);
				lARefRLocal.jet();
			}else if(rvalue instanceof InstanceFieldRef){
				InstanceFieldRef rIFieldRef = (InstanceFieldRef) rvalue;
				AssignStmtLARefRIFieldRef lARefRIFieldRef = new AssignStmtLARefRIFieldRef(writer, this,
						stmtIdx, lARef, rIFieldRef);
				lARefRIFieldRef.jet();
			}else if(rvalue instanceof StaticFieldRef){
				StaticFieldRef rSFieldRef = (StaticFieldRef) rvalue;
				AssignStmtLARefRSFieldRef lARefRSFieldRef = new AssignStmtLARefRSFieldRef(writer, this,
						stmtIdx, lARef, rSFieldRef);
				lARefRSFieldRef.jet();
			}else if(rvalue instanceof ArrayRef){
				ArrayRef rARef = (ArrayRef) rvalue;
				AssignStmtLARefRARef lARefRARef = new AssignStmtLARefRARef(writer, this,
						stmtIdx, lARef, rARef);
				lARefRARef.jet();
			}else if(rvalue instanceof Expr){
				Expr rExpr = (Expr) rvalue;
				AssignStmtLARefRExpr lARefRExpr = new AssignStmtLARefRExpr(writer, this,
						stmtIdx, lARef, rExpr);
				lARefRExpr.jet();
			}
		}
	}
	
	private void recordValueInRenameMap(Value value, int index){
		Iterator<Entry<Value, ArrayList<Integer>>> iter = renamesMap.entrySet().iterator();
		boolean valueExist = false;
		while(iter.hasNext()){
			Entry<Value, ArrayList<Integer>> entry = iter.next();
			Value kValue = entry.getKey();
			if(SSAMiscFunctions.v().twoValueEquals(value, kValue)){
				addIntegerToList(entry.getValue(), index);
				valueExist = true;
				break;
			}
		}
		if(!valueExist){
			ArrayList<Integer> lineNumbersList = new ArrayList<Integer>();
			lineNumbersList.add(new Integer(index));
			renamesMap.put(value, lineNumbersList);
		}
	}
	private void addIntegerToList(ArrayList<Integer> integerList, int n){
		boolean exist = false;
		for(Integer integer : integerList){
			if(integer.intValue() == n){
				exist = true;
				break;
			}
		}
		if(!exist){
			integerList.add(new Integer(n));
		}
	}
	private ArrayList<Integer> getDefineLineNumbers(Value value){
		Iterator<Entry<Value, ArrayList<Integer>>> iter = renamesMap.entrySet().iterator();
		while(iter.hasNext()){
			Entry<Value, ArrayList<Integer>> entry = iter.next();
			Value kValue = entry.getKey();
			if(SSAMiscFunctions.v().twoValueEquals(value, kValue)){
				return entry.getValue();
			}
		}
		return null;
	}
	
	public ArrayList<String> getDeclaredVariables(){
		return this.declaredVariables;
	}
	
	public ArrayList<String> getDeclaredFunctions(){
		return this.declaredFunctions;
	}
	
	public HashMap<String, String> getArraySizeMap(){
		return this.arraySizeMap;
	}
	
	public String getRenameOf(Value value, boolean defValue, int index){
		ArrayList<Integer> lineNumbers = getDefineLineNumbers(value);
		int redefineTimes = 0;
		String valueStr = null;
		
		//constant
		if(value instanceof Constant){
			if(value instanceof NullConstant){
				return "\"\"";
			}else{
				return value.toString();
			}
		}
		
		if(value instanceof Local){
			valueStr = ((Local) value).getName();
		}else if(value instanceof InstanceFieldRef){
			InstanceFieldRef iFieldRef = (InstanceFieldRef) value;
			valueStr = iFieldRef.getBase().toString() + "_" + iFieldRef.getField().getName();
		}else if(value instanceof StaticFieldRef){
			StaticFieldRef sFieldRef = (StaticFieldRef) value;
			valueStr = sFieldRef.getClass().getSimpleName() + "_" + sFieldRef.getField().getName();
		}else if(value instanceof ArrayRef){
			ArrayRef arrayRef = (ArrayRef) value;
			valueStr = arrayRef.getBase().toString();
		}
		
		if(lineNumbers != null){
			if(defValue){
				redefineTimes = SSAMiscFunctions.v().getDefRedefineTimes(lineNumbers, index);
			}else{
				redefineTimes = SSAMiscFunctions.v().getUseRedefineTimes(lineNumbers, index);
			}
		}
		if(redefineTimes > 0){
			return valueStr + "_redefine_" + redefineTimes;
		}else{
			return valueStr;
		}
	}
	
	/**
	 * iterate 'units' and handle the pattern @11 -- refer comment of this class 
	 * @param units
	 */
	private void handleRedefinedValues(ArrayList<Unit> units){
		for(int i = 0; i < units.size(); i++){
			Unit unit = units.get(i);
			/* "assign_stmt = variable "=" rvalue;"
			 * -- we only handle the assign_stmt
			 */
			if(unit instanceof AssignStmt){
				AssignStmt assignStmt = (AssignStmt) unit;
				Value lvalue = assignStmt.getLeftOp();
				Value rvalue = assignStmt.getRightOp();
				List<ValueBox> rUseBoxes = rvalue.getUseBoxes();
				/*
				 * variable = array_ref | instance_field_ref | static_field_ref | local;
				 */
				if(lvalue instanceof ArrayRef){
					/*
					 * (declare-const a1 (Array Int Int))
					 * (declare-const i Int)
					 * ;a[i] = a[i] + 42
					 * (declare-const b1 (Array Int Int))
					 * (assert (= (select b1 i) (+ (select a1 i) 42)))
					 * (check-sat)
					 * (get-model)
					 * ;a[i] = a[i+1] + 3
					 * (assert (= (select a1 i) (+ (select a1 (+ 1 i)) 3)))
					 * (check-sat)
					 * (get-model)
					 * -- If the array ref's base and index are both the same as one of the
					 * 	  right value's useboxes.
					 */
					ArrayRef aRef = (ArrayRef) lvalue;
					if(SSAMiscFunctions.v().arrayRefRedefined(aRef, rUseBoxes)){
						recordValueInRenameMap(aRef, i);
					}
				}else if(lvalue instanceof InstanceFieldRef){
					//b.f = b.f + 42
					InstanceFieldRef iFieldRef = (InstanceFieldRef) lvalue;
					if(SSAMiscFunctions.v().instanceFieldRefRedefined(iFieldRef, rUseBoxes)){
						recordValueInRenameMap(iFieldRef, i);
					}
				}else if(lvalue instanceof StaticFieldRef){
					StaticFieldRef sFieldRef = (StaticFieldRef) lvalue;
					if(SSAMiscFunctions.v().staticFieldRefRedefined(sFieldRef, rUseBoxes)){
						recordValueInRenameMap(sFieldRef, i);
					}
				}else if(lvalue instanceof Local){
					Local local = (Local) lvalue;
					if(SSAMiscFunctions.v().localRedefined(local, rUseBoxes)){
						recordValueInRenameMap(local, i);
					}
				}
			}
		}
	}
}
