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
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeStmt;
import soot.jimple.StaticFieldRef;

import com.monster.taint.path.MethodPath;
import com.monster.taint.z3.Z3MiscFunctions.Z3Type;

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
	HashMap<Value, ArrayList<Integer>> renamesMap = new HashMap<Value, ArrayList<Integer>>();
	//the defined variables names
	ArrayList<String> definedVariables = new ArrayList<String>();
	
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
		
		//first, we should handle the case (e.g.'i0 = i0 + 1') in which the
		//defboxes and useboxes share certain same values
		renamesMap.clear();//important!
		definedVariables.clear();
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
		for(Unit unit : allRelatedUnits){
			smt2Writer.println(";" + unit.toString());
			//we only care about AssignStmt, IfStmt and InvokeStmt
			if(unit instanceof AssignStmt){
				AssignStmt assignStmt = (AssignStmt) unit;
				parseAssignStmt(assignStmt, allRelatedUnits.indexOf(unit), smt2Writer);
			}else if(unit instanceof InvokeStmt){
					
			}else if(unit instanceof IfStmt){
				smt2Writer.println();	
			}
		}
		
		smt2Writer.close();
	}
	
	private void parseAssignStmt(AssignStmt assignStmt, int stmtIdx, PrintWriter writer){
		Value lvalue = assignStmt.getLeftOp();
		Value rvalue = assignStmt.getRightOp();
		//assign_stmt = variable "=" rvalue;
		//variable = array_ref | instance_field_ref | static_field_ref | local;
		if(lvalue instanceof Local){
			Local lLocal = (Local) lvalue;
			String lLocalName = getRenameOf(lvalue, true, stmtIdx);
			Type type = lLocal.getType();
			Z3Type z3Type = Z3MiscFunctions.v().z3Type(type);
			if(!this.definedVariables.contains(lLocalName) && z3Type != Z3Type.Z3Unkonwn){
				writer.println(Z3MiscFunctions.v().getDeclareStmt(lLocalName, z3Type));
				this.definedVariables.add(lLocalName);
			}
		}else if(lvalue instanceof InstanceFieldRef){
			
		}else if(lvalue instanceof StaticFieldRef){
			
		}else if(lvalue instanceof ArrayRef){
			
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
	
	private String getRenameOf(Value value, boolean defValue, int index){
		ArrayList<Integer> lineNumbers = getDefineLineNumbers(value);
		int redefineTimes = 0;
		if(lineNumbers != null){
			if(defValue){
				redefineTimes = SSAMiscFunctions.v().getDefRedefineTimes(lineNumbers, index);
			}else{
				redefineTimes = SSAMiscFunctions.v().getUseRedefineTimes(lineNumbers, index);
			}
		}
		if(redefineTimes > 0){
			return value.toString() + "_redefine_" + redefineTimes;
		}else{
			return value.toString();
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
