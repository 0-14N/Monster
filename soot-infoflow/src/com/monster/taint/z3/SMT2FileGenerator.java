package com.monster.taint.z3;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootMethod;
import soot.Unit;

import com.monster.taint.path.MethodPath;

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
 * @author chenxiong
 *
 */
public class SMT2FileGenerator {
	private Logger logger = LoggerFactory.getLogger(getClass());
	private final String SMT2_DIR = "../monster-out/smt2/";
	
	private static SMT2FileGenerator instance = null;
	
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
	public void generateSMT2File(ArrayList<Constraint> constraintList, MethodPath methodPath) throws IOException{
		SootMethod method = methodPath.getMethodHub().getMethod();
		String fileName = method.getDeclaringClass().getName() + "-" + method.getName() + 
				"-" + methodPath.getPathID() + ".smt";
		PrintWriter smt2Writer = new PrintWriter(SMT2_DIR + fileName, "UTF-8");
		
		smt2Writer.println(";this path has " + constraintList.size() + " constraints");
		
		for(Constraint constraint : constraintList){
			smt2Writer.println();
			ArrayList<Unit> relatedUnits = constraint.getRelatedUnits();
			
			//first add the related units as comment
			writeRelatedUnitsComment(relatedUnits, smt2Writer);
			
			//
		}
		
		smt2Writer.close();
	}
	
	private void writeRelatedUnitsComment(ArrayList<Unit> units, PrintWriter writer){
		for(Unit unit : units){
			writer.println(";" + unit.toString());
		}
	}
}
