package com.monster.taint.z3.stmts;

import java.io.PrintWriter;

import com.monster.taint.z3.SMT2FileGenerator;
import com.monster.taint.z3.Z3Type;
import com.monster.taint.z3.Z3MiscFunctions;
import com.monster.taint.z3.stmts.atom.ASLLocal;
import com.monster.taint.z3.stmts.atom.ASRARef;

import soot.Local;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.Constant;

public class AssignStmtLLocalRARef{
	private PrintWriter writer = null;
	private SMT2FileGenerator fileGenerator = null;
	private int stmtIdx = 0;
	private ASLLocal lLocal = null;
	private ASRARef rARef = null;
	
	
	public AssignStmtLLocalRARef(PrintWriter writer, SMT2FileGenerator fileGenerator,
			int stmtIdx, Local lLocal, ArrayRef rARef){
		this.writer = writer;
		this.fileGenerator = fileGenerator;
		this.stmtIdx = stmtIdx;
		this.lLocal = new ASLLocal(writer, fileGenerator, stmtIdx, lLocal);
		this.rARef = new ASRARef(writer, fileGenerator, stmtIdx, rARef);
	}
	
	public void jet(){
		this.lLocal.jet();
		this.rARef.jet();
		
		Value arrayIndex = rARef.getRARef().getIndex();
		String arrayIndexStr = null;
		if(arrayIndex instanceof Constant){
			arrayIndexStr = arrayIndex.toString();
		}else{
			arrayIndexStr = fileGenerator.getRenameOf(arrayIndex, false, this.stmtIdx);
		}
		writer.println(Z3MiscFunctions.v().getAssertLocalEqualArrayRef(lLocal.getLLocalName(), 
				rARef.getARefName(), arrayIndexStr));
	}
	
}
