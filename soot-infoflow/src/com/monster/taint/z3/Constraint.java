package com.monster.taint.z3;

import soot.jimple.IfStmt;

public class Constraint {
	IfStmt ifStmt = null;
	boolean satisfied = false;
	
	public Constraint(IfStmt ifStmt, boolean satisfied){
		this.ifStmt = ifStmt;
		this.satisfied = satisfied;
	}
}
