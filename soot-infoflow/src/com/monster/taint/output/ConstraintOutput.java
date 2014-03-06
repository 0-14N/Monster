package com.monster.taint.output;

import java.util.ArrayList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.monster.taint.z3.Constraint;

import soot.Unit;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;

public class ConstraintOutput {
	private Logger logger = LoggerFactory.getLogger(getClass());
	
	private static ConstraintOutput instance = null;
	
	private ConstraintOutput(){}
	
	public static ConstraintOutput v(){
		if(instance == null){
			instance = new ConstraintOutput();
		}
		return instance;
	}
	
	public void extractConstraints(PathChain pathChain){
		Unit activationUnit = pathChain.getActivationUnit();
		ArrayList<Unit> unitsOnPath = pathChain.getSinglePath().getUnitsOnPath(); 
		int activationIndex = unitsOnPath.indexOf(activationUnit);
		assert(activationIndex >= 0 && activationIndex < unitsOnPath.size());
		
		//backwards from 'activationUnit' and find all the IfStmt
		for(int i = activationIndex; i >= 0; i--){
			Unit unit = unitsOnPath.get(i);
			if(unit instanceof IfStmt){
				IfStmt ifStmt = (IfStmt) unit;
				boolean satisfied = false;
				Stmt target = ifStmt.getTarget();
				if(i + 1 < unitsOnPath.size()){
					Stmt nextStmt = (Stmt) unitsOnPath.get(i + 1);
					//warn: in most cases, using 'toString' to compare two stmt 
					//has no problem
					if(target.toString().equals(nextStmt.toString())){
						satisfied = true;
					}
				}
				Constraint constraint = new Constraint(ifStmt, satisfied, i, unitsOnPath);
			}
		}
	}
}
