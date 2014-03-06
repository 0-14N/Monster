package com.monster.taint.z3;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import soot.Local;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ConditionExpr;
import soot.jimple.Constant;
import soot.jimple.IfStmt;

public class Constraint {
	IfStmt ifStmt = null;
	int ifStmtIdx = -1;
	boolean satisfied = false;
	ArrayList<Unit> unitsOnPath = null;
	Set<Unit> relatedUnits = null;
	
	public Constraint(IfStmt ifStmt, boolean satisfied, int idx, 
			ArrayList<Unit> unitsOnPath){
		this.ifStmt = ifStmt;
		this.satisfied = satisfied;
		this.ifStmtIdx = idx;
		this.unitsOnPath = unitsOnPath;
		this.relatedUnits = new HashSet<Unit>();
	}
	
	public void stepBackwrads(){
		ConditionExpr conditionExpr = (ConditionExpr) this.ifStmt.getCondition();
		Value v1 = conditionExpr.getOp1();
		Value v2 = conditionExpr.getOp2();
		
		if(!(v1 instanceof Constant)){
			relatedUnits.addAll(propagationOf(v1, ifStmtIdx - 1));
		}
		
		if(!(v2 instanceof Constant)){
			relatedUnits.addAll(propagationOf(v2, ifStmtIdx - 1));
		}
	}
	
	private Set<Unit> propagationOf(Value value, int startIndex){
		Set<Unit> unitSet = new HashSet<Unit>();
		for(int i = startIndex; i >= 0; i--){
			Unit unit = this.unitsOnPath.get(i);
			List<ValueBox> defBoxes = unit.getDefBoxes();
			List<ValueBox> useBoxes = unit.getUseBoxes();
			if(containIn(defBoxes, value)){
				unitSet.add(unit);
				for(ValueBox useBox : useBoxes){
					Value  useValue = useBox.getValue();
					if(useValue instanceof Local){
						unitSet.addAll(propagationOf(useValue, i - 1));
					}
				}
				break;
			}
		}
		return unitSet;
	}
	
	private boolean containIn(List<ValueBox> valueBoxes, Value value){
		boolean contain = false;
		for(ValueBox box : valueBoxes){
			Value v = box.getValue();
			if(v.toString().equals(value.toString()) &&
					v.getType().toString().equals(value.getType().toString())){
				contain = true;
				break;
			}
		}
		return contain;
	}
	
	public Element getElement(Document doc){
		return null;
	}
}
