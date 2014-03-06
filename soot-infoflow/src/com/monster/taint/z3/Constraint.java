package com.monster.taint.z3;

import java.util.ArrayList;
import java.util.List;

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
	private IfStmt ifStmt = null;
	private int ifStmtIdx = -1;
	private boolean satisfied = false;
	private ArrayList<Unit> unitsOnPath = null;
	private ArrayList<Unit> relatedUnits = null;
	private int[] flagsArray = null;
	
	public Constraint(IfStmt ifStmt, boolean satisfied, int idx, 
			ArrayList<Unit> unitsOnPath){
		this.ifStmt = ifStmt;
		this.satisfied = satisfied;
		this.ifStmtIdx = idx;
		this.unitsOnPath = unitsOnPath;
		this.relatedUnits = new ArrayList<Unit>();
		this.flagsArray = new int[unitsOnPath.size()];
	}
	
	public void stepBackwrads(){
		ConditionExpr conditionExpr = (ConditionExpr) this.ifStmt.getCondition();
		Value v1 = conditionExpr.getOp1();
		Value v2 = conditionExpr.getOp2();
		
		if(!(v1 instanceof Constant)){
			propagationOf(v1, ifStmtIdx - 1);
		}
		
		if(!(v2 instanceof Constant)){
			propagationOf(v2, ifStmtIdx - 1);
		}
		
		for(int i = 0; i < flagsArray.length; i++){
			if(flagsArray[i] == 1){
				relatedUnits.add(unitsOnPath.get(i));
			}
		}
	}
	
	private void propagationOf(Value value, int startIndex){
		for(int i = startIndex; i >= 0; i--){
			Unit unit = this.unitsOnPath.get(i);
			List<ValueBox> defBoxes = unit.getDefBoxes();
			List<ValueBox> useBoxes = unit.getUseBoxes();
			if(containIn(defBoxes, value)){
				this.flagsArray[i] = 1;
				for(ValueBox useBox : useBoxes){
					Value  useValue = useBox.getValue();
					if(useValue instanceof Local){
						propagationOf(useValue, i - 1);
					}
				}
				break;
			}
		}
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
	
	public Element getConstraintElement(Document doc){
		Element constraintElement = doc.createElement("Constraint");
		constraintElement.setAttribute("IfStmt", this.ifStmt.toString());
		constraintElement.setAttribute("Condition", "" + this.satisfied);
		
		Element relatedUnitsElement = doc.createElement("RelatedUnits");
		relatedUnitsElement.setAttribute("size", "" + this.relatedUnits.size());
		for(int i = 0; i < this.relatedUnits.size(); i++){
			Element unitElement = doc.createElement("Stmt");
			unitElement.setAttribute("value", this.relatedUnits.get(i).toString());
			relatedUnitsElement.appendChild(unitElement);
		}
		
		constraintElement.appendChild(relatedUnitsElement);
		return constraintElement;
	}
}
