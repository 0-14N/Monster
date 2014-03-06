package com.monster.taint.slice;

import java.util.ArrayList;
import java.util.List;

import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ConditionExpr;
import soot.jimple.IfStmt;

/**
 * this class is a wrapper of stmt,
 * contains unit index of certain path,
 * defboxes, useboxes
 * 
 * @author chenxiong
 *
 */
public class UnitWrapper {
	private Unit unit = null;
	private int idx = -1;
	private List<ValueBox> defBoxes = null;
	private List<ValueBox> useBoxes = null;
	private boolean isIfStmt = false;
	//indicate whether this unit is in ITE slice
	private boolean inITESlice = false;
	//indicate whether this unit is in Intent Source slice
	private boolean inIntentSource = false;
	
	public UnitWrapper(Unit unit, int idx){
		this.unit = unit;
		this.idx = idx;
		this.defBoxes = unit.getDefBoxes();
		this.useBoxes = unit.getUseBoxes();
		if(unit instanceof IfStmt){
			this.isIfStmt = true;
			this.inITESlice = true;
		}
	}
	
	public boolean isIfStmt(){
		return this.isIfStmt;
	}
	
	public boolean isInITESlice(){
		return this.inITESlice;
	}
	
	public boolean isInIntentSourceSlice(){
		return this.inIntentSource;
	}
	
	public void addToIntentSourceSlice(){
		this.inIntentSource = true;
	}
	
	public List<ValueBox> getDefBoxes(){
		return this.defBoxes;
	}
	
	public List<ValueBox> getUseBoxes(){
		return this.useBoxes;
	}
	
	public Unit getUnit(){
		return this.unit;
	}
	
	public List<Value> getITEUsesOfDefs(List<Value> defValues){
		List<Value> useValues = new ArrayList<Value>();
		
		for(Value value : defValues){
			if(isValueInDefBoxes(value) != null){
				this.inITESlice = true;
				break;
			}
		}
		if(this.inITESlice){
			for(ValueBox vb : this.useBoxes){
				useValues.add(vb.getValue());
			}
		}
		return useValues;
	}
	
	public List<Value> getITEUsesOfDefs(Value defValue){
		List<Value> useValues = new ArrayList<Value>();
		
		if(isValueInDefBoxes(defValue) != null){
			this.inITESlice = true;
			for(ValueBox vb : this.useBoxes){
				useValues.add(vb.getValue());
			}
		}
		return useValues;
	}
	
	private ValueBox isValueInDefBoxes(Value value){
		ValueBox valueBox = null;
		for(ValueBox vb : this.defBoxes){
			Value v = vb.getValue();
			if(v.toString().equals(value.toString()) &&
					v.getType().toString().equals(value.getType().toString())){
				valueBox = vb;
				break;
			}
		}
		return valueBox;
	}
}
