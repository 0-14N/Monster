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
	private boolean inSlice = false;
	
	public UnitWrapper(Unit unit, int idx){
		this.unit = unit;
		this.idx = idx;
		this.defBoxes = unit.getDefBoxes();
		this.useBoxes = unit.getUseBoxes();
		if(unit instanceof IfStmt){
			this.isIfStmt = true;
			this.inSlice = true;
		}
	}
	
	public boolean isIfStmt(){
		return this.isIfStmt;
	}
	
	public boolean isInSlice(){
		return this.inSlice;
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
	
	public List<Value> getUsesOfDefs(List<Value> defValues){
		List<Value> useValues = new ArrayList<Value>();
		
		if(this.inSlice){
			return useValues;
		}
		
		for(Value value : defValues){
			if(isValueInDefBoxes(value) != null){
				this.inSlice = true;
				break;
			}
		}
		if(this.inSlice){
			for(ValueBox vb : this.useBoxes){
				useValues.add(vb.getValue());
			}
		}
		return useValues;
	}
	
	public List<Value> getUsesOfDefs(Value defValue){
		List<Value> useValues = new ArrayList<Value>();
		
		if(this.inSlice){
			return useValues;
		}
		
		if(isValueInDefBoxes(defValue) != null){
			this.inSlice = true;
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
