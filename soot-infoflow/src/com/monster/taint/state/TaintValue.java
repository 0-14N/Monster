package com.monster.taint.state;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import com.monster.taint.path.MethodPath;

import soot.SootField;
import soot.Unit;
import soot.Value;

public class TaintValue {
	private TaintValueType type = null;
	//for static field, base is null, otherwise, not null
	private Value base = null;
	private ArrayList<SootField> accessPath = null;
	private Unit activationUnit = null;
	//dependence is the TaintValue this depend on
	private TaintValue dependence = null;
	//the TaintValues depend on this
	private Set<TaintValue> slaves = null;
	//on which path, this TaintValue activated
	private MethodPath context = null;
	
	public TaintValue(TaintValueType type, Value base, Unit activationUnit, 
			MethodPath context){
		this.type = type;
		this.base = base;
		this.accessPath = new ArrayList<SootField>();
		this.activationUnit = activationUnit;
		this.slaves = new HashSet<TaintValue>();
		this.context = context;
	}
	
	public void setDependence(TaintValue dependence){
		this.dependence = dependence;
	}
	
	public TaintValue getDependence(){
		return this.dependence;
	}
	
	public TaintValue getUltimateDependence(){
		TaintValue ultimateDependence = this;
		while(ultimateDependence.getDependence() != null){
			ultimateDependence = ultimateDependence.getDependence();
		}
		return ultimateDependence;
	}
	
	public boolean addSlave(TaintValue slave){
		boolean exists = false;
		for(TaintValue tv : this.slaves){
			if(tv.equals(slave)){
				exists = true;
				break;
			}
		}
		if(!exists){
			this.slaves.add(slave);
		}
		return exists;
	}
	
	public void appendSootField(SootField sootField){
		this.accessPath.add(sootField);
	}
	
	public void appendAllSootField(ArrayList<SootField> sootFields){
		this.accessPath.addAll(sootFields);
	}
	
	public TaintValueType getType(){
		return this.type;
	}
	
	public SootField getFirstField(){
		if(accessPath.size() == 0)
			return null;
		else
			return this.accessPath.get(0);
	}
	
	public Value getBase(){
		return this.base;
	}
	
	public Set<TaintValue> getSlaves(){
		return this.slaves;
	}
	
	public ArrayList<SootField> getAccessPath(){
		return this.accessPath;
	}
	
	public Unit getActivationUnit(){
		return this.activationUnit;
	}

	/**
	 * this comparison method can only be used in
	 * the same method comparison
	 */
	@Override
	public boolean equals(Object obj) {
		if (super.equals(obj))
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		TaintValue other = (TaintValue) obj;
		if(other.getType() != this.type)
			return false;
		
		//not static field
		if(this.type != TaintValueType.STATIC_FIELD){
			//base
			if(!this.base.equals(other.getBase()))
				return false;
		}
		//accessPath
		if(this.accessPath.size() != other.getAccessPath().size())
			return false;
		ArrayList<SootField> otherAccessPath = other.getAccessPath();
		for(int i = 0; i < this.accessPath.size(); i++){
			if(!this.accessPath.get(i).equals(otherAccessPath.get(i)))
				return false;
		}
		//activation unit
		if(!this.activationUnit.equals(other.getActivationUnit())){
			return false;
		}
		
		return true;
	}
	
}
