package com.monster.taint.state;

import java.util.ArrayList;

/**
 * 
 * @author chenxiong
 *
 */
public class MethodState {
	private ArrayList<TaintValue> thisTVs = null;
	private ArrayList<ArrayList<TaintValue>> argsTVs = null;
	private ArrayList<TaintValue> staticTVs = null;
	//for method init state, retTVs should be empty
	private ArrayList<TaintValue> retTVs = null;
	
	public MethodState(int argsCount){
		this.thisTVs = new ArrayList<TaintValue>();
		this.argsTVs = new ArrayList<ArrayList<TaintValue>>(argsCount);
		for(int i = 0; i < argsCount; i++){
			this.argsTVs.add(new ArrayList<TaintValue>());
		}
		this.staticTVs = new ArrayList<TaintValue>();
		this.retTVs = new ArrayList<TaintValue>();
	}
	
	public ArrayList<TaintValue> getThisTVs(){
		return this.thisTVs;
	}
	
	public ArrayList<TaintValue> getArgTVs(int argIndex){
		return this.argsTVs.get(argIndex);
	}
	
	public ArrayList<ArrayList<TaintValue>> getAllArgsTVs(){
		return this.argsTVs;
	}
	
	public ArrayList<TaintValue> getStaticTVs(){
		return this.staticTVs;
	}
	
	public ArrayList<TaintValue> getRetTVs(){
		return this.retTVs;
	}
	
	public void setThisTVs(ArrayList<TaintValue> thisTVs){
		this.thisTVs = thisTVs;
	}
	
	public void setArgTVs(int index, ArrayList<TaintValue> argTVs){
		this.argsTVs.set(index, argTVs);
	}
	
	public void setStaticTVs(ArrayList<TaintValue> staticTVs){
		this.staticTVs = staticTVs;
	}
	
	public void addThisTV(TaintValue thisTV){
		if(!this.thisTVs.contains(thisTV)){
			this.thisTVs.add(thisTV);
		}
	}
	
	public void addArgTV(int argIndex, TaintValue argTV){
		ArrayList<TaintValue> argTVs = this.argsTVs.get(argIndex);
		if(!argTVs.contains(argTV)){
			argTVs.add(argTV);
		}
	}
	
	public void addStaticTV(TaintValue staticTV){
		if(!this.staticTVs.contains(staticTV)){
			this.staticTVs.add(staticTV);
		}
	}
	
	public void addThisTVContextSensitive(TaintValue thisTV){
		TaintValue exsitsTV = null;
		for(TaintValue tv : this.thisTVs){
			if(tv.equals(thisTV)){
				exsitsTV = tv;
				break;
			}
		}
		if(exsitsTV == null){
			this.thisTVs.add(thisTV);
		}else{
			exsitsTV.addContext(thisTV.getFirstContext());
		}
	}
	
	public void addArgTVContextSensitive(int argIndex, TaintValue argTV){
		ArrayList<TaintValue> argTVs = this.argsTVs.get(argIndex);
		TaintValue exsitsTV = null;
		for(TaintValue tv : argTVs){
			if(tv.equals(argTV)){
				exsitsTV = tv;
				break;
			}
		}
		if(exsitsTV == null){
			argTVs.add(argTV);
		}else{
			exsitsTV.addContext(argTV.getFirstContext());
		}
	}
	
	public void addStaticTVContextSensitive(TaintValue staticTV){
		TaintValue exsitsTV = null;
		for(TaintValue tv : this.staticTVs){
			if(tv.equals(staticTV)){
				exsitsTV = tv;
				break;
			}
		}
		if(exsitsTV == null){
			this.staticTVs.add(staticTV);
		}else{
			exsitsTV.addContext(staticTV.getFirstContext());
		}
	}
	
	public void addRetTVContextSensitive(TaintValue retTV){
		TaintValue exsitsTV = null;
		for(TaintValue tv : this.retTVs){
			if(tv.equals(retTV)){
				exsitsTV = tv;
				break;
			}
		}
		if(exsitsTV == null){
			this.retTVs.add(retTV);
		}else{
			exsitsTV.addContext(retTV.getFirstContext());
		}
	}
	
}
