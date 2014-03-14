package com.monster.taint.z3;

import java.util.List;

import soot.Local;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.StaticFieldRef;

/**
 * Miscellaneous functions to help handle
 * the redefined variables.
 * 
 * @author chenxiong
 *
 */
public class SSAMiscFunctions {
	private static SSAMiscFunctions instance = null;
	
	private SSAMiscFunctions(){}
	
	public static SSAMiscFunctions v(){
		if(instance == null){
			instance = new SSAMiscFunctions();
		}
		return instance;
	}
	
	public boolean arrayRefRedefined(ArrayRef lARef, List<ValueBox> rUseBoxes){
		for(ValueBox rUseBox : rUseBoxes){
			Value rBoxValue = rUseBox.getValue();
			if(rBoxValue instanceof ArrayRef){
				ArrayRef rARef = (ArrayRef) rBoxValue;
				if(twoValueEquals(lARef.getBase(), rARef.getBase()) &&
						twoValueEquals(lARef.getIndex(), rARef.getIndex())){
					return true;
				}
			}
		}
		return false;
	}
	
	public boolean instanceFieldRefRedefined(InstanceFieldRef lIFieldRef, List<ValueBox> rUseBoxes){
		for(ValueBox rUseBox : rUseBoxes){
			Value rBoxValue = rUseBox.getValue();
			if(rBoxValue instanceof InstanceFieldRef){
				InstanceFieldRef rIFieldRef = (InstanceFieldRef) rBoxValue;
				if(twoValueEquals(lIFieldRef.getBase(), rIFieldRef.getBase()) &&
						lIFieldRef.getField().equals(rIFieldRef.getField())){
					return true;
				}
			}
		}
		return false;
	}
	
	public boolean staticFieldRefRedefined(StaticFieldRef lSFieldRef, List<ValueBox> rUseBoxes){
		for(ValueBox rUseBox : rUseBoxes){
			Value rBoxValue = rUseBox.getValue();
			if(rBoxValue instanceof StaticFieldRef){
				StaticFieldRef rSFieldRef = (StaticFieldRef) rBoxValue;
				if(lSFieldRef.getField().equals(rSFieldRef.getField())){
					return true;
				}
			}
		}
		return false;
	}
	
	public boolean localRedefined(Local lLocal, List<ValueBox> rUseBoxes){
		for(ValueBox rUseBox : rUseBoxes){
			Value rBoxValue = rUseBox.getValue();
			if(rBoxValue instanceof Local){
				Local rLocal = (Local) rBoxValue;
				if(lLocal.getName().equals(rLocal.getName()) &&
						lLocal.getType().toString().equals(rLocal.getType().toString())){
					return true;
				}
			}
		}
		return false;
	}
	
	
	public boolean twoValueEquals(Value v1, Value v2){
		if(v1.toString().equals(v2.toString()) &&
				v1.getType().toString().equals(v2.getType().toString())){
			return true;
		}
		return false;
	}
	
	public int getDefineTimes(List<Integer> defineLineNumbers, int index){
		int i = 0;
		for(Integer integer : defineLineNumbers){
			if(index >= integer.intValue()){
				i++;
			}
		}
		return i;
	}
}
