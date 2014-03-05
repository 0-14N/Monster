package com.monster.taint.slice;

import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.Constant;
import soot.jimple.IdentityStmt;

public class IntentSourceSlice {
	private Logger logger = LoggerFactory.getLogger(getClass());
	
	private static IntentSourceSlice instance = null;
	
	private IntentSourceSlice(){}
	
	public static IntentSourceSlice v(){
		if(instance == null){
			instance = new IntentSourceSlice();
		}
		return instance;
	}

	/**
	 * forward slice from "$rn := @parametern: android.content.Intent"
	 * 
	 * @param iteSlicedPath
	 * @return
	 */
	public List<UnitWrapper> slice(List<UnitWrapper> iteSlicedPath){
		List<ValueBox> allDefBoxes = new ArrayList<ValueBox>(); 
		
		for(int i = 0; i < iteSlicedPath.size(); i++){
			UnitWrapper unitWrapper = iteSlicedPath.get(i);
			Unit unit =  unitWrapper.getUnit();
			
			//first, find the "start" stmt
			if(unit instanceof IdentityStmt){
				IdentityStmt identityStmt = (IdentityStmt) unit;
				Value rv = identityStmt.getRightOp();
				if(rv.getType().toString().equals("android.content.Intent")){
					allDefBoxes.addAll(unit.getDefBoxes());
					unitWrapper.addToIntentSourceSlice();
				}
				continue;
			}
			
			List<ValueBox> defBoxes = unitWrapper.getDefBoxes();
			List<ValueBox> useBoxes = unitWrapper.getUseBoxes();
			//if there is any usebox contained in 'allDefBoxes', add the 'defBoxes' 
			//to 'allDefBoxes'
			if(isAnyContainedIn(useBoxes, allDefBoxes)){
				unitWrapper.addToIntentSourceSlice();
				//if there is any usebox not contained in 'allDefBoxes',
				//start backwards slice to get their defboxes
				List<ValueBox> notContainedBoxes = getNotContainedIn(useBoxes, allDefBoxes);
				if(notContainedBoxes.size() > 0){
					for(ValueBox notContainedBox : notContainedBoxes){
						startBackwardsSlice(iteSlicedPath, i - 1, notContainedBox, allDefBoxes);
						allDefBoxes.add(notContainedBox);
					}
				}
				allDefBoxes.addAll(defBoxes);
			}
		}
		
		List<UnitWrapper> intentSourceSlice = new ArrayList<UnitWrapper>();
		for(UnitWrapper wrapper : iteSlicedPath){
			if(wrapper.isInIntentSourceSlice()){
				intentSourceSlice.add(wrapper);
			}
		}
		return intentSourceSlice;
	}
	
	private void startBackwardsSlice(List<UnitWrapper> allWrappers, int startIndex, ValueBox box,
			List<ValueBox> allDefBoxes){
		//box is a constant
		if(box.getValue() instanceof Constant){
			return;
		}
		
		int currIndex = startIndex;
		while(currIndex >= 0){
			UnitWrapper wrapper = allWrappers.get(currIndex);
			List<ValueBox> defBoxes = wrapper.getDefBoxes();
			if(containIn(defBoxes, box)){
				wrapper.addToIntentSourceSlice();
				List<ValueBox> useBoxes = wrapper.getUseBoxes();
				List<ValueBox> notContainedBoxes = getNotContainedIn(useBoxes, allDefBoxes);
				if(notContainedBoxes.size() > 0){
					for(ValueBox vb : notContainedBoxes){
						startBackwardsSlice(allWrappers, currIndex - 1, vb, allDefBoxes);
					}
				}
				allDefBoxes.add(box);
			}
			currIndex--;
		}
	}
	
	private boolean isAnyContainedIn(List<ValueBox> useBoxes, List<ValueBox> allDefBoxes){
		boolean contained = false;
		
		for(ValueBox useBox : useBoxes){
			if(containIn(allDefBoxes, useBox)){
				contained = true;
				break;
			}
		}
		
		return contained;
	}
	
	private List<ValueBox> getNotContainedIn(List<ValueBox> useBoxes, List<ValueBox> allDefBoxes){
		List<ValueBox> result = new ArrayList<ValueBox>();
		
		for(ValueBox useBox : useBoxes){
			if(!containIn(allDefBoxes, useBox)){
				result.add(useBox);
			}
		}
		
		return result;
	}
	
	private boolean containIn(List<ValueBox> boxesList, ValueBox box){
		boolean contained = false;
		
		for(ValueBox valueBox : boxesList){
			if(valueBox.getValue().toString().equals(box.getValue().toString()) &&
					valueBox.getValue().getType().toString().equals(box.getValue().getType().toString())){
				contained = true;
				break;
			}
		}
		
		return contained;
	}
}
