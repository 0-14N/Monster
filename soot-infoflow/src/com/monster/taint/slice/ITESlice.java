package com.monster.taint.slice;

import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ConditionExpr;
import soot.jimple.IfStmt;

import com.monster.taint.path.MethodPath;

/**
 * slice for "if ... then ... else"
 * 
 * @author chenxiong
 *
 */
public class ITESlice {
	private Logger logger = LoggerFactory.getLogger(getClass());
	private static ITESlice instance = null;
	
	private ITESlice(){}
	
	public static ITESlice v(){
		if(instance == null){
			instance = new ITESlice();
		}
		return instance;
	}
	
	public List<UnitWrapper> slice(MethodPath methodPath){
		ArrayList<Unit> unitsOnPath = methodPath.getUnitsOnPath();
		ArrayList<UnitWrapper> unitWrappers = new ArrayList<UnitWrapper>();
		
		for(int i = 0; i < unitsOnPath.size(); i++){
			Unit unit = unitsOnPath.get(i);
			UnitWrapper wrapper = new UnitWrapper(unit, i);
			unitWrappers.add(wrapper);
			if(wrapper.isIfStmt()){
				backwardsFromIfStmt(i-1, unitWrappers, (IfStmt) unit);
			}
		}
		
		ArrayList<UnitWrapper> slicedWrappers = new ArrayList<UnitWrapper>();
		for(UnitWrapper unitWrapper : unitWrappers){
			if(unitWrapper.isInITESlice()){
				slicedWrappers.add(unitWrapper);
			}
		}
		
		return slicedWrappers;
	}
	
	private void backwardsFromIfStmt(int startIndex, ArrayList<UnitWrapper> unitWrappers, IfStmt ifStmt){
		ConditionExpr conditionExpr = (ConditionExpr) ifStmt.getCondition();
		Value lv = conditionExpr.getOp1();
		Value rv = conditionExpr.getOp2();
		
		backwardsFromStmt(startIndex, unitWrappers, lv);
		backwardsFromStmt(startIndex, unitWrappers, rv);
	}

	/**
	 * 
	 * @param startIndex
	 * @param unitWrappers
	 * @param defValue
	 */
	private void backwardsFromStmt(int startIndex, ArrayList<UnitWrapper> unitWrappers, Value defValue){
		for(int i = startIndex; i >= 0; i--){
			UnitWrapper wrapper = unitWrappers.get(i);
			List<Value> useValues = wrapper.getITEUsesOfDefs(defValue);
			for(Value useValue : useValues){
				this.backwardsFromStmt(i-1, unitWrappers, useValue);
			}
			if(useValues.size() > 0){
				break;
			}
		}
	}
}
