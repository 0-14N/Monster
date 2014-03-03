package com.monster.taint.slice;

import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootMethod;
import soot.Unit;
import soot.ValueBox;

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
	
	public void slice(MethodPath methodPath){
		ArrayList<Unit> unitsOnPath = methodPath.getUnitsOnPath();
		SootMethod method = methodPath.getMethodHub().getMethod();
		List<ValueBox> defBoxes = method.getActiveBody().getDefBoxes();
		List<ValueBox> useBoxes = method.getActiveBody().getUseBoxes();
		for(Unit unit : unitsOnPath){
			List<ValueBox> tmpBoxes1 = unit.getDefBoxes();
			List<ValueBox> tmpBoxes2 = unit.getUseBoxes();
			logger.info("Break Point!");
		}
	}
}
