package com.monster.taint.slice;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class SourceTaintSlice {
	private Logger logger = LoggerFactory.getLogger(getClass());
	
	private static SourceTaintSlice instance = null;
	
	private SourceTaintSlice(){}
	
	public static SourceTaintSlice v(){
		if(instance == null){
			instance = new SourceTaintSlice();
		}
		return instance;
	}
}
