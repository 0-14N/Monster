package com.monster.taint.state;

/**
 * Q: What is the difference between type TAINT and ALIAS?
 * A: An alias is something can be used to taint others, but itself is 
 * 	  never tainted.
 * @author chenxiong
 *
 */
public enum TaintValueType {
	TAINT,
	ALIAS, //if a taint value's type is ALIAS, its dependence's may be alias, but its ultimate dependence's type
			//must be TAINT
	STATIC_FIELD,
}
