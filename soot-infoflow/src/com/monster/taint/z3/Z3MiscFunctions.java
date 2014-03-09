package com.monster.taint.z3;

import java.util.HashMap;

import soot.Type;

/**
 * 
 * @author chenxiong
 *
 */
public class Z3MiscFunctions {
	private static Z3MiscFunctions instance = null;
	
	public static final String booleanStr = "boolean",
						 byteStr = "byte",
						 shortStr = "short",
						 intStr = "int",
						 longStr = "long",
						 floatStr = "float",
						 doubleStr = "double",
						 stringStr = "java.lang.String";
	
	public static final String z3BoolStr = "Bool",
					    z3IntStr = "Int",
					    z3RealStr = "Real",
					    z3StringStr = "String";
					    
	
	enum Z3Type {
		Z3Boolean,
		Z3Int,
		Z3Real,
		Z3String,
		Z3Unkonwn
	}

	//should I ignore this warning?
	private final HashMap<String, Z3Type> strToZ3TypeMap = new HashMap<String, Z3Type>(){
		/**
		 * 
		 */
		private static final long serialVersionUID = 1L;

		{
			put(booleanStr, Z3Type.Z3Boolean);
			put(byteStr, Z3Type.Z3Int);
			put(shortStr, Z3Type.Z3Int);
			put(intStr, Z3Type.Z3Int);
			put(longStr, Z3Type.Z3Int);
			put(floatStr, Z3Type.Z3Real);
			put(doubleStr, Z3Type.Z3Real);
			put(stringStr, Z3Type.Z3String);
		}
	};
	
	public static final HashMap<Z3Type, String> z3TypeToStringMap = new HashMap<Z3Type, String>(){
		/**
		 * 
		 */
		private static final long serialVersionUID = 1L;

		{
			put(Z3Type.Z3Boolean, z3BoolStr);
			put(Z3Type.Z3Int, z3IntStr);
			put(Z3Type.Z3Real, z3RealStr);
			put(Z3Type.Z3String, z3StringStr);
		}
	};
	
	private Z3MiscFunctions(){}
	
	public static Z3MiscFunctions v(){
		if(instance == null){
			instance = new Z3MiscFunctions();
		}
		return instance;
	}
	
	public Z3Type z3Type(Type type){
		String typeStr = type.toString();
		Z3Type z3Type = strToZ3TypeMap.get(typeStr);
		if(z3Type == null){
			z3Type = Z3Type.Z3Unkonwn;
		}
		return z3Type;
	}
	
	public String getDeclareStmt(String name, Z3Type z3Type){
		StringBuilder sb = new StringBuilder();
		sb.append("(declare-variable ");
		sb.append(name);
		sb.append(" ");
		sb.append(z3TypeToStringMap.get(z3Type));
		sb.append(")");
		return sb.toString();
	}

}
