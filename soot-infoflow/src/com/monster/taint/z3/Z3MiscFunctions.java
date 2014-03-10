package com.monster.taint.z3;

import java.util.HashMap;

import soot.Type;
import soot.Value;
import soot.jimple.Constant;
import soot.jimple.NullConstant;

/**
 * 
 * @author chenxiong
 *
 */
public class Z3MiscFunctions {
	private static Z3MiscFunctions instance = null;
	
	public static final String booleanStr = "boolean",
						 aBooleanStr = "boolean[]",
						 byteStr = "byte",
						 aByteStr = "byte[]",
						 shortStr = "short",
						 aShortStr = "short[]",
						 intStr = "int",
						 aIntStr = "int[]",
						 longStr = "long",
						 aLongStr = "long[]",
						 floatStr = "float",
						 aFloatStr = "float[]",
						 doubleStr = "double",
						 aDoubleStr = "double[]",
						 stringStr = "java.lang.String",
						 aStringStr = "java.lang.String[]";
	
	public static final String z3BoolStr = "Bool",
						z3BoolArrayStr = "Array Int Bool",
					    z3IntStr = "Int",
					    z3IntArrayStr = "Array Int Int",
					    z3RealStr = "Real",
					    z3RealArrayStr = "Array Int Real",
					    z3StringStr = "String",
					    z3StringArrayStr = "Array Int String";
					    
	
	enum Z3Type {
		Z3Boolean,
		Z3BooleanArray,
		Z3Int,
		Z3IntArray,
		Z3Real,
		Z3RealArray,
		Z3String,
		Z3StringArray,
		Z3Unknown
	}

	private final HashMap<String, Z3Type> strToZ3TypeMap = new HashMap<String, Z3Type>(){
		private static final long serialVersionUID = 1L;

		{
			put(booleanStr, Z3Type.Z3Boolean);
			put(aBooleanStr, Z3Type.Z3BooleanArray);
			put(byteStr, Z3Type.Z3Int);
			put(aByteStr, Z3Type.Z3IntArray);
			put(shortStr, Z3Type.Z3Int);
			put(aShortStr, Z3Type.Z3IntArray);
			put(intStr, Z3Type.Z3Int);
			put(aIntStr, Z3Type.Z3IntArray);
			put(longStr, Z3Type.Z3Int);
			put(aLongStr, Z3Type.Z3IntArray);
			put(floatStr, Z3Type.Z3Real);
			put(aFloatStr, Z3Type.Z3RealArray);
			put(doubleStr, Z3Type.Z3Real);
			put(aDoubleStr, Z3Type.Z3RealArray);
			put(stringStr, Z3Type.Z3String);
			put(aStringStr, Z3Type.Z3StringArray);
		}
	};
	
	public static final HashMap<Z3Type, String> z3TypeToStringMap = new HashMap<Z3Type, String>(){
		/**
		 * 
		 */
		private static final long serialVersionUID = 1L;

		{
			put(Z3Type.Z3Boolean, z3BoolStr);
			put(Z3Type.Z3BooleanArray, z3BoolArrayStr);
			put(Z3Type.Z3Int, z3IntStr);
			put(Z3Type.Z3IntArray, z3IntArrayStr);
			put(Z3Type.Z3Real, z3RealStr);
			put(Z3Type.Z3RealArray, z3RealArrayStr);
			put(Z3Type.Z3String, z3StringStr);
			put(Z3Type.Z3StringArray, z3StringArrayStr);
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
			z3Type = Z3Type.Z3Unknown;
		}
		return z3Type;
	}

	/**
	 * (declare-variable a Int)
	 * (declare-variable a Bool)
	 * (declare-variable a String)
	 * (declare-variable a Real)
	 * @param name
	 * @param z3Type
	 * @return
	 */
	public String getPrimeTypeDeclareStmt(String name, Z3Type z3Type){
		StringBuilder sb = new StringBuilder();
		sb.append("(declare-variable ");
		sb.append(name);
		sb.append(" ");
		sb.append(z3TypeToStringMap.get(z3Type));
		sb.append(")");
		return sb.toString();
	}

	/**
	 * (declare-variable a (Array Int String))
	 * @param name
	 * @param z3Type
	 * @return
	 */
	public String getArrayDeclareStmt(String name, Z3Type z3Type){
		StringBuilder sb = new StringBuilder();
		sb.append("(declare-variable ");
		sb.append(name);
		sb.append(" ");
		sb.append("(");
		sb.append(z3TypeToStringMap.get(z3Type));
		sb.append("))");
		return sb.toString();
	}

	/**
	 * (assert (= a 42))
	 * (assert (= a true))
	 * (assert (= a "415"))
	 * @param varName
	 * @param type
	 * @param constant
	 * @return
	 */
	public String getAssertLocalEqualConst(String varName, Z3Type type, Constant constant){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(varName);
		sb.append(" ");
		String conStr = null;
		switch(type){
			case Z3Boolean:
				conStr = constant.toString();
				assert(conStr.equals("true") || conStr.equals("false"));
				break;
			case Z3Int:
			case Z3Real:
				conStr = constant.toString();
				break;
			case Z3String:
				if(constant instanceof NullConstant){
					conStr = "\"\"";
				}else{
					conStr = constant.toString();
				}
				break;
		}
		assert(conStr != null);
		sb.append(conStr);
		sb.append("))");
		return sb.toString();
	}

	/**
	 * (assert (= r1 r2))
	 * @param varName1
	 * @param varName2
	 * @return
	 */
	public String getCommonAssertEqual(String varName1, String varName2){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(varName1);
		sb.append(" ");
		sb.append(varName2);
		sb.append("))");
		return sb.toString();
	}

	/**
	 * (assert (= localName (select aBaseName aIndex))) 
	 * @param localName
	 * @param aBaseName
	 * @param aIndex TODO: parse aIndex?
	 * @return
	 */
	public String getAssertLocalEqualArrayRef(String localName, String aBaseName, Value aIndex){
		StringBuilder sb = new StringBuilder();
		sb.append("(assert (= ");
		sb.append(localName);
		sb.append(" ");
		sb.append("(select ");
		sb.append(aBaseName);
		sb.append(" ");
		sb.append(aIndex.toString());
		sb.append(")))");
		return sb.toString();
	}

}
