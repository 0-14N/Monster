package com.monster.taint.z3;

import java.util.HashMap;
import java.util.List;

import com.monster.taint.z3.stmts.atom.BinopExprType;
import com.monster.taint.z3.stmts.atom.ExprType;

import soot.Type;
import soot.Value;
import soot.JastAddJ.SubExpr;
import soot.jimple.AddExpr;
import soot.jimple.AndExpr;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.CmpExpr;
import soot.jimple.CmpgExpr;
import soot.jimple.CmplExpr;
import soot.jimple.Constant;
import soot.jimple.DivExpr;
import soot.jimple.EqExpr;
import soot.jimple.Expr;
import soot.jimple.GeExpr;
import soot.jimple.GtExpr;
import soot.jimple.InstanceOfExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.LeExpr;
import soot.jimple.LtExpr;
import soot.jimple.MulExpr;
import soot.jimple.NeExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.NullConstant;
import soot.jimple.OrExpr;
import soot.jimple.RemExpr;
import soot.jimple.ShlExpr;
import soot.jimple.ShrExpr;
import soot.jimple.UnopExpr;
import soot.jimple.UshrExpr;
import soot.jimple.XorExpr;

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

	/**
	 * (declare-fun funName (paramType1 paramType2 ...) retType)
	 * @param funName
	 * @param paramTypes
	 * @param retType
	 * @return
	 */
	public String getFuncDeclareStmt(String funName, List<Type> paramTypes, Type retType){
		StringBuilder sb = new StringBuilder();
		sb.append("(declare-fun ");
		sb.append(funName);
		sb.append(" ");
		sb.append("(");
		for(Type paramType : paramTypes){
			Z3Type z3Type = this.z3Type(paramType);
			if(z3Type != Z3Type.Z3Unknown){
				sb.append(z3TypeToStringMap.get(z3Type));
			}else{
				sb.append(z3TypeToStringMap.get(Z3Type.Z3String));
			}
			sb.append(" ");
		}
		sb.append(")");
		sb.append(" ");
		if(!retType.toString().equals("void")){
			Z3Type z3Type = this.z3Type(retType);
			if(z3Type != Z3Type.Z3Unknown){
				sb.append(z3TypeToStringMap.get(z3Type));
			}else{
				sb.append(z3TypeToStringMap.get(Z3Type.Z3String));
			}
		}
		sb.append(")");
		return sb.toString();
	}
	
	public ExprType getExprType(Expr expr){
		ExprType type = null;
		if(expr instanceof BinopExpr){
			type = ExprType.BINOP;
		}else if(expr instanceof CastExpr){
			type = ExprType.CAST;
		}else if(expr instanceof InstanceOfExpr){
			type = ExprType.INSTANCEOF;
		}else if(expr instanceof InvokeExpr){
			type = ExprType.INVOKE;
		}else if(expr instanceof NewArrayExpr){
			type = ExprType.NEWARRAY;
		}else if(expr instanceof NewExpr){
			type = ExprType.NEWEXPR;
		}else if(expr instanceof NewMultiArrayExpr){
			type = ExprType.NEWMULIARRAY;
		}else if(expr instanceof UnopExpr){
			type = ExprType.UNOP;
		}
		assert(type != null);
		return type;
	}
	
	public BinopExprType getBinopExprType(BinopExpr binopExpr){
		BinopExprType type = null;
		if(binopExpr instanceof AddExpr){
			type = BinopExprType.ADD;
		}else if(binopExpr instanceof AndExpr){
			type = BinopExprType.AND;
		}else if(binopExpr instanceof CmpExpr){
			type = BinopExprType.CMP;
		}else if(binopExpr instanceof CmpgExpr){
			type = BinopExprType.CMPG;
		}else if(binopExpr instanceof CmplExpr){
			type = BinopExprType.CMPL;
		}else if(binopExpr instanceof DivExpr){
			type = BinopExprType.DIV;
		}else if(binopExpr instanceof EqExpr){
			type = BinopExprType.EQ;
		}else if(binopExpr instanceof GeExpr){
			type = BinopExprType.GE;
		}else if(binopExpr instanceof GtExpr){
			type = BinopExprType.GT;
		}else if(binopExpr instanceof LeExpr){
			type = BinopExprType.LE;
		}else if(binopExpr instanceof LtExpr){
			type = BinopExprType.LT;
		}else if(binopExpr instanceof MulExpr){
			type = BinopExprType.MUL;
		}else if(binopExpr instanceof NeExpr){
			type = BinopExprType.NE;
		}else if(binopExpr instanceof OrExpr){
			type = BinopExprType.OR;
		}else if(binopExpr instanceof RemExpr){
			type = BinopExprType.REM;
		}else if(binopExpr instanceof ShlExpr){
			type = BinopExprType.SHL;
		}else if(binopExpr instanceof ShrExpr){
			type = BinopExprType.SHR;
		}else if(binopExpr instanceof SubExpr){
			type = BinopExprType.SUB;
		}else if(binopExpr instanceof UshrExpr){
			type = BinopExprType.USHR;
		}else if(binopExpr instanceof XorExpr){
			type = BinopExprType.XOR;
		}
		assert(type != null);
		return type;
	}

}
