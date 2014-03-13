package com.monster.taint.z3.stmts.atom;

import java.util.ArrayList;
import java.util.HashMap;

import soot.SootMethodRef;
import soot.Value;
import soot.jimple.InvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.VirtualInvokeExpr;

import com.monster.taint.z3.SMT2FileGenerator;

/**
 * I found Java sucks because of loss of "function pointers", though we can
 * use Interface to replace FPs, I hate class/interface explosion. 
 * 
 * To avoid class/interface explosion, the only way can make it is use "Table Driven"
 * with "Switch/Enum". 
 * 
 * @author chenxiong
 *
 */
public class StringModeling {
	/**
	 * The methods modeled:
	 * 1. String concat(String string)  -- Concat
	 * 	  <java.lang.String: java.lang.String concat(java.lang.String)> 
	 * 2. boolean contains(CharSequence cs)  -- Contains
	 *    <java.lang.String: boolean contains(java.lang.CharSequence)>
	 * 3. boolean contentEquals(CharSequence cs) -- =
	 * 	  <java.lang.String: boolean contentEquals(java.lang.CharSequence)>
	 * 4. boolean contentEquals(StringBuffer strbuf) -- =
	 * 	  <java.lang.String: boolean contentEquals(java.lang.StringBuffer)>
	 * 5. boolean endsWith(String suffix) -- EndsWith
	 * 	  <java.lang.String: boolean endsWith(java.lang.String)>
	 * 6. boolean equals(Object object) -- =
	 * 	  <java.lang.String: boolean equals(java.lang.Object)>
	 * 7. boolean equalsIgnoreCase(String string) -- =
	 * 	  <java.lang.String: boolean equalsIgnoreCase(java.lang.String)>
	 * 8. int indexOf(String subString, int start) -- IndexOf
	 *    <java.lang.String: int indexOf(java.lang.String,int)>
	 * 9. int indexOf(String string) -- IndexOf
	 *    <java.lang.String: int indexOf(java.lang.String)>
	 * 10. String intern() -- =
	 *    <java.lang.String: java.lang.String intern()>
	 * 11. boolean isEmpty() -- =
	 * 	  <java.lang.String: boolean isEmpty()>
	 * 12. int lastIndexOf(String string) -- IndexOf
	 *    <java.lang.String: int lastIndexOf(java.lang.String)>
	 * 13. int lastIndexOf(String subString, int start) -- IndexOf
	 *    <java.lang.String: int lastIndexOf(java.lang.String,int)>
	 * 14. int length() -- Length
	 *    <java.lang.String: int length()>
	 * 15. String replace(CharSequence target, CharSequence replacement) -- Replace
	 *    <java.lang.String: java.lang.String replace(java.lang.CharSequence,java.lang.CharSequence)>
	 * 16. boolean startsWith(String prefix) -- StartsWith
	 *    <java.lang.String: boolean startsWith(java.lang.String)>
	 * 17. boolean startsWith(String prefix, int start) -- StartsWith
	 *    <java.lang.String: boolean startsWith(java.lang.String,int)>
	 * 18. CharSequence	subSequence(int start, int end) --SubString
	 *    <java.lang.String: java.lang.CharSequence subSequence(int,int)>
	 * 19. String substring(int start) -- SubString
	 *    <java.lang.String: java.lang.String substring(int)>
	 * 20. String substring(int start, int end) -- SubString
	 *    <java.lang.String: java.lang.String substring(int,int)>
	 * 21. String toString() -- =
	 *    <java.lang.String: java.lang.String toString()>
	 * 22. static String valueOf(Object value) -- =
	 *    <java.lang.String: java.lang.String valueOf(java.lang.Object)>
	 */
	
	private enum StringMethodEnum{
		Concat, Contains, ContentEquals, ContentEquals2, EndsWith,
		Equals, EqualsIgnore, IndexOf, IndexOf2, Intern,
		IsEmpty, LastIndexOf, LastIndexOf2, Length, Replace,
		StartsWith, StartsWith2, SubSequence, SubString, SubString2,
		ToString, ValueOf
	}
	
	public static ArrayList<String> stringMethods = new ArrayList<String>(){
		/**
		 * 
		 */
		private static final long serialVersionUID = 1L;

		{
			add("<java.lang.String: java.lang.String concat(java.lang.String)>");
			add("<java.lang.String: boolean contains(java.lang.CharSequence)>");
			add("<java.lang.String: boolean contentEquals(java.lang.CharSequence)>");
			add("<java.lang.String: boolean contentEquals(java.lang.StringBuffer)>");
			add("<java.lang.String: boolean endsWith(java.lang.String)>");
			
			add("<java.lang.String: boolean equals(java.lang.Object)>");
			add("<java.lang.String: boolean equalsIgnoreCase(java.lang.String)>");
			add("<java.lang.String: int indexOf(java.lang.String,int)>");
			add("<java.lang.String: int indexOf(java.lang.String)>");
			add("<java.lang.String: java.lang.String intern()>");
			
			add("<java.lang.String: boolean isEmpty()>");
			add("<java.lang.String: int lastIndexOf(java.lang.String)>");
			add("<java.lang.String: int lastIndexOf(java.lang.String,int)>");
			add("<java.lang.String: int length()>");
			add("<java.lang.String: java.lang.String replace(java.lang.CharSequence,java.lang.CharSequence)>");
			
			add("<java.lang.String: boolean startsWith(java.lang.String)>");
			add("<java.lang.String: boolean startsWith(java.lang.String,int)>");
			add("<java.lang.String: java.lang.CharSequence subSequence(int,int)>");
			add("<java.lang.String: java.lang.String substring(int)>");
			add("<java.lang.String: java.lang.String substring(int,int)>");
			
			add("<java.lang.String: java.lang.String toString()>");
			add("<java.lang.String: java.lang.String valueOf(java.lang.Object)>");
		}
	};
	
	private static HashMap<String, StringMethodEnum> stringMethodsEnumMap = new HashMap<String, StringMethodEnum>(){
		/**
		 * 
		 */
		private static final long serialVersionUID = 1L;

		{
			put(stringMethods.get(0), StringMethodEnum.Concat);
			put(stringMethods.get(1), StringMethodEnum.Contains);
			put(stringMethods.get(2), StringMethodEnum.ContentEquals);
			put(stringMethods.get(3), StringMethodEnum.ContentEquals2);
			put(stringMethods.get(4), StringMethodEnum.EndsWith);
			
			put(stringMethods.get(5), StringMethodEnum.Equals);
			put(stringMethods.get(6), StringMethodEnum.EqualsIgnore);
			put(stringMethods.get(7), StringMethodEnum.IndexOf);
			put(stringMethods.get(8), StringMethodEnum.IndexOf2);
			put(stringMethods.get(9), StringMethodEnum.Intern);
			
			put(stringMethods.get(10), StringMethodEnum.IsEmpty);
			put(stringMethods.get(11), StringMethodEnum.LastIndexOf);
			put(stringMethods.get(12), StringMethodEnum.LastIndexOf2);
			put(stringMethods.get(13), StringMethodEnum.Length);
			put(stringMethods.get(14), StringMethodEnum.Replace);
			
			put(stringMethods.get(15), StringMethodEnum.StartsWith);
			put(stringMethods.get(16), StringMethodEnum.StartsWith2);
			put(stringMethods.get(17), StringMethodEnum.SubSequence);
			put(stringMethods.get(18), StringMethodEnum.SubString);
			put(stringMethods.get(19), StringMethodEnum.SubString2);
			
			put(stringMethods.get(20), StringMethodEnum.ToString);
			put(stringMethods.get(21), StringMethodEnum.ValueOf);
		}
	};
	
	public static String modelMethod(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		SootMethodRef methodRef = invokeExpr.getMethodRef();
		switch(stringMethodsEnumMap.get(methodRef.getSignature())){
		case Concat:
			return mConcat(invokeExpr, fileGenerator, stmtIdx);
		case Contains:
			return mContains(invokeExpr, fileGenerator, stmtIdx);
		case ContentEquals:
			return mContentEquals(invokeExpr, fileGenerator, stmtIdx);
		case ContentEquals2:
			return mContentEquals(invokeExpr, fileGenerator, stmtIdx);
		case EndsWith:
			return mEndsWith(invokeExpr, fileGenerator, stmtIdx);
		case Equals:
			return mEquals(invokeExpr, fileGenerator, stmtIdx);
		case EqualsIgnore:
			return mEqualsIgnore(invokeExpr, fileGenerator, stmtIdx);
		case IndexOf:
			return mIndexOf(invokeExpr, fileGenerator, stmtIdx);
		case IndexOf2:
			return mIndexOf(invokeExpr, fileGenerator, stmtIdx);
		case Intern:
			return mIntern(invokeExpr, fileGenerator, stmtIdx);
		case IsEmpty:
			return mIsEmpty(invokeExpr, fileGenerator, stmtIdx);
		case LastIndexOf:
			return mLastIndexOf(invokeExpr, fileGenerator, stmtIdx);
		case LastIndexOf2:
			return mLastIndexOf(invokeExpr, fileGenerator, stmtIdx);
		case Length:
			return mLength(invokeExpr, fileGenerator, stmtIdx);
		case Replace:
			return mReplace(invokeExpr, fileGenerator, stmtIdx);
		case StartsWith:
			return mStartsWith(invokeExpr, fileGenerator, stmtIdx);
		case StartsWith2:
			return mStartsWith(invokeExpr, fileGenerator, stmtIdx);
		case SubSequence:
			return mSubSequence(invokeExpr, fileGenerator, stmtIdx);
		case SubString:
			return mSubString(invokeExpr, fileGenerator, stmtIdx);
		case SubString2:
			return mSubString2(invokeExpr, fileGenerator, stmtIdx);
		case ToString:
			return mToString(invokeExpr, fileGenerator, stmtIdx);
		case ValueOf:
			return mValueOf(invokeExpr, fileGenerator, stmtIdx);
			default:
				assert(false);
				return null;
		}
	}

	private static VirtualInvokeExpr convertToVirtualInvokeExpr(InvokeExpr invokeExpr){
		assert(invokeExpr instanceof VirtualInvokeExpr);
		return (VirtualInvokeExpr) invokeExpr;
	}
	
	/**
	 * a = b.concat(c)
	 * (assert (= a (Concat b c)))
	 * 
	 * @param invokeExpr
	 * @param stmtIdx 
	 * @param fileGenerator
	 * @return
	 */
	private static String mConcat(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(Concat ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.contains(c)
	 * (assert (= a (Contains b c)))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mContains(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(Contains ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.contentEquals(c)
	 * (assert (= a (= b c)))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mContentEquals(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(= ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.endsWith(c)
	 * (assert (= a (EndsWith b c)))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mEndsWith(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(EndsWith ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.equals(c)
	 * (assert (= a (= b c))) 
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mEquals(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(= ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.equalsIgnore(c)
	 * (assert (= a (= b c))) 
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mEqualsIgnore(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(= ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.indexof(c)
	 * a = b.indexof(c, 42)
	 * (assert (= a (Indexof b c)))
	 * 
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mIndexOf(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(Indexof ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.intern()
	 * (assert (= a b))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mIntern(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append(thisBaseName);
		return sb.toString();
	}

	/**
	 * a = b.isEmpty()
	 * (assert (= a (= b "")))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mIsEmpty(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(= ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append("\"\"");
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.lastIndexOf(c)
	 * a = b.lastIndexOf(c, 42)
	 * (assert (= a (Indexof b c)))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mLastIndexOf(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(Indexof ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.length()
	 * (assert (= a (Length b)))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mLength(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(Length ");
		sb.append(thisBaseName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.replace(c , d)
	 * (assert (= a (Replace b c d)))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mReplace(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		Value secondParam = vInvokeExpr.getArg(1);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		String secondParamName = fileGenerator.getRenameOf(secondParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(Replace ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(" ");
		sb.append(secondParamName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.startsWith(c)
	 * a = b.startsWith(c, 42)
	 * (assert (= a (StartsWith b c)))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mStartsWith(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(StartsWith ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.subSequence(int start, int end)
	 * (assert (= a (Substring b start (- end 1)))) 
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mSubSequence(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		Value secondParam = vInvokeExpr.getArg(1);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		String secondParamName = fileGenerator.getRenameOf(secondParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(Substring ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(" ");
		sb.append("(- ");
		sb.append(secondParamName);
		sb.append(" 1)");
		sb.append(")");
		return sb.toString();
	}

	/**
	 * substring(int start)
	 * a = b.substring(c)
	 * (assert (= a (Substring b c (- (Length b) 1))))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mSubString(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(Substring ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(" (- (Length ");
		sb.append(thisBaseName);
		sb.append(") 1)");
		sb.append(")");
		return sb.toString();
	}

	/**
	 * substring(int start, int end)
	 * a = b.substring(c, d)
	 * (assert (= a (Substring b c (- d 1))))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mSubString2(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		Value firstParam = vInvokeExpr.getArg(0);
		Value secondParam = vInvokeExpr.getArg(1);
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		String secondParamName = fileGenerator.getRenameOf(secondParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append("(Substring ");
		sb.append(thisBaseName);
		sb.append(" ");
		sb.append(firstParamName);
		sb.append(" ");
		sb.append("(- ");
		sb.append(secondParamName);
		sb.append(" 1)");
		sb.append(")");
		return sb.toString();
	}

	/**
	 * a = b.toString()
	 * (assert (= a b))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mToString(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		VirtualInvokeExpr vInvokeExpr = convertToVirtualInvokeExpr(invokeExpr);
		Value thisBase = vInvokeExpr.getBase();
		String thisBaseName = fileGenerator.getRenameOf(thisBase, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append(thisBaseName);
		return sb.toString();
	}

	/**
	 * a = String.valueOf(b)
	 * (assert (= a b))
	 * @param invokeExpr
	 * @param fileGenerator
	 * @param stmtIdx
	 * @return
	 */
	private static String mValueOf(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator, int stmtIdx){
		StaticInvokeExpr sInvokeExpr = (StaticInvokeExpr) invokeExpr;
		Value firstParam = sInvokeExpr.getArg(0);
		String firstParamName = fileGenerator.getRenameOf(firstParam, false, stmtIdx);
		
		StringBuilder sb = new StringBuilder();
		sb.append(firstParamName);
		return sb.toString();
	}
}
