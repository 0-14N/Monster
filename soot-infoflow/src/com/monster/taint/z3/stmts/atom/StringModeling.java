package com.monster.taint.z3.stmts.atom;

import java.util.ArrayList;
import java.util.HashMap;

import soot.SootMethodRef;
import soot.jimple.InvokeExpr;

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
	
	public static String modelMethod(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		SootMethodRef methodRef = invokeExpr.getMethodRef();
		switch(stringMethodsEnumMap.get(methodRef.getSignature())){
		case Concat:
			return mConcat(invokeExpr, fileGenerator);
		case Contains:
			return mContains(invokeExpr, fileGenerator);
		case ContentEquals:
			return mContentEquals(invokeExpr, fileGenerator);
		case ContentEquals2:
			return mContentEquals2(invokeExpr, fileGenerator);
		case EndsWith:
			return mEndsWith(invokeExpr, fileGenerator);
		case Equals:
			return mEquals(invokeExpr, fileGenerator);
		case EqualsIgnore:
			return mEqualsIgnore(invokeExpr, fileGenerator);
		case IndexOf:
			return mIndexOf(invokeExpr, fileGenerator);
		case IndexOf2:
			return mIndexOf2(invokeExpr, fileGenerator);
		case Intern:
			return mIntern(invokeExpr, fileGenerator);
		case IsEmpty:
			return mIsEmpty(invokeExpr, fileGenerator);
		case LastIndexOf:
			return mLastIndexOf(invokeExpr, fileGenerator);
		case LastIndexOf2:
			return mLastIndexOf2(invokeExpr, fileGenerator);
		case Length:
			return mLength(invokeExpr, fileGenerator);
		case Replace:
			return mReplace(invokeExpr, fileGenerator);
		case StartsWith:
			return mStartsWith(invokeExpr, fileGenerator);
		case StartsWith2:
			return mStartsWith2(invokeExpr, fileGenerator);
		case SubSequence:
			return mSubSequence(invokeExpr, fileGenerator);
		case SubString:
			return mSubString(invokeExpr, fileGenerator);
		case SubString2:
			return mSubString2(invokeExpr, fileGenerator);
		case ToString:
			return mToString(invokeExpr, fileGenerator);
		case ValueOf:
			mValueOf(invokeExpr, fileGenerator);
			default:
				assert(false);
				return null;
		}
	}
	
	private static String mConcat(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mContains(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mContentEquals(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mContentEquals2(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mEndsWith(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mEquals(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mEqualsIgnore(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mIndexOf(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mIndexOf2(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mIntern(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mIsEmpty(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mLastIndexOf(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mLastIndexOf2(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mLength(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mReplace(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mStartsWith(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mStartsWith2(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mSubSequence(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mSubString(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mSubString2(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mToString(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
	
	private static String mValueOf(InvokeExpr invokeExpr, SMT2FileGenerator fileGenerator){
		StringBuilder sb = new StringBuilder();
		return sb.toString();
	}
}
