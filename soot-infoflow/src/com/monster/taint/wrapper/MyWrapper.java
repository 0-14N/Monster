package com.monster.taint.wrapper;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;

public class MyWrapper {
	private final Logger logger = LoggerFactory.getLogger(getClass());
	private final String COLLECTION_WRAPPER_FILE = "../soot-infoflow/CollectionWrapper.txt";
	
	private EasyTaintWrapper wrapper = null;
	private static MyWrapper instance = null;
	private  Map<String, Set<String>> classList = null;
	private  Map<String, Set<String>> excludeList = null;
	private  Map<String, Set<String>> killList = null;
	private  Set<String> includeList = null;
	private Map<String, Set<String>> collectionPutList = null;
	
	private MyWrapper(){}
	
	public static MyWrapper v(){
		if(instance == null)
			instance = new MyWrapper();
		return instance;
	}
	
	public void init(EasyTaintWrapper wrapper){
		this.wrapper = wrapper;
		this.classList = this.wrapper.getClassList();
		this.excludeList = this.wrapper.getExcludeList();
		this.killList = this.wrapper.getKillList();
		this.includeList = this.wrapper.getIncludeList();
		this.collectionPutList = new HashMap<String, Set<String>>();
		try{
			initCollectionPutList();
		}catch(IOException ioe){
			System.out.print(ioe.toString());
		}
	}
	
	private void initCollectionPutList() throws IOException{
		FileReader fr = null;
		BufferedReader br = null;
		String line = null;
		try {
			fr = new FileReader(COLLECTION_WRAPPER_FILE);
			br = new BufferedReader(fr);
		    while((line = br.readLine()) != null && !line.isEmpty()){
		    	String[] tokens = line.split(":");
		    	String className = tokens[0].substring(1);
		    	String subSignature = tokens[1].substring(1, tokens[1].length()-1);
		    	Set<String> methods = this.collectionPutList.get(className);
		    	if(methods == null){
		    		methods = new HashSet<String>();
		    		methods.add(subSignature);
		    		this.collectionPutList.put(className, methods);
		    	}else{
		    		methods.add(subSignature);
		    	}
		    }
		}catch(IOException ioe){
			System.out.print(ioe.toString());
		}
		finally {
			if (br != null)
				br.close();
			if (fr != null)
				fr.close();
		}
	}

	private boolean isInList(String className, String subSignature, Map<String, Set<String>> map){
		boolean isIn = false;
		Set<String> methodsSubSignatures = map.get(className);
		if(methodsSubSignatures != null){
			for(String s : methodsSubSignatures){
				if(s.equals(subSignature)){
					isIn = true;
					break;
				}
			}
		}
		return isIn;
		
	}
	
	public boolean isInExcludeList(String className, String subSignature){
		return this.isInList(className, subSignature, this.excludeList);
	}
	
	public boolean isInClassList(String className, String subSignature){
		return this.isInList(className, subSignature, this.classList);
	}
	
	public boolean isInKillList(String className, String subSignature){
		return this.isInList(className, subSignature, this.killList);
	}
	
	public boolean isInCollectionPutList(String className, String subSignature){
		return this.isInList(className, subSignature, this.collectionPutList);
	}
}
