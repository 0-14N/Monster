package com.monster.taint.target;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class TargetManager {
	private static String IPC_FILE = "IPC.txt";
	private static TargetManager instance = null;
	private static Map<String, Set<String>> startComponentMethods = null;
	private static Set<String> subSignatures = null;
	
	private TargetManager(){}
	
	public static TargetManager v(){
		if(instance == null){
			instance = new TargetManager();
			try{
				init();
			}catch(IOException ioe){
				ioe.printStackTrace();
			}
		}
		return instance;
	}
	
	private static void init() throws IOException{
		startComponentMethods = new HashMap<String, Set<String>>();
		subSignatures = new HashSet<String>();
		FileReader fr = null;
		BufferedReader br = null;
		String line = null;
		try {
			fr = new FileReader(IPC_FILE);
			br = new BufferedReader(fr);
		    while((line = br.readLine()) != null){
		    	String[] tokens = line.split(":");
		    	String className = tokens[0].substring(1);
		    	String subSignature = tokens[1].substring(1, tokens[1].length()-1);
		    	Set<String> methods = startComponentMethods.get(className);
		    	if(methods == null){
		    		methods = new HashSet<String>();
		    		methods.add(subSignature);
		    		subSignatures.add(subSignature);
		    		startComponentMethods.put(className, methods);
		    	}else{
		    		methods.add(subSignature);
		    		subSignatures.add(subSignature);
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
	
	public boolean isStartComponent(String className, String subSignature){
		Set<String> methods = startComponentMethods.get(className);
		if(methods != null){
			return methods.contains(subSignature);
		}else{
			return subSignatures.contains(subSignature);
		}
	}
}
