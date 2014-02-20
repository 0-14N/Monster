package com.monster.taint.mstcallback;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class MSTCallbackFactory {

	private Logger logger = LoggerFactory.getLogger(getClass());
	private static MSTCallbackFactory instance = null;
	private final static String MSTCALLBACKS_FILE = "MSTCALLBACKS.txt";
	
	private MSTCallbackFactory(){}
	
	public static MSTCallbackFactory v(){
		if(instance == null)
			instance = new MSTCallbackFactory();
		return instance;
	}

	/**
	 * parse the "MSTCALLBACKS.txt" to create the MSTCallbacks
	 * 
	 * ++ called by Monster.init()
	 * @return
	 * @throws IOException
	 */
	public Set<MSTCallback> createMSTCallbacks() throws IOException{
		Set<MSTCallback> mstCallbacks = new HashSet<MSTCallback>();
		
		//[start] parsing "MSTCALLBACKS.txt" to construct MSTCallbacks
		FileReader fr = null;
		BufferedReader br = null;
		String line = null;
		try {
			fr = new FileReader(MSTCALLBACKS_FILE);
			br = new BufferedReader(fr);
		    while((line = br.readLine()) != null){
		    	if(line.isEmpty() || line.startsWith("#")) continue;
		    	
		    	String[] tokens = line.split("~");
		    	assert(tokens.length >= 3);
		    	String signature = tokens[0];
		    	boolean isStatic = tokens[1].equals("0") ? false : true;
		    	int argCount = Integer.parseInt(tokens[2]);
		    	int taintedParametersCount = tokens.length - 3;
		    	int[] taintedArgs = null;
		    	if(taintedParametersCount > 0){
		    		taintedArgs = new int[taintedParametersCount];
		    		for(int i = 0; i < taintedParametersCount; i++){
		    			taintedArgs[i] = Integer.parseInt(tokens[i+3]);
		    		}
		    	}
		    	
		    	MSTCallback mstCallback = new MSTCallback(signature, isStatic, argCount, taintedArgs);
		    	mstCallbacks.add(mstCallback);
		    }
		}catch(IOException ioe){
			logger.error("Failed to parse \"{}\"", MSTCALLBACKS_FILE);
		}
		finally {
			if (br != null)
				br.close();
			if (fr != null)
				fr.close();
		}
		//[end]
		return mstCallbacks;
	}
}
