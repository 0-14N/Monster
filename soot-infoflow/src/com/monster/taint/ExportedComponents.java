package com.monster.taint;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public class ExportedComponents {
	private static ExportedComponents instance = null;
	
	private HashMap<String, Set<String>> exportedServicesMap = null;
	private HashMap<String, Set<String>> exportedReceiversMap = null;
	private HashMap<String, Set<String>> exportedActivitiesMap = null;
	
	private ExportedComponents(){}
	
	public static ExportedComponents v(){
		if(instance == null){
			instance = new ExportedComponents();
		}
		return instance;
	}
	
	public void init(String exportedServices, String exportedReceivers, String exportedActivities){
		initExportedServices(exportedServices);
		initExportedReceivers(exportedReceivers);
		initExportedActivities(exportedActivities);
	}
	
	private void initExportedServices(String fileName){
		exportedServicesMap = new HashMap<String, Set<String>>();
		FileReader fdr = null;
		BufferedReader br = null;
		String line = null;
		try {
			fdr = new FileReader(fileName);
			br = new BufferedReader(fdr);
			
			while((line = br.readLine()) != null){
				String[] attrs = line.split(",");
				String packageName = attrs[0];
				String componentName = null;
				for(int i = 1; i < attrs.length; i++){
					if(attrs[i].contains("=")){
						String[] tokens = attrs[i].split("=");
						if(tokens[0].equals("name")){
							if(tokens[1].startsWith(".")){
								componentName = packageName + tokens[1];
							}else{
								componentName = tokens[1];
							}
						}
					}
				}
				assert(componentName != null);
				Set<String> components = exportedServicesMap.get(packageName);
				if(components == null){
					components = new HashSet<String>();
					components.add(componentName);
					exportedServicesMap.put(packageName, components);
				}else{
					components.add(componentName);
				}
			}
		} catch (IOException ioe) {
			ioe.printStackTrace();
		}
	}
	
	private void initExportedReceivers(String fileName){
		
	}
	
	private void initExportedActivities(String fileName){
		
	}
}
