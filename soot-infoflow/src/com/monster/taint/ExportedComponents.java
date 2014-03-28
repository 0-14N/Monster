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
	private String appPackageName = null;
	
	private ExportedComponents(){}
	
	public static ExportedComponents v(){
		if(instance == null){
			instance = new ExportedComponents();
		}
		return instance;
	}
	
	public void init(String exportedServices, String exportedReceivers, String exportedActivities){
		this.exportedServicesMap = new HashMap<String, Set<String>>();
		this.exportedReceiversMap = new HashMap<String, Set<String>>();
		this.exportedActivitiesMap = new HashMap<String, Set<String>>();
		initExportedComponents(exportedServices, this.exportedServicesMap);
		initExportedComponents(exportedReceivers, this.exportedReceiversMap);
		initExportedComponents(exportedActivities, this.exportedActivitiesMap);
	}

	public boolean isExported(String className){
		assert(appPackageName != null);
		
		Set<String> exportedServices = exportedServicesMap.get(appPackageName);
		if(exportedServices != null){
			for(String serviceName : exportedServices){
				if(serviceName.equals(className)){
					return true;
				}
			}
		}
		
		Set<String> exportedReceivers = exportedReceiversMap.get(appPackageName);
		if(exportedReceivers != null){
			for(String receiverName : exportedReceivers){
				if(receiverName.equals(className)){
					return true;
				}
			}
		}
		
		Set<String> exportedActivities = exportedActivitiesMap.get(appPackageName);
		if(exportedActivities != null){
			for(String activityName : exportedActivities){
				if(activityName.equals(className)){
					return true;
				}
			}
		}
		
		return false;
	}
	
	public void setAppPackageName(String appPackageName){
		this.appPackageName = appPackageName;
	}
	
	private void initExportedComponents(String fileName, HashMap<String, Set<String>> exportedComponentsMap){
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
				Set<String> components = exportedComponentsMap.get(packageName);
				if(components == null){
					components = new HashSet<String>();
					components.add(componentName);
					exportedComponentsMap.put(packageName, components);
				}else{
					components.add(componentName);
				}
			}
		} catch (IOException ioe) {
			ioe.printStackTrace();
		}
		finally{
			try{
				if(br != null){
					br.close();
				}
			
				if(fdr != null){
					fdr.close();
				}
			}catch(IOException ioe){
				ioe.printStackTrace();
			}
		}
	}

}
