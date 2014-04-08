package com.monster.batch.runner;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.concurrent.TimeoutException;

import org.apache.commons.io.FileUtils;

import com.google.common.io.ByteStreams;

public class Main {
	private static final String SDK_PLATFORMS = "/home/monster2/sdk-platforms/";
	
	public static void main(String[] argv){
		new Main().run(argv);
	}
	
	private void run(String[] argv){
		if(argv.length != 3){
			printUsage();
			System.exit(-1);
		}
		
		String apkDir = argv[0];
		String monsterOutPath = argv[1];
		String thisOut = argv[2];
		
		if(!verifyDirExist(apkDir)){
			printUsage();
			System.exit(-1);
		}
		
		
		File[] apks = new File(apkDir).listFiles();
		for(File apk : apks){
			if(apk.getName().endsWith(".apk")){
				//clean monster-out
				assert(cleanMonsterOut(monsterOutPath));
				
				String apkPath = apk.getAbsolutePath();
				String apkOutDirName = thisOut + "/" + apk.getName().substring(0, apk.getName().length()-4);
				File apkOutDir = new File(apkOutDirName);
				if(!apkOutDir.exists()){
					apkOutDir.mkdir();
				}
				
				try {
					Process process = Runtime.getRuntime().exec("java -Xms16g -ea -jar monster.jar " + apkPath + " " + SDK_PLATFORMS);
					
					Worker worker = new Worker(process);
					worker.start();
					
					//20 minutes
					worker.join(1000 * 60 * 20);
					if(worker.exit == null){
						System.out.println("Timeout: " + apk.getAbsolutePath());
						worker.interrupt();
						Thread.currentThread().interrupt();
					}else{
						InputStream stdout = new BufferedInputStream(process.getInputStream());
						FileOutputStream stdoutFileOutputStream = new FileOutputStream(apkOutDir+"/"+"stdlog");
						ByteStreams.copy(stdout, stdoutFileOutputStream);
					
						InputStream stderr = new BufferedInputStream(process.getErrorStream());
						FileOutputStream stderrFileOutputStream = new FileOutputStream(apkOutDir+"/"+"errlog");
						ByteStreams.copy(stderr, stderrFileOutputStream);
					}
					
					process.destroy();
				} catch (Exception e) {
					System.out.println("Exception happens when getRuntime.exec: " + apk.getAbsolutePath());
					e.printStackTrace();
				}
				
				//handle monster-out
				try {
					FileUtils.copyDirectoryToDirectory(new File(monsterOutPath), new File(apkOutDirName));
				} catch (IOException e) {
					System.out.println("Copy monster-out exception");
					e.printStackTrace();
				}
				
			}
		}
		
	}
	
	private void printUsage(){
		System.out.println("Usage: \n" + 
								"java -ea -jar BatchRunner.jar " +
								"apkDir/ monsterOutPath batchRunnerOutDir");
	}
	
	private boolean verifyDirExist(String apkDir){
		File f = new File(apkDir);
		if(f.exists() && f.isDirectory()){
			return true;
		}
		return false;
	}
	
	private boolean cleanMonsterOut(String monsterOutPath){
		if(!verifyDirExist(monsterOutPath)){
			return false;
		}
		try{
			String shellPath = monsterOutPath + "/clean.sh";
			Process cleanProcess = Runtime.getRuntime().exec(shellPath);
			cleanProcess.waitFor();
		}catch(Exception e){
			e.printStackTrace();
			return false;
		}
		return true;
	}
}

class Worker extends Thread {
	  private final Process process;
	  public Integer exit;
	  
	  Worker(Process process) {
	    this.process = process;
	  }
	  
	  public void run() {
	    try { 
	      exit = process.waitFor();
	    } catch (InterruptedException ignore) {
	    	Thread.currentThread().interrupt();
	    	System.out.println("InterruptedException happens in Worker.run()!");
	    }
	  }  
}