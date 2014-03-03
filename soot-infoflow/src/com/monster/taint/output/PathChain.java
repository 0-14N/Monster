package com.monster.taint.output;

import java.util.ArrayList;

import com.monster.taint.path.MethodPath;

public class PathChain {
	private MethodPath singlePath = null;
	private ArrayList<PathChain> inDepPaths = null;
	private ArrayList<PathChain> retDepPaths = null;
	
	public PathChain(){}
	
	public void init(MethodPath path){
		this.singlePath = path;
		this.inDepPaths = new ArrayList<PathChain>();
		this.retDepPaths = new ArrayList<PathChain>();
	}
	
	public PathChain(MethodPath path){
		this.singlePath = path;
		this.inDepPaths = new ArrayList<PathChain>();
		this.retDepPaths = new ArrayList<PathChain>();
	}
	
	public void setInDepPaths(ArrayList<MethodPath> paths){
		for(MethodPath path : paths){
			PathChain inDepPath = new PathChain(path);
			this.inDepPaths.add(inDepPath);
		}
	}
	
	public void setRetDepPaths(ArrayList<MethodPath> paths){
		for(MethodPath path : paths){
			PathChain retDepPath = new PathChain(path);
			this.retDepPaths.add(retDepPath);
		}
	}

	public PathChain getFirstInDepChain(){
		assert(hasInDepPaths());
		return this.inDepPaths.get(0);
	}
	
	public PathChain getFirstRetDepChain(){
		assert(hasRetDepPaths());
		return this.retDepPaths.get(0);
	}
	
	public boolean hasInDepPaths(){
		return this.inDepPaths.size() > 0;
	}
	
	public boolean hasRetDepPaths(){
		return this.retDepPaths.size() > 0;
	}

	public MethodPath getSinglePath() {
		return singlePath;
	}

	public ArrayList<PathChain> getInDepPaths() {
		return inDepPaths;
	}

	public ArrayList<PathChain> getRetDepPaths() {
		return retDepPaths;
	}
	
}
