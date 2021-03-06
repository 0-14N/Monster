package com.monster.taint.path;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.monster.taint.Monster;

import soot.Scene;
import soot.Unit;
import soot.Value;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.ThrowStmt;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ZonedBlockGraph;

public class MethodPathCreator {
	private Logger logger = LoggerFactory.getLogger(getClass());
	private static MethodPathCreator instance;
	
	private MethodPathCreator(){}
	
	public static MethodPathCreator v(){
		if(instance == null){
			instance = new MethodPathCreator();
		}
		return instance;
	}

	/**
	 * get all the paths (sequence of blocks) of a SootMethod from start to end
	 * @param method
	 * @return
	 */
	//public ArrayList<ArrayList<Block>> getPaths(ClassicCompleteBlockGraph graph){
	public ArrayList<ArrayList<Block>> getPaths(ZonedBlockGraph graph){
		ArrayList<ArrayList<Block>> result = new ArrayList<ArrayList<Block>>();
		List<Block> allBlocks = graph.getBlocks();
		List<Block> heads = graph.getHeads();
		List<Block> tails = graph.getTails();
		int i = 0;
	
		ArrayList<Block> nonExceptionHeads = new ArrayList<Block>();
		HashMap<String, Block> exceptionHandlers = new HashMap<String, Block>();
		for(i = 0; i < heads.size(); i++){
			Block headBlk = heads.get(i);
			Unit headU = headBlk.getHead();
			boolean isExceptionHandler = false;
			if(headU instanceof DefinitionStmt){
				DefinitionStmt ds = (DefinitionStmt) headU;
				Value rv = ds.getRightOp();
				Value lv = ds.getLeftOp();
				if(rv instanceof CaughtExceptionRef){
					String exceptionType = lv.getType().toString();
					exceptionHandlers.put(exceptionType, headBlk);
					isExceptionHandler = true;
				}
			}
			if(!isExceptionHandler){
				nonExceptionHeads.add(headBlk);
			}
		}
	
		//use an iterative algorithm to get the paths
		LinkedList<ArrayList<Integer>> pathSucc = new LinkedList<ArrayList<Integer>>();
		for(i = 0; i < nonExceptionHeads.size(); i++){
			ArrayList<Integer> headStart = new ArrayList<Integer>();
			Block head = nonExceptionHeads.get(i);
			headStart.add(new Integer(allBlocks.indexOf(head)));
			pathSucc.offer(headStart);
		}
		ArrayList<ArrayList<Integer>> intLists = this.getPathIterately(pathSucc, allBlocks, tails);
		for(ArrayList<Integer> intList : intLists){
			ArrayList<Block> blockList = new ArrayList<Block>();
			for(Integer integer : intList){
				Block b = allBlocks.get(integer.intValue());
				blockList.add(b);
				//if the block throws an exception
				Unit tail = b.getTail();
				if(tail instanceof ThrowStmt){
					ThrowStmt ts = (ThrowStmt) tail;
					Value exception = ts.getOp();
					String exceptionType = exception.getType().toString();
					Block handlerBlk = exceptionHandlers.get(exceptionType);
					if(handlerBlk != null){
						blockList.add(handlerBlk);
					}
				}
			}
			result.add(blockList);
		}
		
	
		/* the heavy overhead algorithm
		for(i = 0; i < nonExceptionHeads.size(); i++){
			Block head = nonExceptionHeads.get(i);
			ArrayList<Integer> source = new ArrayList<Integer>();
			//get the paths start from this head
			ArrayList<ArrayList<Integer>> intLists = forkPathsRecursively(source, head, allBlocks, tails);
			//convert the integer list to block list
			for(ArrayList<Integer> intList : intLists){
				ArrayList<Block> blockList = new ArrayList<Block>();
				for(Integer integer : intList){
					Block b = allBlocks.get(integer.intValue());
					blockList.add(b);
					//if the block throws an exception
					Unit tail = b.getTail();
					if(tail instanceof ThrowStmt){
						ThrowStmt ts = (ThrowStmt) tail;
						Value exception = ts.getOp();
						String exceptionType = exception.getType().toString();
						Block handlerBlk = exceptionHandlers.get(exceptionType);
						if(handlerBlk != null){
							blockList.add(handlerBlk);
						}
					}
				}
				result.add(blockList);
			}
		}
		*/
		return result;
	}

	/**
	 * a recursive call for expanding the path until we meet a end
	 * @param source : the path before handling the "branch"
	 * @param branch : the block being handled, maybe the "branch" is not a branch (only has one succor)
	 * @param allBlocks : it is used for querying the index of a block
	 * @param tails : it is used for judging whether it comes to end
	 * @return
	 */
	private ArrayList<ArrayList<Integer>> forkPathsRecursively(ArrayList<Integer> source, Block branch, List<Block> allBlocks, List<Block> tails){
		ArrayList<ArrayList<Integer>> results = new ArrayList<ArrayList<Integer>>();
		//branch is one of the end blocks
		if(tails.contains(branch)){
			source.add(new Integer(allBlocks.indexOf(branch)));
			results.add(source);
		}else{
			List<Block> succors = branch.getSuccs();
			//branch has only one succor, append to the end of source
			if(succors.size() == 1){
				source.add(new Integer(allBlocks.indexOf(branch)));
				ArrayList<ArrayList<Integer>> tmp = forkPathsRecursively(source, succors.get(0), allBlocks, tails);
				results.addAll(tmp);
			}else{//more than one succors, produce a new path for each succor
				int i = 0;
				source.add(new Integer(allBlocks.indexOf(branch)));
				for(; i < succors.size(); i++){
					Block succor = succors.get(i);
					//this is a loop, the succor is already in the previous list
					int loopStart = -1;
					if((loopStart = isInList(source, allBlocks.indexOf(succor))) != -1){
						//add the loop to the source and continue to handle other succors
						int tmpSize = source.size();
						for(int j = loopStart; j < tmpSize; j++){
							source.add(new Integer(source.get(j).intValue()));
						}
						continue;
					}else{
						ArrayList<Integer> clone = cloneList(source);
						ArrayList<ArrayList<Integer>> tmp =  forkPathsRecursively(clone, succor, allBlocks, tails);
						results.addAll(tmp);
					}
				}
			}
		}
		return results;
	}

	/**
	 * Pull a path from pathSucc's front, if its last block is tail, record the path,
	 * else, add its non-loop succors to it and offer it to pathSucc's end.
	 * 
	 * @param pathSucc
	 * @param allBlocks
	 * @param tails
	 * @return
	 */
	private ArrayList<ArrayList<Integer>> getPathIterately(LinkedList<ArrayList<Integer>> pathSucc,
			List<Block> allBlocks, List<Block> tails){
		ArrayList<ArrayList<Integer>> paths = new ArrayList<ArrayList<Integer>>();
		
		while(!pathSucc.isEmpty()){
			
			if(Monster.MAX_PATH_NUM > 0 && paths.size() == Monster.MAX_PATH_NUM){
				break;
			}
			
			ArrayList<Integer> path = pathSucc.poll();
			int size = path.size();
			int lastBlockIndex = path.get(size-1).intValue();
			Block lastBlock = allBlocks.get(lastBlockIndex);
			if(tails.contains(lastBlock)){
				paths.add(path);
				continue;
			}else{
				List<Block> succors = lastBlock.getSuccs();
				for(Block succor : succors){
					int succIndex = allBlocks.indexOf(succor);
					if(isInList(path, succIndex) != -1){
						continue;
					}else{
						ArrayList<Integer> clonePath = cloneList(path);
						clonePath.add(new Integer(succIndex));
						pathSucc.offer(clonePath);
					}
				}
			}
		}
		
		if(paths.size() == Monster.MAX_PATH_NUM){
			logger.warn("FUCK!!! Too many paths, we just analyze the first {}!", Monster.MAX_PATH_NUM);
		}
		
		return paths;
	}
	
	private int isInList(ArrayList<Integer> lst, int n){
		int result = -1;
		for(int i = 0; i < lst.size(); i++){
			if(lst.get(i).intValue() == n){
				result = i;
				break;
			}
		}
		return result;
	}
	
	private ArrayList<Integer> cloneList(ArrayList<Integer> source){
		ArrayList<Integer> result = new ArrayList<Integer>();
		for(int i = 0; i < source.size(); i++){
			Integer integer = new Integer(source.get(i).intValue());
			result.add(integer);
		}
		return result;
	}
	
}
