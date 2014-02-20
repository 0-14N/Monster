package com.monster.taint;

public enum MethodHubType {
	CALLED_FORWARD,  //this method was called during forward analysis
	CALLED_BACKWARD, //this method was called during backward analysis
	INVOKING_RETURN, //this method called A and A return back to A
}
