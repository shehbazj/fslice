// Input Dependent Loop 
// from the paper: Characteristic Studies of Loop Problems for
// Structural Test Generation via Symbolic Execution
// Figure 1

// Example from Wix
//
// If its a IDL, NOP does not matter.
// If its a FIL, NOP can be used to fill gaps.

public static Version ParseVersion(string ver)
{
	int dotCount = 0;
	
	for ( int i = 0 ; i < ver.length ; i++){
		char c = ver[i];
		if(c == '.'){
			dotCount++;
		}
		// ...
	}

/*	dotCount - pre-condition = 0
 *	postCondition = 0
 *	operation -> if(c == '.') dotcount++
 *	operation -> if(c != '.') dotcount + 0
 *	loop - IDL? FIL? 
 *	IDL.
 *	(x op1 + y op2) = postCondition
 *	x 1 + 0 = 0
 *	x = 0
 *	x + y = loopCount
 *	y 0 times. loopCount 0 times.
 *	min (loopCount times)
 *	0
 * */

	
	if(dotCount == 0) {
		ver = ver + ".0";
	}

/*	dotCount - loop dependent? yes
 *	why? it is set to a new value after each iteration
 *	operations - 
 *	op1 = dotcount++ if(c == '.')
 *	op2 = dotcount if(c != '.')
 *	x op1 + y op2 = postCondition
 *	x op1 + y op2 > 3
 *	x (op1) + y (0) > 3
 *	x = 4
 *	x + y = loopCount
 *	x = loopCount
 *	loop has to happen 4 times
 *	ver.length = 4	// input characteristic
 *	each time op1 has to be performed.
 *	c == '.'
 *	c = ver[i]
 *	is ver[i] dependent only on current iteration?
 *	yes. 
 *	get all iteration dependencies
 *	ver[0,1,2,3]
 *	ver[0,1,2,3] = '.' // input characteristic
 * */

	else if(dotCount > 3) {
		string[] verSplit = ver.Split('.');
		ver = String.Join(".", verSplit, 0, 4);
	}
	//...
}
