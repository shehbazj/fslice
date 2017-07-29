/* Simplified Code from DotNetZip. Figure 2 from paper
 * Characteristic Studies of Loop Problems for Structural
 * Test Generation via Symbolic Execution
 * */

public static void Main(String[] args) {
//	...
	for (int i = 1; i < args.Length; i++) {
		switch (args[i]) {
			case ”−keep”: keepOriginal = true; break;
			case ”−f”: force = true; break;
			case ”−v”: verbose = true; break;
			default: throw new ArgumentException(args[i]);
		}
	}
	string fname = args[0];
	bool decompress = (fname.ToLower().EndsWith(”.bz”) ||
			fname.ToLower().EndsWith(”.bz2”));
	// result not dependent on loop.
	string result = decompress ? Decompress(fname, force) :
		Compress(fname, force);
	// result calls external function(s). we assume both functions can return
	// all possible values of result for each new if statement we encounter

	// for the result == null comparision, we fork two states with result
	// having null and non-null symbolic value
	if (result==null) {
		Console.WriteLine(”No action taken. The file already exists.”);
	}
	else {
		if (verbose) {
		// pre-condition, verbose = none
		// post-condition, verbose = true
		// op - assignment - verbose = true, condition, args[i] == '-v'
		// num of ops required = 1
		// condition to be true atleast 1 time.

		// what is the input condition? args[i] == '-v'
		// IDL? yes. min iteration 1. increment 1. max = INF
		// have 1 iteration. args[1] = '-v'
		//	...
			if (decompress) { 
				// ... 
			} else { 
				// ... 
			}
		}
		// keepOriginal 
		// is loop condition? yes
		// is constant assignment? yes
		// post Condition = keepOriginal = true
		// post Condition = keepOriginal = false
		// 
		// operations -> op1 keepOriginal = true.
		// args[i] == "-keep"
 		// op2 -> noOP. condition -> args[i] != "-keep"
 		// is loop IDL? yes. 

		// XXX pre = post. skip loop.
		// result != null
		if (!keepOriginal) { 
			// ... 
		}
	}
}
