
int counter = 0, values = 0;

// pre: counter = 0 
for( i = 0 ; i < 100 ; i++ ) {	// 4
    if(input[i] == 'B'){	// 2
        counter++;
        values += 2;
    }
}

// operation: op1 -> counter +1 , condition: input[i] = 'B'
// op2 -> counter +0 , condition: input[i] != 'B'
// post: == 75
// calculate number of operations required from counters:

// x * op1(counter)  + y * op2(counter) = post_condition(counter)
// x + y = loop_count
// x * 1 + y * 0 = 75
// x = 75
// y = loop_count - x = 25

// op1 = 75, op2 = 25

// op1 dependency input[i] == 'B'.
// is input[i] in write set of loop? no.
// op2 dependency input[i] != 'B'.
// is input[i] in write set of loop? no.
// if yes, we unroll the loop to the extent where input[i] and its dependency
// are in the same loop body.
// there are no inter-transition point dependencies

// each transition point evaluated 

// we need 75 op1's and 25 op2's
// input[0] input[74] = 'B'. input[75] input[99] != 'B'

if(counter == 75){
    bug();
}
