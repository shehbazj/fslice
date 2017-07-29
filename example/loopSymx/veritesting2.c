
int counter = 0, values = 0;

// pre: counter = 0 
for( i = 0 ; i < 100 ; i++ ) {	// 4
    if(input[i%10] == 'B'){	// 2
        counter++;
        values += 2;
    }
}

// operation: op1 -> counter +1 , condition: input[i] = 'B'
// op2 -> counter +0 , condition: input[i%10] != 'B' 
// all input idx between 0 to 9 (input[0,1,2...9]) need to
// be != 'B'

// post: == 75
// calculate number of operations required from counters:

// x * op1(counter)  + y * op2(counter) = post_condition(counter)
// x + y = loop_count
// x * 1 + y * 0 = 75
// x = 75
// y = loop_count - x = 25

// op1 = 75, op2 = 25

// op1 dependency input[i%10] == 'B'.
// is input[i] in write set of loop? no.
// op2 dependency input[i%10] != 'B'.
// is input[i] in write set of loop? no.
// there are no inter-transition point dependencies

// we need 75 op1's and 25 op2's
// input[0] input[74] = 'B'. input[75] input[99] != 'B'

// i = 0 to 99. with interval 1.
// 75 of input[i%10] = 'B'
// 25 of input[i%10] != 'B'
// variables involved. input[0... 9].
// any of them being set? no.
// range of loop 0...99
// input[0] i= {0,10,20, 90}
// input[1] i= {1,11,21, 91}

// 


if(counter == 75){
    bug();
}
