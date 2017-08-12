# script that prints z3 constraints for linear equation (our approach)
# ite equation- (veritesting approach).
# for our approach, a better equation is constant operation as shown
# in the constadd.py file in this folder.

if [ "$#" -ne 2 ]; then
	echo "usage [linear|ite] [numberOfIterations]"
	exit
fi

loopcount=$2
constraintType=$1

cat header.py

if [ "$constraintType" == "linear" ]; then
	for i in `seq 1 $loopcount`;
		do
			echo "counter$i =Int('counter$i')"
			echo "s.add(counter$i >= 0)"
			echo "s.add(counter$i <= 1)"
		done
	printf "s.add( "
	printf "counter$i * $i "
	for i in `seq 2 $loopcount`;do
		printf "+ counter$i * $i "
	done
	
	echo "== 75)"
elif [ "$constraintType" == "ite" ]; then
	echo "counter0=Int('counter0')
s.add(counter0 == 0)
s0= Int('s0')"
	for i in `seq 1 $loopcount`;
		do
			echo "counter$i=Int('counter$i')"
			echo "s.add(counter$i==If(s$(($i-1)) == 50,counter$(($i-1)) + $i, counter$(($i-1))))"
			echo "s$i=Int('s$i')"
		done
	echo ""
	echo "counter_final=Int('counter_final')
s.add(counter_final == 75)
s.add(counter_final == counter$(($loopcount)))"
fi

echo "x=s.check()
if(x == z3.sat):
	m = s.model()
	print m
else:
	print unsat"

