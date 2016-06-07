FILES=./backtrace/*
for f in $FILES;
do
	#taintNo=`echo $f | cut -d'.' -f2`
	taintNo=`echo $f | cut -d'.' -f3`
	if [[ $taintNo -lt 6005 ]]; then
		rm $f
	fi	
	#echo $taintNo
#	if [[ $taintNo -lt 495 ]]; then
#		rm $f
#	fi
done
