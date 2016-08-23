# getFieldAnnotation.sh <taintFile>

# Collect all taints involved in ICMP Operations

# Check if Taints are values -> discard
# Check if Taints are Objects -> get the blocks taint that the object refers to.
# Check usage of that block Taint. If it is being used for "A", "M", The taint cannot be a FIELD.
# Check usage of that block taint. If it is a POINTER, the block cannot be a FIELD.

# TODO

# if a taint is being compared to a non-constant, the taint is not a field taint.
# if a taint is a pointer, it is not a field taint.
# if a taint is being used for A, it is not a field constant.
# if a taint is being compared to another taint that has A or M, it is not a field constant.

if [ "$#" -eq "0" ]; then
	echo "Usage ./getFieldAnnotation.sh taintFile"
	exit
fi

taintFile=$1

# Collect all taints involved in ICMP Operations

cat $taintFile | grep ICMP | cut -d" " -f2 > /tmp/taint1
cat $taintFile | grep ICMP | cut -d" " -f4 > /tmp/taint2

cat /tmp/taint1 | sort | uniq > /tmp/taints
cat /tmp/taint2 | sort | uniq >> /tmp/taints

cat /tmp/taints | sort | uniq > /tmp/taintX

mv /tmp/taintX /tmp/taints

rm /tmp/taint1 /tmp/taint2 /tmp/objTaints

# here /tmp/taints contains all relevant taints

# process collected taints

while read line; 
do
	# Check if Taints are values,binary operations or memory allocations -> discard
	# since FIELD values will never be used for such operations
	taint='t'$line'='
	line=`cat $taintFile | grep $taint`
	if [[ $line == *"V"* ]]; then
		continue
	elif [[ $line == *"A"* ]]; then
		continue 
	elif [[ $line == *"M"* ]]; then
		continue 
	elif [[ $line == *"O"* ]]; then
		while read line2; 
		do
			if [[ $line2 == *"$line"* ]]; then
				if [[ $line2 == *"M"* ]]; then
					continue
				elif [[ $line2 == *"A"* ]]; then
					continue
				else
					echo $line >> /tmp/objTaints
				fi
			fi 
		done < $taintFile
	else
		echo $taint >> /tmp/objTaints
		echo $line
	fi
done < /tmp/taints

echo "Blocks / Offsets being Referred"

cat /tmp/objTaints

#echo "< Object Taint,  Block Taint, Block Number , Offset >"
echo "< Object Taint, Block Number , Offset >"

while read objLine; 
do
	offset=`echo $objLine | awk -vRS="]" -vFS="[" '{print $2}'`

	objTaint=`echo $objLine | cut -d"=" -f1`
	
#	t763=O(t762,763,t762[0],t762[1],t762[2],t762[3]) # Load(140732601401264, 4)
	
	blockTaint=`echo $objLine | cut -d"=" -f2 | cut -d"," -f1 | cut -d"t" -f2`
#	echo blockTaint , $blockTaint
	blockTaintLine="t"$blockTaint"="
	while read blockLines; 
	do
		if [[ $blockLines == *"$blockTaintLine"* ]]; then
#			echo blockLines , $blockLines
#			echo blockTaintLine, $blockTaintLine , "expect t+<blockTaint> + ="
#			echo blockLines , $blockLines , "B() "
			blockNum=`echo $blockLines | cut -d"," -f2`
		fi
	done < $taintFile

	#echo $objTaint $blockTaint $blockNum $offset
	echo $objTaint $blockNum $offset

done < /tmp/objTaints

# make a list of all block taints that O objects refer to.

#rm /tmp/taints
