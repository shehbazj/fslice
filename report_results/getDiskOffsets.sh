#	script to process number of icmp instructions (all comparisions that occured for a filesystem workflow).
#	script to process unique ICMP instructions with disk comparisions (all disk structure comparisions in a filesystem workflow).
#	lists all blocks and their offsets in use.

initICMP=0
initicmp=372

icmp=`grep icmp /tmp/testfs.py | wc -l`
ICMP=`grep ICMP /tmp/testfs.py | wc -l`

echo "$icmp $ICMP"

echo "number of comparisions = $(($icmp-$initicmp))"
echo "disk comparisions = $(($ICMP-$initICMP))"

cat /tmp/testfs.py | grep ICMP | sort | uniq | cut -d" " -f2 > blockStructureTaintFile
cat /tmp/testfs.py | grep ICMP | sort | uniq | cut -d" " -f4 >> blockStructureTaintFile

noOfUniqICMPs=`grep "ICMP" /tmp/testfs.py | sort | uniq`

echo "Number of Uniq disk structure comparisions = $noOfUniqICMPs"

echo "---------------------"
echo "Taints of block Structures Accessed"
echo "---------------------"

cat blockStructureTaintFile | sort | uniq > tmp
mv tmp blockStructureTaintFile

cat blockStructureTaintFile

echo "---------------------"
echo "---------------------"

#echo "TAINT	| 	VALUE					|BLOCK NO. (If ANY)	|	OFFSET	"
echo "TAINT	|	BLOCK NO. (If ANY)	|	OFFSET	"
while read line;
do
	taintNo=$line
	taint='t'$taintNo'='
	taintDesc=`grep $taint /tmp/testfs.py | cut -d"=" -f2 | cut -d"#" -f1`
	if [[ $taintDesc =~ "O" ]]; then
		blockTaint=`echo $taintDesc | cut -d"(" -f2 | cut -d"," -f1`
		blockTaint=$blockTaint'='
		blockDesc=`grep $blockTaint /tmp/testfs.py`
		blockNum=`echo $blockDesc | cut -d"," -f2`
		offsetsMultiLines=`echo $taintDesc | grep -oP '\[\K[^\]]+'`
		offsets=`echo $offsetsMultiLines | tr '\n' ' '`
#		echo "$taint	|	 $taintDesc	|	$blockNum	|	$offsets	|"
		echo "$taint	|	$blockNum	|	$offsets	|"
	fi
done < blockStructureTaintFile

