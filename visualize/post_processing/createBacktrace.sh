# DEPENDENCIES

# block size assumed to be 64, default block size for TESTFS
# customization may be required for other file systems, depending on their block size
# trace file generated as of commit #55 of on_disk_pointers branch in shehbazj/fslice. 
# if any changes are made to taint output since #55 (specifically "cerr <<" statements 
# in shehbazj/fslice/runtime/FSlice.cpp, change this script accordingly

echo "./normalize.sh TRACE_FILE"
if [[ $# -eq 0 ]]; then
	echo "Processing with default TRACE_FILE - /tmp/testfs.py"
fi

TRACE_FILE=${1:-/tmp/testfs.py}
BLOCK_SIZE=64
DEST_DIR=backtrace
BNUM_TAINT_FILE=bnum_taint_file

if [[ ! -f $TRACE_FILE ]]; then
	echo "File $TRACE_FILE does not exist"
	exit
fi

if [[ -f $BNUM_TAINT_FILE ]]; then
	rm $BNUM_TAINT_FILE	
	touch $BNUM_TAINT_FILE
fi

if [[ -d $DEST_DIR ]]; then
	rm -rf $DEST_DIR
fi
mkdir $DEST_DIR

filename=""
# stores (block_number, taint_for_block_number)
bnum_taint_tuple=""

# creates a backtrace file containing trace of taint for block number

createBlockVisualizeFile() {	
	blockNumber=`echo "$bnum_taint_tuple" | cut -d"," -f1`
	blockTaint=`echo "$bnum_taint_tuple" | cut -d" " -f2`
	echo "processing for blockNumber $blockNumber and blockTaint $blockTaint"
	
	fileBack=$DEST_DIR/$blockNumber\.$blockTaint\.back   # temporary file name, contains backtrace of block
	fileReverse=$DEST_DIR/$blockNumber\.$blockTaint\.reverse   # temporary file name, contains reverse of block backtrace
	fileName=$DEST_DIR/$blockNumber\.$blockTaint\.visualize   # valid python visualize file

	python ../trace.py -b $blockTaint $TRACE_FILE > $fileBack

	#tac $fileBack > $fileReverse
	#rm $fileBack
	#
	#cat ../head.py $fileReverse ../tail.py > $fileName
	#rm $fileReverse
}

# normalizes backtrace file. see README A.3, A.4
#normalizeBackTraceFile() {
#	
#


# takes taint trace file, generates trace lines as tuples <block number, block taint>
# we want unique <blockNumber, block number Taint> fields
# BlockTaint=B(BlockSize ,BlockNumber, BlockSizeTaint, Block number Taint)
# for each block, it now generates a valid python visualization file

cat /tmp/testfs.py | grep "B(64" | cut -d"(" -f2 | cut -d")" -f1 | cut -d "," -f2,4,5 | sort -u -t, -k 1,2 > $BNUM_TAINT_FILE
	
while read line
do
	bnum_taint_tuple=$line	
	createBlockVisualizeFile
#	normalizeBackTraceFile()	
done < $BNUM_TAINT_FILE

rm $BNUM_TAINT_FILE
