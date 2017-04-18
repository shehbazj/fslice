declare -a arr=("ifElse" "basic" "ifElse2" "for" "forIfElse" "forNested" "forNestedIfElse" "intCACI")
for file in "${arr[@]}"
do
	bcFile=example/$file\.bc
	echo "PROCESSING $file"
	sleep 1
	./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < $bcFile > /dev/null 2> /tmp/path
	cat /tmp/path
	cd visualize/post_processing/pathCounter && ./z3LogProcessor.py && cd -
done
