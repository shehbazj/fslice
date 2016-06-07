# If two templates of the same block are of the same type we delete the same template

FILES=./templates/*
for f1 in $FILES;
do
	echo $f1
	blockNum=`echo $f1 | cut -d '/' -f3 | cut -d '.' -f1`
	for f2 in $FILES;
	do
		blockNum2=`echo $f2 | cut -d '/' -f3 | cut -d '.' -f1`
		# if two templates are of different block numbers, do not
		# eliminate templates
		if [ $blockNum -ne $blockNum2 ]; then 
			continue
		fi

		if [[ -f $f1 && -f $f2 ]]; then # file may have been deleted
			if [[ "$f1" != "$f2" ]]; then  # f1 and f2 is not the same file
				if cmp f1 f2 > /dev/null 2>&1; then
					echo "$f1 $f2 different"
				else
					echo "$f1 $f2 same"
					rm $f2
					continue
				fi
			fi 
#			echo "both $f1 and $f2 exists"
		else
			echo "either $f1 or $f2 does not exist"
			continue
		fi


	done
done
