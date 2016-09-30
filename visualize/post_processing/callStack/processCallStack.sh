rm -rf blocks.tmp/*
rm -rf blockTrace.tmp

if [[ ! -d blocks.tmp ]]; then
	echo "blocks.tmp does not exist, creating one"
	mkdir blocks.tmp
else
	echo "blocks.tmp already exists"
fi

cat /tmp/testfs.py | grep -e "CALL STACK" -e "B" > callStackAndBlockFile.tmp

while read line; 
do
	if [[ $line == *","* ]]; then
		echo $line | cut -d"=" -f1 >> blockTrace.tmp
	elif [[ $line == *":"* ]]; then
		echo $line | cut -d":" -f2 >> blockTrace.tmp
	fi	
done < callStackAndBlockFile.tmp

while read line;
do
	if [[ $line == *"()"* ]]; then
		stackLine=$line
	else
		block=$line
		echo $stackLine >> blocks.tmp/$line
	fi
done < blockTrace.tmp

cd blocks.tmp

for file in `ls`;
do
	sort $file | uniq > $file.back
	rm $file
done

cd ..

python stackSeparation.py

#rm blockTrace
