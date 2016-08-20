cat /tmp/testfs.py | grep -e "CALL STACK" -e "B" > callStackAndBlockFile

rm -rf blocks/*
rm -rf blockTrace

while read line; 
do
	if [[ $line == *","* ]]; then
		echo $line | cut -d"," -f2 >> blockTrace
	elif [[ $line == *":"* ]]; then
		echo $line | cut -d":" -f2 >> blockTrace
	fi	
done < callStackAndBlockFile

while read line;
do
	if [[ $line == *"()"* ]]; then
		stackLine=$line
	else
		block=$line
		echo $stackLine >> blocks/$line
	fi
done < blockTrace

cd blocks

for file in `ls`;
do
	sort $file | uniq > $file.back
	rm $file
done

cd ..

#rm blockTrace
