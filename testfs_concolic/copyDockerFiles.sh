
if [[ "$#" != "1" ]]; then
	echo "Usage : copyDockerFiles.sh <numTests>"
	exit
fi

rm f[0-9]*

numTests=$1
cp filelist filelist$numTests
for i in `seq 10 $numTests`; 
do
	echo "f$i" >> filelist$numTests
done

while read line; do sudo docker cp testfs_container:/home/klee/testfs_concolic/$line . ; done < filelist$numTests

for i in `ls f[0-9]*` ; do
	cat $i | grep "object    1: data:" > tmp-file
	sed 's/object    1: data: b//g' tmp-file > tmp2-file
	sed -e 's|["'\'']||g' tmp2-file > $i-data
done;
