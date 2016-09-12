
if [[ -d annotationWorkloads ]]; then
	rm -r annotationWorkloads
fi
mkdir annotationWorkloads


for dir in 10 30 50; do
	for fs in 10 25 50 60 70; do
		python annotation_benchmark.py $fs 3 $dir 10 1000 > annotationWorkloads/dir$dir\_fs$fs
	done
done
