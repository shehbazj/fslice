for i in `ls gen_const*` ; do echo $i ; time python $i ; done 2> /tmp/time ; cat /tmp/time | grep "real" | cut -d "." -f2 | cut -d "s" -f1 | awk '{ sum += $1 } END { print sum }'

