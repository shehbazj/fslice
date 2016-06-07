# for a given block number, print its taint values on RHS

echo "Usage ./checkBlockRHSOccurence.sh <bnum>"

bnum=$1
cat /tmp/testfs.py | grep "B(64,$bnum" | cut -d "=" -f1 > taints
while read line; do grep -r "$line\[" /tmp/testfs.py ; done < taints
