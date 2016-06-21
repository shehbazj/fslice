#!/usr/bin/env bash

# Verify that the input arguments are correct.
if [ "$#" -ne 6 ]; then
	echo "Wrong number of arguments!"
	echo "Usage: ./${0##*/} <file-with-tainted-operations> <verbose-flag> <debug-flag>"
	exit -1
fi

for argument in ${@:2}; do
	if [[ ("$argument" != "true" && ("$argument" != "false")) ]]; then
		echo -e "Unknown option: ${argument}\nChoose one from {true, false}."
		exit -1
	fi
done

# Prints the full path of the current directory.
DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

# Create a temporary Python file to process the generated tainted operations.
cat $DIR/visualize/head.py $1 $DIR/visualize/tail.py > /tmp/visualize.py

if [ "$2" == "true" ]; then
        metadata="--metadata"
else
        metadata=""
fi

# Create a visualization using the dot language.
if [ "$3" == "true" ]; then
        graph="--graph"
else
        graph=""
fi

if [ "$4" == "true" ]; then
        enum="--enum"
else
        enum=""
fi

if [ "$5" == "true" ]; then
	verbose="--verbose"
else
	verbose=""
fi

if [ "$6" == "true" ]; then
	debug="--debug"
else
	debug=""
fi

python /tmp/visualize.py $metadata $graph $enum $verbose $debug
