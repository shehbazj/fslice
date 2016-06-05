#!/usr/bin/env bash

# This script takes either all backtraces in the folder backTraces or the user given argument and creates a template and stores it in "templates" folder.
# The script also calls computeTemplateCksum.sh which creates a checksum of the template for clustering and stores them in "cksums" folder

WORKING_DIR=`pwd`
SRC_DIR=`pwd`/backtrace
PREPROCESS_DIR=`pwd`/prenormalize
DEST_DIR=`pwd`/templates
FILES=${@:-*.back}

if [ -d $PREPROCESS_DIR ]; then
	rm -rf $PREPROCESS_DIR
fi

mkdir $PREPROCESS_DIR

if [ -d $DEST_DIR ]; then
	rm -rf $DEST_DIR
fi

mkdir $DEST_DIR

# the variable replaces all constants with character 'C'
# useful for standardising templates
removeConstants=True
#removeConstants=False

# Prints the full path of the current directory.
#DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )
if [ -d cksums ]; then
	rm -rf cksums
fi

mkdir cksums

if [ $# -gt 1 ]; then
	for file in $@; do
		cp $file $SRC_DIR
	done
fi

cd $SRC_DIR

for file in $FILES; do
	echo "Processing $file"
	
	taintLine=`head -1 $file`
    echo $taintLine
	taintValue=`echo $taintLine | cut -d'=' -f1`
	
	#echo "global removeConstants" > template/body.py
	rm $WORKING_DIR/baseTemplateFunctions/body.py
	echo "removeConstants=$removeConstants" >> $WORKING_DIR/baseTemplateFunctions/body.py
	tac $file >> $WORKING_DIR/baseTemplateFunctions/body.py
	
	# Create a temporary Python file to process the generated tainted operations.
	cat $WORKING_DIR/baseTemplateFunctions/head.py $WORKING_DIR/baseTemplateFunctions/body.py >> $WORKING_DIR/prenormalize/$file.py
	#echo "print $taintValue" >> template/$1.py
	
	# 0 - place variables as constants.
	# 1 - retain variables
	blockNumber=`echo $file | cut -d'.' -f1`
	python $WORKING_DIR/prenormalize/$file.py > $WORKING_DIR/templates/$file.template
	$WORKING_DIR/computeTemplateCksum.sh $file $blockNumber $removeConstants
done
