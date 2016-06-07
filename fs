#!/usr/bin/env bash

DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

if [ "$#" -eq 0 ]; then
    echo "Illegal number of parameters"
    exit
fi

if [ $1 = "make" ]; then
    $DIR/testfs/mktestfs /tmp/fs
    echo "mktestfs success"
elif [ $1 = "start" ]; then
    if [ -z "$2" ]; then
        $DIR/testfs/testfs.exe /tmp/fs 2> /tmp/testfs.py
    else
        $DIR/testfs/testfs.exe /tmp/fs < input.txt 2> /tmp/testfs.py
    fi
elif [ $1 = "see" ]; then
    $DIR/visualize.sh /tmp/testfs.py
elif [ $1 = "output" ]; then
    vim /tmp/testfs.py
elif [ $1 = "compile" ]; then
    make clean; make all
    ./env.sh make -C testfs clean all
    ./run.sh testfs/testfs
elif [ $1 = "blocks" ]; then
    grep =B /tmp/testfs.py | tail -20
else
    echo "try again"
fi
