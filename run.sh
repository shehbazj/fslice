#!/usr/bin/env bash

DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )
export LLVM_COMPILER=clang
export LLVM_COMPILER_PATH=$DIR/llvm/build/bin/
export CC=$DIR/whole-program-llvm/wllvm
export CXX=$DIR/whole-program-llvm/wllvm++

# run is invoked using ./run testfs/testfs
# hence $1 = filesystem executable

# extract bc use -
# it extracts the bitcode section from the given ELF or MACH-O object and reassembles it to an actual bitcode file.

$DIR/whole-program-llvm/extract-bc $1

# opt = optimize 
# info about all these options were obtained by using the following command:
# opt -load=libFSlice.so -help
#
#
# load = load the dynamic object plugin, which is libFSlice.so
# opt -load=libFSlice.so -help gives the following info regarding the options used.
# constprop - simple constant propagation
# ssa - single static assignment form - every variable is assigned only once.
#					multiple assignment of variables leads to giving version numbers
# sccp - sparse conditional constant propagation
# sccp - removing dead code and doing constant propagation in ssa form of code
#
# scalarrepl - Scalar Replacement of Aggregates - SSAUp
# eleminating all enums and complicated structures by treating each variables separately. see fruit example here:
# https://books.google.ca/books?id=Pq7pHwG1_OkC&pg=PA331&lpg=PA331&dq=scalar+replacement+of+aggregates&source=bl&ots=4Y80Lth5mU&sig=CIxJEJe08Z7scX7k5w1K_MMUKWM&hl=en&sa=X&ved=0ahUKEwi1kMWowp3LAhXFkh4KHXY6DPoQ6AEIITAB#v=onepage&q=scalar%20replacement%20of%20aggregates&f=false

# mergereturn - Unify Function Exit Nodes
# ensure that functions have atmost one exit function in them.

# sink - Code Sinking
# moves instructions to successor blocks, when possible, so that they are not executed on paths where there results are not needed

# licm - Loop Invariant Code motion
# move code inside loop outside the loop without changing function semantics 

# mem2reg - Promote Memory to register
# 

# fslice - File system runtime program slicing pass
# read - http://www0.cs.ucl.ac.uk/staff/mharman/exe1.html 

# optimize shared object file libFSlice.so and call it testfs.inst.bc

$DIR/llvm/build/bin/opt -load $DIR/build/libFSlice.so -constprop -sccp -scalarrepl -mergereturn -sink -licm -reg2mem -fslice -reg2mem $1.bc -o $1.inst.bc

# link libFSlice.bc and testfs.inst.bc and call it testfs.inst2.bc

$DIR/llvm/build/bin/llvm-link -o=$1.inst2.bc $DIR/build/libFSlice.bc $1.inst.bc

# Optimize the linked file testfs.inst2.bc and call it testfs.opt.bc. 

$DIR/llvm/build/bin/opt -reg2mem $1.inst2.bc -o $1.opt.bc

# Compile bc with clang that would result in creation of .o optimized file

$DIR/llvm/build/bin/clang++ -c $1.opt.bc -o $1.opt.o

# create an exe out of the intermediate optimized file

$DIR/llvm/build/bin/clang++ -o $1.exe $1.opt.o $LDFLAGS

echo "$1.exe created"
