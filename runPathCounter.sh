#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/ifElse.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/ifElseTest.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/ifElse.bc > /dev/null

#declare -a arr=("yes" "groups" "sleep" "nice" "sync" "echo" "sum" "cksum" "pwd" "touch")
declare -a arr=("yes") # "groups" "sleep" "nice" "sync" "echo" "sum" "cksum" "pwd" "touch")
for file in "${arr[@]}"
#for file in $@ 
do
file1=coreutils/src/$file\.bc
./llvm/build/bin/clang -c -emit-llvm coreutils/src/$file\.c -o coreutils/src/$file\.bc -I coreutils/lib
echo $file
./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < $file1 > /dev/null
done


#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < coreutils/src/yes.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/for_klee.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < coreutils/src/users.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/users.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < coreutils/gnulib/lib/progname.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/users.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/load.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/forIfElse.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/forNested.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/recursion.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/funCall.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < example/switchCase.bc > /dev/null

### Testfs stuff
#cd testfs
#../llvm/build/bin/clang -c -emit-llvm bitmap.c
#../llvm/build/bin/clang -c -emit-llvm block.c 
#../llvm/build/bin/clang -c -emit-llvm csum.c 
#../llvm/build/bin/clang -c -emit-llvm dir.c 
#../llvm/build/bin/clang -c -emit-llvm file.c 
#../llvm/build/bin/clang -c -emit-llvm inode.c 
#../llvm/build/bin/clang -c -emit-llvm super.c 
#../llvm/build/bin/clang -c -emit-llvm testfs.c 
#../llvm/build/bin/clang -c -emit-llvm tx.c
#../llvm/build/bin/llvm-link bitmap.bc block.bc csum.bc dir.bc file.bc inode.bc super.bc testfs.bc tx.bc -o testfs.bc
##../llvm/build/bin/clang -c -emit-llvm testfs_dir_name_to_inode_nr_rec.c
#cd ..
##./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < testfs/testfs_dir_name_to_inode_nr_rec.bc > /dev/null
#./llvm/build/bin/opt -load ./build/libpathCounter.so -pathCounter < testfs/testfs.bc > /dev/null
