all: ifElse ifElse2 for forIfElse funCall forNested forNestedIfElse recursion switchCase for_klee users load dart eg1 eg1_assert tripleloop basic cmd intArray
CC=../llvm/build/bin/clang
WCC=../whole-program-llvm/wllvm

ifElse: ifElse.c
	$(CC) -emit-llvm -c ifElse.c -o ifElse.bc
	$(CC) -emit-llvm -c ifElseTest.c -o ifElseTest.bc

ifElse2: ifElse2.c
	$(CC) -emit-llvm -c ifElse2.c -o ifElse2.bc

for_klee: for_klee.c
	$(CC) -emit-llvm -c for_klee.c -o for_klee.bc

users: ../coreutils/src/users.c
	$(CC) -emit-llvm -c ../coreutils/src/users.c -I../coreutils/lib -o users.bc
	#./setup_env.sh
	#$(WCC) -emit-llvm -c ../coreutils/src/users.c ../coreutils/lib/progname.c -I../coreutils/lib/ -Wunused-function -o users.bc

eg1_assert: eg1_assert.c
	$(CC) -emit-llvm -c eg1_assert.c -o eg1_assert.bc

eg1: eg1.c
	$(CC) -emit-llvm -c eg1.c -o eg1.bc

load: load.c
	$(CC) -emit-llvm -c load.c -o load.bc

dart: dart.c
	$(CC) -emit-llvm -c dart.c -o dart.bc

intArray: intArray.c
	$(CC) -emit-llvm -c intArray.c -o intArray.bc
	$(CC) -emit-llvm -c intCACI.c -o intCACI.bc
	$(CC) -emit-llvm -c intSACI.c -o intSACI.bc
	$(CC) -emit-llvm -c intCASI.c -o intCASI.bc
	$(CC) -emit-llvm -c intCASI2.c -o intCASI2.bc
	$(CC) -emit-llvm -c intSASI.c -o intSASI.bc
	
cmd: cmd.c
	$(CC) -emit-llvm -c cmd.c -o cmd.bc

basic: basic.c
	$(CC) -emit-llvm -c basic.c -o basic.bc

for: for.c
	$(CC) -emit-llvm -c for.c -o for.bc

tripleloop: tripleloop.c
	$(CC) -emit-llvm -c tripleloop.c -o tripleloop.bc

forIfElse: forIfElse.c
	$(CC) -emit-llvm -c forIfElse.c -o forIfElse.bc

switchCase: switchCase.c
	$(CC) -emit-llvm -c switchCase.c -o switchCase.bc


forNested: forNested.c
	$(CC) -emit-llvm -c forNested.c -o forNested.bc

forNestedIfElse: forNestedIfElse.c
	$(CC) -emit-llvm -c forNestedIfElse.c -o forNestedIfElse.bc

funCall: funCall.c
	$(CC) -emit-llvm -c funCall.c -o funCall.bc

recursion: recursion.c
	$(CC) -emit-llvm -c recursion.c -o recursion.bc

clean:
	rm -rf *.bc for
