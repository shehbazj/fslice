# fslice
LLVM-based forward program slice instrumentation.

== Loop Analysis Pass == 

Analyzes loops and lists down different paths in a function. The paths are listed in terms of Basic Blocks. The Basic Blocks
inside a loop body are repeated in the loop body loopCount times. Once the path has been listed, we run a taint pass, to create
a file containing z3 variables and their associated operations.
these z3 variables and operations can then be run on the Z3 solver. this gives us the input values for the program to go through
the entire function.
For running the Z3 API, we can use the following:

Z3 Installation Instructions
```
virtualenv venv
source venv/bin/activate
python scripts/mk_make.py --python
cd build
make
make install
#You will find Z3 and the Python bindings installed in the virtual environment
venv/bin/z3 -h
...
python -c 'import z3; print(z3.get_version_string())'
...
```
