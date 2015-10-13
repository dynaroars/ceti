# README #


CETI (Correcting Errors using Test-input) is an automatic program repair technique that uses test-input generation to repair C programs. The idea is to convert the buggy program/test suite specification into another program consisting of a location reachable iff the buggy program can be repair to pass the given test suite.

Additional information on CETI can be found from these papers

* Automating Program Verification and Repair Using Invariant Analysis and Test-input Generation Nguyen, T. Ph.D. Thesis, University of New Mexico, August 2014. 


## Setup ##

The source code of CETI is released under the BSD license and can be downloaded using the command 

```
#!shell

hg clone https://nguyenthanhvuh@bitbucket.org/nguyenthanhvuh/ceti/
```


CETI uses Ocaml/CIL to parse and operate over C programs, and Python to invoke the test-input generator KLEE.  CETI has been tested using the following setup:

* Debian Linux 7 (Wheezy)
* Ocaml 3.12.1
* CIL 1.7.3
* Python 2.7
* An installed KLEE version

### Run examples ###

```
#!shell

$ cd ceti
$ source klee_export.sh  #setup environments for llvm-gcc and klee
$ make  #compile the program
# execute on an example
$ ./tf ../programs/examples/bugfix/a.bug1.c ../programs/examples/bugfix/a.inputs ../programs/examples/bugfix/a.outputs
```


### Experimentations ###

Reproducing experiments for FSE paper for the Tcas program

- the C file must have a mainQ function, see e.g., in tests/tcas/orig

- preprocess file with CIL

```
#!shell

$ for i in {1..41} do cilly bug$i.c --save-temps --noPrintLn --useLogicalOperators ; done

```

- run program (e.g., on our 32-core machine)

```
#!shell

$ for i in {1..41}; do  rm -rf /tmp/cece_* &> t; echo "***** BEGIN $i *******"; time ./tf ../test/tcas/orig/bug$i.cil.i ../test/tcas/tcas.orig.inputs ../test/tcas/tcas.orig.outputs --top_n_ssids 80 --min_sscore 0.01;  echo "****** DONE $i ******"; done
```