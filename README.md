# README #


CETI (Correcting Errors using Test-input) is an automatic program repair technique that uses test-input generation to repair C programs. The idea is to convert the buggy program/test suite specification into another program consisting of a location reachable iff the buggy program can be repair to pass the given test suite.


## Setup ##

The source code of CETI is released under the BSD license and can be obtained using the command 

```
hg clone https://nguyenthanhvuh@bitbucket.org/nguyenthanhvuh/ceti/
hg clone https://nguyenthanhvuh@bitbucket.org/nguyenthanhvuh/common_python/
```

CETI uses Ocaml/CIL to parse and operate over C programs, and Python to invoke the test-input generator KLEE.  CETI has been tested using the following setup:

* Debian Linux 7 (Wheezy)
* Python 2.7
* Ocaml 3.12.1
* CIL 1.7.3
* An installed KLEE version

### Installing KLEE and CIL ###

For `KLEE`, consult its [build page](http://klee.github.io/experimental/).  
For `CIL`, download `[cil-1.7.3](http://kerneis.github.io/cil/doc/html/cil/)` and do a `./configure; make`. 

### Building CETI ###
Assume that we are in `/PATH/TO/ceti/src/`, first edit `klee_export.sh` to update KLEE's path appropriately. Then do a `source klee_export.sh` so that we can call `klee`, .e.g., `klee --help` should produce some usage information.
Next edit the `Makefile` so that it contains something like this
```
OCAML_OPTIONS = \
-I ../faultloc/\
-I /PATH/TO/common_python/\
-I /PATH/TO/cil-1.7.3/_build/src/\
-I /PATH/TO/cil-1.7.3/_build/src/ext/\
-I /PATH/TO/cil-1.7.3/_build/src/frontc/\
-I /PATH/TO/cil-1.7.3/_build/ocamlutil/\
```
Now type `make clean; make` to compile `ceti`.

### Usage ###

Here are some usage examples of CETI.

Given the *buggy* C program `/PATH/TO/ceti/examples/bugfix/p.tcas100.c` 

```
#!c

  if(inhibit) {
    bias = up_sep ; //bug, should be up_sep + 100                                             
  }
  else {
    bias = up_sep;
  }
  if (bias > down_sep)
    return 1;
  else
    return 0;
}

int mainQ(int inhibit, int up_sep, int down_sep){
  return buggyQ(inhibit, up_sep, down_sep);
}

int main(int argc, char* argv[]){
  printf("%d\n",mainQ(atoi(argv[1]), atoi(argv[2]),atoi(argv[3])));
  return 0;
}
```
that when given the inputs `/PATH/TO/ceti/examples/bugfix/p.inputs`

```
#!

1  0 100
1 11 110
0 100 50
1 -20 60
0  0 10
0 0 -10
```

does not produce the expected outputs `/PATH/TO/ceti/examples/bugfix/p.outputs` 

```
#!

0 
1 
1 
1 
0
1
```
We call `ceti` to create a new program that produces these expected outputs when given the above inputs.

```
$ ./ceti ../examples/bugfix/p.tacas100.c ../examples/bugfix/a.inputs ../examples/bugfix/a.outputs
...
0. /tmp/CETI_789b61/p.tcas100.c.s1.t1_z1_c1.tf.c: bias = up_sep; ===> bias = uk_0 + uk_1 * up_sep; ===> uk_0 100, uk_1 1
```

This results means CETI found a program (stored in `/tmp/CETI_789b61/p.tcas100.c.s1.t1_z1_c1.tf.c`) that passes the in/outputs by changing the statement `bias = up_sep;` to `bias = 100 + up_sep;`.  

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

## Publications ##
Additional information on CETI can be found from these papers

* Automating Program Verification and Repair Using Invariant Analysis and Test-input Generation Nguyen, T. Ph.D. Thesis, University of New Mexico, August 2014.