CETI (Correcting Errors using Test-input) is an automatic program repair technique that uses test-input generation to repair C programs. The idea is to convert the buggy program/test suite specification into another program consisting of a location reachable iff the buggy program can be repair to pass the given test suite.


## Setup ##

The source code of CETI is released under the BSD license and can be obtained using the command 

```
git clone https://nguyenthanhvuh@gitlab.org/nguyenthanhvuh/ceti.git
```

CETI uses Ocaml/CIL to parse and operate over C programs, and Python to invoke the test-input generator KLEE.  CETI has been tested using the following setup:

* Tested on Debian Linux 7 and 8
NOTE: make sure `/bin/sh` is bash instead of dash (use `dpkg-reconfigure dash` to switch)
* Python 2.7
* Ocaml 3.12.1:  `apt-get install ocaml-core`
* CIL 1.7.3
* An installed KLEE version

### Installing KLEE and CIL ###

For `KLEE`, consult its [build page](http://klee.github.io/experimental/).  
For `CIL`, download [cil-1.7.3](https://github.com/cil-project/cil/releases) and do a `./configure; make`. 

### Building CETI ###
First, make sure that `klee` can be called, .e.g., `klee --help` should produce some usage information.

Now, go to `path/to/ceti/src`.   Edit the `Makefile` so that it contains something like this
```
OCAML_OPTIONS = \
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

  if(inhibit) {bias = up_sep} ; //bug, should be up_sep + 100                                             
  else {bias = up_sep;}
  if (bias > down_sep) return 1;
  else return 0;
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
We call `ceti` to create a new program that produces these expected outputs when given the above inputs

```
$ ./ceti ../examples/bugfix/p.tcas100.c ../examples/bugfix/p.inputs ../examples/bugfix/p.outputs

#lots of msgs detailing CETI's runs

0. /tmp/CETI_789b61/p.tcas100.c.s1.t1_z1_c1.tf.c: bias = up_sep; ===> bias = uk_0 + uk_1 * up_sep; ===> uk_0 100, uk_1 1
```

The last line indicates that CETI creates a program that passes the in/outputs by changing the statement `bias = up_sep;` to `bias = 100 + up_sep;`. 

### Experimentations ###

Reproducing experiments for the Tcas program

- the C file must have a mainQ function, see e.g., in tests/tcas/orig

- preprocess file with CIL

```
#!shell

$ for i in {1..41} do cilly bug$i.c --save-temps --noPrintLn --useLogicalOperators ; done

```

- run program (e.g., on our 32-core machine)

```
$ for i in {1..41}; do  rm -rf /tmp/CETI_* &> t; echo "***** BEGIN $i *******"; time ./ceti ../benchmarks/tcas/orig/bug
$i.cil.i ../benchmarks/tcas/tcas.orig.inputs ../benchmarks/tcas/tcas.orig.outputs --top_n_sids 80 --min_sscore 0.01;  echo "****** DONE $i ******"; done                                                                          

#output and time are logged in `tcas.log`
```

## Trips and Tricks ##
Sometimes it is useful to preprocess input source code with `CIL`. For examples
```
#!shell

$ cilly file.c --save-temps --noPrintLn --useLogicalOperators   #now call CETI on the resulting file.c.cil.i

$ cilly file.c --save-temps --noPrintLn --noUseLogicalOperators   #This breaks and and or operator into multiple statements
```


## Publications ##
Additional information on CETI can be found from these papers

* ThanhVu Nguyen, Deepak Kapur, Westley Weimer, and Stephanie Forrest. Connecting Program Synthesis and Reachability: Automatic Program Repair using Test-Input Generation. In Tools and Algorithms for the Construction and Analysis of Systems (TACAS), pages 301--318. Springer, 2017.

* Automating Program Verification and Repair Using Invariant Analysis and Test-input Generation Nguyen, T. Ph.D. Thesis, University of New Mexico, August 2014.

