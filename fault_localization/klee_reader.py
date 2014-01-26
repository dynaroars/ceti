#!/usr/bin/env python
import subprocess as sp
import os
import sys

def read_file(fn):
    with open(fn, 'r') as fh: 
        for line in fh: 
            yield line

def vcmd(cmd):
    proc = sp.Popen(cmd,shell=True,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    return proc.communicate(input=None)

def read_klee (filename_src, clean=True):
    #compile file with llvm
    include_path = "/home/Storage/Src/Devel/KLEE/klee/include"
    opts =  "--optimize -emit-llvm -c"
    filename_obj = os.path.splitext(filename_src)[0] + os.extsep + 'o'

    cmd = "llvm-gcc -I {} {} {} -o {}".format(include_path,opts,filename_src,filename_obj)

    rs,rs_err = vcmd(cmd)
    print 'rs: ',rs
    print 'rs_err: ',rs_err

    assert not rs
    assert "llvm-gcc" not in rs_err, "cmd '{}' failed\n{}".format(cmd, rs_err)


    #run klee and monitor output


    cmd = "klee --allow-external-sym-calls {}".format(filename_obj)
    print cmd
    proc = sp.Popen(cmd,shell=True,stdout=sp.PIPE, stderr=sp.STDOUT)

    while proc.poll() is None:
        line = proc.stdout.readline()
        
        print 'Read line:', line
        if line and "KLEE: ERROR: ASSERTION FAIL: 0" in line: 
            print 'Got It!'
            break
        #sys.stdout.flush()

    rs,rs_err = proc.communicate()
    print 'rs: ',rs
    print 'rs_err: ',rs_err

    #parse result
    rs = [r for r in rs.split('\n') if 'GOAL' in r]
    print rs

    #clean up

if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser()

    aparser.add_argument("file", help="instrumented C file")
 
    aparser.add_argument("-clean", "--clean",
                         help="remove temp files after done",
                         action="store_true")

    args = aparser.parse_args()
    read_klee(args.file,
              clean = args.clean)
             
                         





# GiaoChi Fri Jan 24:20:40:41 (20724) ~/Dropbox/git/cece/fault_localization 
# $ python klee_reader.py tests/p.3.c
# rs:  
# rs_err:  p.c:16: warning: conflicting types for built-in function 'printf'
# p.c: In function 'main':
# p.c:16: warning: return type of 'main' is not 'int'

# klee --allow-external-sym-calls tests/p.3.o
# Read line: KLEE: output directory = "klee-out-33"

# Read line: KLEE: WARNING: undefined reference to function: printf

# Read line: KLEE: WARNING ONCE: calling external: printf(35138192, (ReadLSB w32 0 uk_0), (ReadLSB w32 0 uk_1))

# Read line: KLEE: ERROR: ASSERTION FAIL: 0

# Got It!
# rs:  KLEE: NOTE: now ignoring this error at this location
# GOAL: uk_0 100, uk_1 1

# KLEE: done: total instructions = 28
# KLEE: done: completed paths = 1
# KLEE: done: generated tests = 1

# rs_err:  None
# ['GOAL: uk_0 100, uk_1 1']
# GiaoChi Fri Jan 24:20:43:31 (20725) ~/Dropbox/git/cece/fault_localization 
