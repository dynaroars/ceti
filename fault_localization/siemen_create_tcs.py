#!/usr/bin/env python

#A script that takes in a runall.sh and (correct) src.c from Siemens testsuite
#and produces
#1. src.inputs  
#2. src.outputs  ,the (expected) outputs of src.c
#also does lots of filtering to use only correct inputs (i.e., those that don't give error even on src.c).

import subprocess as sp
import os
import vu_common as CM


def siemen_parser(src):
    #setup filenames
    assert os.path.isfile(src)
    print src  # the/path/to/src.c  (#not necessarily full path)

    src_abspath = os.path.abspath(src)  #full path
    src_name =  os.path.basename(src_abspath) #src.c
    src_dir = os.path.dirname(src_abspath) #the/path/to

    exe   = src_name + os.extsep + 'exe'     #src.c.exe
    exe   = os.path.join(src_dir,exe) #the/path/to/src.c.exe

    outps = src_name + os.extsep + 'outputs' #src.c.outputs
    outps = os.path.join(src_dir,outps) #the/path/to/src.c.outputs

    inps  = src_name + os.extsep + 'inputs' #src.c.inputs
    inps = os.path.join(src_dir,inps) #the/path/to/src.c.inputs

    runscript = os.path.join(src_dir,'runall.sh')
    print runscript  #the/path/to/runall.sh
    runscript_abspath = os.path.abspath(runscript)
    #the/path/to/runall.sh.src.vsh
    runscript_ = runscript_abspath + os.extsep + src_name + os.extsep + 'vsh'

    print src_name
    print src_dir
    print exe
    print outps
    print inps
    print runscript_


    #./tcas.exe  958 1 1 2597  574 4253 0  399  400 0 0 1     > ../outputs/t1
    tcs = CM.iread(runscript)
    tcs = (tc for tc in tcs if "echo" not in tc)
    tcs = (tc.split() for tc in tcs)
    tcs = [[t for t in tc if CM.isnum(t)]  #input arguments
           for tc in tcs]
    print 'readin {} tcs'.format(len(tcs))

    #heuristically determine well-formed testcases based on freq of inp args
    #i.e., testcases with # of arguments appear frequently from testsuite

    counts = [len(tc) for tc in tcs]
    freqs = set(counts)
    freqs = [(f,counts.count(f)) for f in freqs]
    maxid = 0
    for i,(f,c) in enumerate(freqs[1:]):
        i_ = i+1
        if c > freqs[maxid][1]:
            maxid = i_
    #length that appears most often    
    amo_len = freqs[maxid][0]
    tcs = [tc for tc,c in zip(tcs,counts) if c == amo_len]
    print '{} tcs after filtering ({} args)'.format(len(tcs),len(tcs[0]))
    

    #compile src
    cmd = "gcc {} -o {}".format(src,exe)
    print cmd
    rs,rs_err = CM.vcmd(cmd)
    assert not rs, rs
    assert 'error' not in rs_err, rs_err
    assert os.path.isfile(exe)

    #create inputs file
    tcs = [' '.join(tc) for tc in tcs]
    CM.vwrite(inps, '\n'.join(tcs))
    assert os.path.isfile(inps)

    #create new testscript
    outps_ = " >> " + outps
    lines = [exe + " " + tc + " " + outps_ for tc in tcs]
    CM.vwrite(runscript_,'\n'.join(lines))
    assert os.path.isfile(runscript_)

    #run the testscript to get outputs file
    if os.path.isfile(outps): 
        cmd = "rm -f {}".format(outps)
        print cmd
        CM.vcmd(cmd) #rm output file first

    cmd = "sh {}".format(runscript_)
    print cmd
    CM.vcmd(cmd)
    assert os.path.isfile(outps)
    
    
if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser()
    
    aparser.add_argument("src", help="src.c")
   
    
    aparser.add_argument("-clean", "--clean",
                         help="remove temp files after done",
                         action="store_true")
    
    args = aparser.parse_args()
    siemen_parser(args.src)
                  
