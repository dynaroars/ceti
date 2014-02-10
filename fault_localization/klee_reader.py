#!/usr/bin/env python
import subprocess as sp
import os
import sys
import shutil

def tbf_worker(src, sid, cid, idxs, do_savetemps):
    #$ ./tf /tmp/cece_1392070907_eedfba/p.c --do_ssid 3 --xinfo z3_c0 --idxs "0 1"

    idxs = " ".join(map(str,idxs))
    xinfo = "z{}_c{}".format(len(idxs),cid)

    msg = 'Python: *** instrument {} sid {} xinfo {} idxs {} ***'.format(src,sid,xinfo,idxs)
    print msg 


    cmd = './tf {} --do_ssid {} --xinfo {} --idxs "{}"'.format(src,sid,xinfo,idxs)
    print "$ {}".format(cmd)
    proc = sp.Popen(cmd,shell=True,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    rs,rs_err = proc.communicate()

    print rs_err, msg + ".. done"

    assert not rs, rs
    if "error" in rs_err:
        print 'instrument error'
        print cmd
        print rs_err
        return None

    return "done instrumenting with {}".format(sid)

def tbf(src, combs, do_savetemps, do_parallel):
    #e.g., combs = [(1,5), (5,2), (9,5)]

    import itertools
    max_comb_siz = 2

    combs_ = []
    for sid,vs_siz in combs:
        for siz in range(max_comb_siz+1):
            cs = itertools.combinations(range(vs_siz),siz)
            combs_.extend([(sid,i,list(c)) for i,c in enumerate(cs)])

    print len(combs_)
    print combs_

    for sid,cid,idxs in combs_:
        tbf_worker(src,sid,cid,idxs,do_savetemps)



def instrument_worker(src, sid, do_savetemps):
    #./tf /tmp/cece_1391897182_68074b/p.bug2.c --do_instrument_ssid 2

    msg = 'Python: *** instrument {} wrt sid {} ***'.format(src,sid)
    print msg 

    cmd = "./tf {} --do_instrument_ssid {}".format(src,sid)
    print "$ {}".format(cmd)
    proc = sp.Popen(cmd,shell=True,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    rs,rs_err = proc.communicate()

    print rs_err, msg + ".. done"

    assert not rs, rs
    if "error" in rs_err:
        print 'instrument error'
        print cmd
        print rs_err
        return None

    return "done instrumenting with {}".format(sid)
    


def instrument(src, ssids, do_savetemps, do_parallel):
    #parallism on ssids
    # time python klee_reader.py /tmp/cece_1391898175_e46d2a/p.c --do_instrument "1 2" --do_parallel

    print "Processing {} files (parallel: {})".format(len(ssids),do_parallel)

    def wprocess(tasks,Q):
        rs = [(sid,instrument_worker(src,sid,do_savetemps)) for sid in tasks]
        if Q is None: #no multiprocessing
            return rs
        else:
            Q.put(rs)

    tasks = ssids

    if do_parallel:
        from vu_common import get_workloads
        from multiprocessing import (Process, Queue,
                                     current_process, cpu_count)
        Q = Queue()
        workloads = get_workloads(tasks,max_nprocesses=cpu_count(),chunksiz=1)

        print "workloads 'instrument ssid' {}: {}".format(len(workloads),map(len,workloads))
        workers = [Process(target=wprocess,args=(wl,Q)) for wl in workloads]

        for w in workers: w.start()
        wrs = []
        for _ in workers: wrs.extend(Q.get())

    else:
        wrs = wprocess(tasks,Q=None)
        
    wrs = [(sid,r) for (sid,r) in wrs if r]
    print "SUMMARY: For '{}', instrument {} files / {} total (parallel: {})".format(src,len(wrs),len(tasks),do_parallel)

    for i,(sid,r) in enumerate(wrs):
        print "{}. sid {}: {}".format(i,sid,r)

#compile file then run klee on the resulting object file
def read_klee_worker (src, do_savetemps):
    print "Python: *** processing {} ***".format(src)

    #compile file with llvm
    include_path = "/home/Storage/Src/Devel/KLEE/klee/include"
    llvm_opts =  "--optimize -emit-llvm -c"
    obj = os.path.splitext(src)[0] + os.extsep + 'o'
    
    cmd = "llvm-gcc -I {} {} {} -o {}".format(include_path,llvm_opts,src,obj)
    print "$ {}".format(cmd)
    proc = sp.Popen(cmd,shell=True,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    rs,rs_err = proc.communicate()

    assert not rs, rs

    if "llvm-gcc" in rs_err or "error" in rs_err:
        print 'compile error:\n', rs_err
        return None
    

    #run klee and monitor its output
    klee_outdir = "{}-klee-out".format(obj)
    klee_opts = " --allow-external-sym-calls -output-dir={}".format(klee_outdir)

    cmd = "klee {} {}".format(klee_opts,obj)
    print "$ {}".format(cmd)
    proc = sp.Popen(cmd,shell=True,stdout=sp.PIPE, stderr=sp.STDOUT)

    while proc.poll() is None:
        line = proc.stdout.readline()
        line = line.strip()
        if line:
            print 'stdout:', line
            if "KLEE: ERROR: ASSERTION FAIL: 0" in line: 
                print 'Got It!'
                break
        #sys.stdout.flush()
            


    rs,rs_err = proc.communicate()


    if rs_err: print 'rs_err:\n',rs_err

    if rs: 
        print 'rs:\n',rs
        rs = [r for r in rs.split('\n') if 'GOAL' in r]
        if len(rs) == 1:
            rs = rs[0]
            rs = rs[rs.find(':')+1:].strip()

        return rs


    print "No result for '{}'".format(src)
    return None
        

def read_klee(src, do_savetemps, do_parallel):
    file_ = os.path.basename(src)
    dir_ = os.path.dirname(src)

    
    files = [os.path.join(dir_,f) for f in os.listdir(dir_)
             if f.endswith('.tf.c') and f.startswith(file_)]

    files = sorted(files)
    #Iterate over all file with .tf.c extension
    print "Processing {} files (parallel: {})".format(len(files),do_parallel)

    def wprocess(tasks,Q):
        rs = [(f, read_klee_worker(f,do_savetemps)) for f in tasks]
        if Q is None: #no multiprocessing
            return rs
        else:
            Q.put(rs)

    tasks = files

    if do_parallel:
        from vu_common import get_workloads
        from multiprocessing import (Process, Queue,
                                     current_process, cpu_count)
        Q = Queue()
        workloads = get_workloads(tasks,max_nprocesses=cpu_count(),chunksiz=2)

        print "workloads 'read_klee' {}: {}".format(len(workloads),map(len,workloads))
        workers = [Process(target=wprocess,args=(wl,Q)) for wl in workloads]

        for w in workers: w.start()
        wrs = []
        for _ in workers: wrs.extend(Q.get())
    else:
        wrs = wprocess(tasks,Q=None)

    #rs = [(f,read_klee(f,do_savetemps)) for f in files]

    wrs = [(f,r) for (f,r) in wrs if r]
    print "SUMMARY: For '{}', found {} fixes/ {} total (parallel: {})".format(src,len(wrs),len(tasks),do_parallel)
    for i,(f,r) in enumerate(wrs):
        print "{}.{}: {}".format(i, f, r)
        

if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser()
    
    aparser.add_argument("file", help="instrumented C file")
 


    aparser.add_argument("--do_savetemps",
                         help="don't remove temp files after done",
                         action="store_true")

    aparser.add_argument("--do_parallel",
                         help="use multiprocessing",
                         action="store_true")

    aparser.add_argument("--do_instrument",
                         help='instrument ssids, e.g., --do_tbf "1 3 7 9"',
                         dest='ssids',
                         action="store")

    aparser.add_argument("--do_tbf",
                         help='transform and bug fix, e.g., --do_tbf "(1,5); (5,2); (9,5)"',
                         dest='combs',
                         action="store")

    args = aparser.parse_args()

    if args.ssids:
        ssids = [int(sid) for sid in args.ssids.split()]
        print ssids
        instrument(args.file, ssids, 
                   do_savetemps=args.do_savetemps, 
                   do_parallel=args.do_parallel)
    elif args.combs:
        #[(1,5), (5,2), (9,5)]
        combs = [comb.strip() for comb in args.combs.split(";")]
        combs = [comb[1:][:-1] for comb in combs] #remove ( )
        combs = [comb.split(',') for comb in combs]
        combs = [(int(comb[0]),int(comb[1])) for comb in combs]

        tbf(args.file, combs, 
            do_savetemps=args.do_savetemps,do_parallel=args.do_parallel)

    else:
        read_klee(args.file,
                  do_savetemps = args.do_savetemps, 
                  do_parallel=args.do_parallel)

             
                         


# time python klee_reader.py /tmp/cece_1391898175_e46d2a/p.c --do_instrument "1 2" --do_parallel



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
