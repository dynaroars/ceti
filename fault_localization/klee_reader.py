#!/usr/bin/env python
import subprocess as sp
import os
import sys
import shutil

vdebug = False

def instrument_worker(src, sid, tpl, xinfo, idxs):
    #$ ./tf /tmp/cece_1392070907_eedfba/p.c 
    #--do_standalone --ssid 3 --tpl 1 --xinfo z3_c0 --idxs "0 1"
    
    if vdebug: print ('KR: *** create {} sid {} tpl {} xinfo {} idxs {} ***'
                      .format(src,tpl,sid,xinfo,idxs))
    
    cmd = ('./tf {} --do_standalone --ssid {} --tpl {} --idxs "{}" --xinfo {}{}'
           .format(src,sid,tpl,idxs,xinfo, " --debug" if vdebug else ""))
                   
    if vdebug: print "$ {}".format(cmd)
    proc = sp.Popen(cmd,shell=True,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    rs,rs_err = proc.communicate()

    assert not rs, rs
    if vdebug: print rs_err

    if "error" in rs_err or "write_src" not in rs_err:
        print "instrumentation failed '{}' !!".format(cmd)
        raise AssertionError

    #get the created file name 
    #write_src: "/tmp/cece_1392071927_eeea2d/p.bug2.c.s3.z3_c5.tf.c"
    #Alert: Transform success: @@ '/tmp/cece_4b2065/q.bug2.c.s1.t5_z3_c1.tf.c' @@  __cil_tmp4 = (x || y) || z; @@ __cil_tmp4 = (x || y) && z;

    rs_file = ""
    old_stmt = ""
    new_stmt = ""

    for line in rs_err.split("\n"):
        if "success:" in line: 
            line = line.split("##")
            assert len(line) == 4
            line = [l.strip() for l in line[1:]]
            rs_file = line[0][1:][:-1]
            old_stmt = line[1]
            new_stmt = line[2]
            break
        
    return rs_file,old_stmt,new_stmt

#compile file then run klee on the resulting object file
def read_klee_worker (src):
    if vdebug: print "KR: *** run klee on {} ***".format(src)

    #compile file with llvm
    include_path = "~/Src/Devel/KLEE/klee/include"
    llvm_opts =  "--optimize -emit-llvm -c"
    obj = os.path.splitext(src)[0] + os.extsep + 'o'
    
    cmd = "llvm-gcc -I {} {} {} -o {}".format(include_path,llvm_opts,src,obj)
    if vdebug: print "$ {}".format(cmd)

    proc = sp.Popen(cmd,shell=True,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    rs,rs_err = proc.communicate()

    assert not rs, rs
    if "llvm-gcc" in rs_err or "error" in rs_err:
        print 'compile error:\n', rs_err
        return None
    

    #run klee and monitor its output
    klee_outdir = "{}-klee-out".format(obj)
    if os.path.exists(klee_outdir): shutil.rmtree(klee_outdir)

    klee_opts = \
        "--allow-external-sym-calls "\
        "-optimize "\
        "--max-time=600. "\
        "-output-dir={}".format(klee_outdir)

    cmd = "klee {} {}".format(klee_opts,obj)
    if vdebug: print "$ {}".format(cmd)
    proc = sp.Popen(cmd,shell=True,stdout=sp.PIPE, stderr=sp.STDOUT)

    ignores_done = ['KLEE: done: total instructions',
                    'KLEE: done: completed paths',
                    'KLEE: done: generated tests']

    ignores_run = [
        'KLEE: WARNING: undefined reference to function: printf',
        'KLEE: WARNING ONCE: calling external: printf',
        'KLEE: ERROR: ASSERTION FAIL: 0']

    while proc.poll() is None:
        line = proc.stdout.readline()
        line = line.strip()
        if line:
            sys.stdout.flush()
            if all(x not in line for x in ignores_run + ignores_done):
                if vdebug: print 'stdout:', line

            
            if "KLEE: ERROR" in line and "ASSERTION FAIL: 0" in line: 
                break
        
            
    rs,rs_err = proc.communicate()

    assert not rs_err, rs_err

    ignores_miscs = ['KLEE: NOTE: now ignoring this error at this location',
                     'GOAL: ']

    if rs:
        for line in rs.split('\n'):
            if line:
                if all(x not in line for x in ignores_done + ignores_miscs):
                    if vdebug: print 'rs:', line
                
                #GOAL: uk_0 0, uk_1 0, uk_2 1
                if 'GOAL' in line:
                    s = line[line.find(':')+1:].strip()
                    s = '{}'.format(s if s else "no uks")
                    return s

    return None
        

def tbf_worker(src, sid, tpl, cid, idxs, no_bugfix):
    idxs = " ".join(map(str,idxs))
    xinfo = "t{}_z{}_c{}".format(tpl,len(idxs),cid)

    r = instrument_worker(src, sid, tpl, xinfo, idxs)
    assert len(r) == 3
    fn,old_stmt,new_stmt = r

    if fn : #transform success
        if no_bugfix: 
            return "{}, {}, {}".format(fn,old_stmt,new_stmt)
        else:
            rk_r = read_klee_worker(fn)
            if rk_r:
                return "{}: {} ===> {} ===> {}".format(fn,old_stmt,new_stmt,rk_r)
            

    return None


def tbf(src, combs, no_bugfix, no_parallel, no_break):
    #e.g., combs = [(1,1,5), (5,2,2), (9,2,5)]

   
    import itertools
    max_comb_siz = 2

    combs_ = []
    for sid,tpl,l in combs:
        if tpl == 1: #VS
            assert len(l) == 1, len(l)
            l = l[0]
            for siz in range(max_comb_siz+1):
                cs = itertools.combinations(range(l),siz)
                for i,c in enumerate(cs):
                    combs_.append((sid,tpl,i,list(c)))

        elif tpl == 5:  #BOPS
            ls = [range(l_) for l_ in l]
            cs = itertools.product(*ls)
            for i,c in enumerate(cs):
                combs_.append((sid,tpl,i,list(c)))

        elif tpl == 3: #CONST
            assert len(l) == 1, len(l)
            combs_.append((sid,tpl,0,l))

        else:
            assert False, "unknown template id {}".format(tpl)
                              

    # print len(combs_)
    # print combs_
    # assert False 

    def wprocess(tasks,V,Q):

        if no_break:
            rs = [tbf_worker(src,sid,tpl,cid,idxs,no_bugfix) 
                  for sid,tpl,cid,idxs in tasks]
            if Q is None:
                return rs
            else:
                Q.put(rs)
                return None

        else: #break after finding a fix 
            rs = []
            if Q is None:  #no multiprocessing
                for sid,tpl,cid,idxs in tasks:
                    r = tbf_worker(src,sid,tpl,cid,idxs,no_bugfix)
                    if r: 
                        if vdebug: print "sol found, break !"
                        rs.append(r)
                        break
                return rs

            else: #multiprocessing
                for sid,tpl,cid,idxs in tasks:
                    if V.value > 0: 
                        if vdebug: print "sol found, break !"
                        break
                    else:
                        r = tbf_worker(src,sid,tpl,cid,idxs,no_bugfix)
                        if r: 
                            rs.append(r)
                            V.value = 1
                            break

                Q.put(rs)
                return None
    
    # def wprocess_fake(tasks,V,Q):
    #     if len(tasks) == 6:
    #         import time
    #         time.sleep(2)

    #     if Q is None:
    #         return range(len(tasks))
    #     else:
    #         Q.put(range(len(tasks)))
    #         return None

    ###


    tasks = combs_

    if no_parallel:
        wrs = wprocess(tasks,V=None,Q=None)
        
    else:
        from vu_common import get_workloads
        from multiprocessing import (Process, Queue, Value,
                                     current_process, cpu_count)

        Q = Queue()
        V = Value("i",0)

        workloads = get_workloads(tasks,max_nprocesses=cpu_count(),chunksiz=1)

        print ("KR: tbf tasks {}, workloads 'tbf' {}: {}"
               .format(len(tasks), len(workloads),map(len,workloads)))
        workers = [Process(target=wprocess,args=(wl,V,Q)) for wl in workloads]

        for w in workers: w.start()
        wrs = []
        for i,_ in enumerate(workers):
            wrs.extend(Q.get())
        

    wrs = [r for r in wrs if r]
    print ("KR summary (bugfix: {}, parallel: {}, break: {}):"\
               "'{}', tbf {} / {}"
           .format(not no_bugfix, 
                   not no_parallel, 
                   not no_break,
                   src,len(wrs),len(tasks)))

    for i,r in enumerate(wrs):
        print "{}. {}".format(i+1,r)


#template 1: VS
#(tpl_id,ssid,vsize) where vsize is th length of available variables where we'll create a bunch of combinations from

#template 3: CONSTS
#(tpl_id,ssid,n_const) where nconsts is the # consts , won't do anything with this number

if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser()
    
    aparser.add_argument("file", help="src code")
 
    aparser.add_argument("--do_tbf",
                         help='transform and bug fix, e.g., --do_tbf "(1,1,5); (5,1,2); (9,1,5)"',
                         dest='combs',
                         action="store")

    aparser.add_argument("--no_parallel",
                         help="don't use multiprocessing",
                         action="store_true")

    aparser.add_argument("--no_bugfix",
                         help="don't run klee to find fixes",
                         action="store_true")

    aparser.add_argument("--no_break",
                         help="don't stop bugfix process after a sol is found ",
                         action="store_true")

    aparser.add_argument("--debug",
                         help="shows debug info ",
                         action="store_true")
                         

    args = aparser.parse_args()

    vdebug = args.debug

    assert args.combs         #[(1,5), (5,2), (9,5)]
    combs = [comb.strip() for comb in args.combs.split(";")]
    combs = [comb[1:][:-1] for comb in combs] #remove ( )
    combs = [comb.split(',') for comb in combs]


    combs = [(int(comb[0]),int(comb[1]),
              [int(c) for c in comb[2].strip().split()])
             for comb in combs]

    tbf(args.file, combs, 
        no_bugfix=args.no_bugfix,
        no_parallel=args.no_parallel,
        no_break=args.no_break)

             
                         


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
