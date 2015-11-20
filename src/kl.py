#!/usr/bin/env python
import subprocess as sp
import os
import sys
import shutil

vdebug = False

#parallel stuff
def get_workloads(tasks,max_nprocesses,chunksiz):
    """
    >>> wls = get_workloads(range(12),7,1); wls
    [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9], [10, 11]]


    >>> wls = get_workloads(range(12),5,2); wls
    [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9, 10, 11]]

    >>> wls = get_workloads(range(20),7,2); wls
    [[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11], [12, 13, 14], [15, 16, 17], [18, 19]]


    >>> wls = get_workloads(range(20),20,2); wls
    [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9], [10, 11], [12, 13], [14, 15], [16, 17], [18, 19]]

    """

    if __debug__:
        assert len(tasks) >= 1, tasks
        assert max_nprocesses >= 1, max_nprocesses
        assert chunksiz >= 1, chunksiz

    #determine # of processes
    ntasks = len(tasks)
    nprocesses = int(round(ntasks/float(chunksiz)))
    if nprocesses > max_nprocesses:
        nprocesses = max_nprocesses


    #determine workloads 
    cs = int(round(ntasks/float(nprocesses)))
    workloads = []
    for i in range(nprocesses):
        s = i*cs
        e = s+cs if i < nprocesses-1 else ntasks
        wl = tasks[s:e]
        if wl:  #could be 0, e.g., get_workloads(range(12),7,1)
            workloads.append(wl)

    return workloads



#Template Ids
TPL_VS     = 1
TPL_CONST  = 3
TPL_BOPS_1 = 5
TPL_BOPS_2 = 6
TPL_BOPS_PR = 7

#parse data based on template
def get_data(tpl, data_l):
    import itertools
    rs = []

    #[n], n consts ... not doing anything with this
    if tpl == TPL_CONST:
        assert len(data_l) == 1, len(data_l)
        rs.append((0, data_l))

    #[n], from n vars make comb of sizes 0 .. max_comb_size 
    elif tpl == TPL_VS:  
        max_comb_siz = 2 
        assert len(data_l) == 1, len(data_l)
        data_l = data_l[0]
        for siz in range(max_comb_siz + 1):
            cs = itertools.combinations(range(data_l),siz)
            for i,c in enumerate(cs):
                rs.append((i, list(c)))

    #[n], n ops
    #make n list [1] ,.., [n]
    elif tpl == TPL_BOPS_PR:
        assert len(data_l) == 1, len(data_l)
        for i in range(data_l[0]):
            rs.append((i,[i+1]))

    #[l,m,n,..] lengths l,m,n of 1st,2nd,3rd,.. arrays
    elif tpl == TPL_BOPS_1 or tpl == TPL_BOPS_2:
        assert len(data_l) > 0, len(data_l)

        ls = [range(l) for l in data_l]
        cs = itertools.product(*ls)
        for i,c in enumerate(cs):
            rs.append((i, list(c)))

    else:
        raise AssertionError("unknown template id {}".format(tpl))

    return rs

#call ocaml prog to transform file
def worker_transform(wid, src, sids, tpl, xinfo, idxs):
    #$ ./ceti /tmp/cece_1392070907_eedfba/p.c 
    #--only_transform --sids "3" --tpl 1 --xinfo z3_c0 --idxs "0 1"
    
    if vdebug: print ('worker {}: transform {} sids {} tpl {} xinfo {} idxs {} ***'
                      .format(wid, src,tpl,sids,xinfo,idxs))
    cmd = ('./ceti {} '
           '--only_transform --sids "{}" --tpl {} --idxs "{}" --xinfo {}{}'
           .format(src,sids,tpl,idxs,xinfo, 
                   " --debug" if vdebug else ""))
                   
    if vdebug: print "$ {}".format(cmd)
    proc = sp.Popen(cmd,shell=True,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    rs,rs_err = proc.communicate()

    #assert not rs, rs

    if vdebug: print rs_err[:-1] if rs_err.endswith("\n") else rs_err

    if "error" in rs_err or "success" not in rs_err:
        print "worker {}: transform failed '{}' !".format(wid, cmd)
        print rs_err
        raise AssertionError


    #obtained the created result
    #Alert: Transform success: ## '/tmp/cece_4b2065/q.bug2.c.s1.t5_z3_c1.ceti.c' ##  __cil_tmp4 = (x || y) || z; ## __cil_tmp4 = (x || y) && z;

    rs_file, old_stmt, new_stmt = "", "", ""

    for line in rs_err.split("\n"):
        if "success:" in line: 
            line = line.split("##")
            assert len(line) == 4 #must has 4 parts
            line = [l.strip() for l in line[1:]]
            rs_file = line[0][1:][:-1] #remove ' ' from filename
            old_stmt = line[1]
            new_stmt = line[2]
            break
    
    return rs_file,old_stmt,new_stmt

#compile transformed file and run run klee on it
def worker_klee (wid, src):
    if vdebug: print "worker {}: run klee on {} ***".format(wid, src)

    #compile file with llvm
    include_path = "~/Src/Devel/KLEE/klee/include"
    #llvm_opts =  "--optimize -emit-llvm -c"
    llvm_opts =  "-emit-llvm -c"
    obj = os.path.splitext(src)[0] + os.extsep + 'o'
    
    #cmd = "llvm-gcc -I {} {} {} -o {}".format(include_path,llvm_opts,src,obj)
    cmd = "clang -I {} {} {} -o {}".format(include_path,llvm_opts,src,obj)
    if vdebug: print "$ {}".format(cmd)

    proc = sp.Popen(cmd,shell=True,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    rs,rs_err = proc.communicate()

    assert not rs, rs
    #if "llvm-gcc" in rs_err or "error" in rs_err:
    if "clang" in rs_err or "error" in rs_err:
        print 'worker {}: compile error:\n{}'.format(wid,rs_err)
        return None
    

    #run klee and monitor its output
    klee_outdir = "{}-klee-out".format(obj)
    if os.path.exists(klee_outdir): shutil.rmtree(klee_outdir)

    timeout = 10
    klee_opts = ("--allow-external-sym-calls "
                 "-optimize "
                 "--max-time={}. "
                 "-output-dir={} "
                 .format(timeout,klee_outdir))

    cmd = "klee {} {}".format(klee_opts,obj).strip()

    if vdebug: print "$ {}".format(cmd)
    proc = sp.Popen(cmd,shell=True,stdout=sp.PIPE, stderr=sp.STDOUT)

    ignores_done = ['KLEE: done: total instructions',
                    'KLEE: done: completed paths',
                    'KLEE: done: generated tests']

    ignores_run = [ 
        'KLEE: WARNING: undefined reference to function: printf',
        'KLEE: WARNING ONCE: calling external: printf',
        'KLEE: ERROR: ASSERTION FAIL: 0',
        'KLEE: ERROR: (location information missing) ASSERTION FAIL: 0'
        ]

    while proc.poll() is None:
        line = proc.stdout.readline()
        line = line.strip()
        if line:
            sys.stdout.flush()
            if all(x not in line for x in ignores_run + ignores_done):
                if vdebug: print 'worker {}: stdout: {}'.format(wid,line)

            if 'KLEE: HaltTimer invoked' in line:
                print 'worker {}: stdout: {}, timeout {}'.format(wid, src, timeout)

            if "KLEE: ERROR" in line and "ASSERTION FAIL: 0" in line: 
                print 'worker {}: found fix for {}'.format(wid, src)
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
        

def worker_tb(wid, src, sids, tpl, cid, idxs, no_bugfix):
    sids = " ".join(map(str,sids))
    idxs = " ".join(map(str,idxs))
    xinfo = "t{}_z{}_c{}".format(tpl,len(idxs),cid)

    r = worker_transform(wid, src, sids, tpl, xinfo, idxs)
    assert len(r) == 3
    src,old_stmt,new_stmt = r

    if src : #transform success
        if no_bugfix: 
            return "{}, {}, {}".format(src,old_stmt,new_stmt)
        else:
            rk_r = worker_klee(wid, src)
            if rk_r:
                return "{}: {} ===> {} ===> {}".format(src,old_stmt,new_stmt,rk_r)
            

    return None


#these wprocesses run in parallel but their own tasks are done sequentially
def wprocess(wid, tasks, no_stop,no_bugfix,V,Q):

    tasks = sorted(tasks, 
                   key=lambda (src,sids,tpl,tpl_level,cid,idxs): 
                   (tpl_level, len(idxs)))
                   

    if no_stop:
        rs = [worker_tb(wid, src, sids, tpl, cid, idxs, no_bugfix) 
              for src, sids, tpl, tpl_level, cid, idxs in tasks]

        if Q is None: #no parallel
            return rs
        else:
            Q.put(rs) #parallel
            return None

    else: #break after finding a fix 
        rs = []
        if Q is None:  #no parallel
            for src, sids, tpl, tpl_level, cid, idxs in tasks:
                r = worker_tb(wid, src, sids, tpl, cid, idxs, no_bugfix)
                if r: 
                    if vdebug: print "worker {}: sol found, break !".format(wid)
                    rs.append(r)
                    break
            return rs

        else: #parallel
            for src, sids, tpl, tpl_level, cid, idxs in tasks:
                if V.value > 0: 
                    if vdebug: print "worker {}: sol found, break !".format(wid)
                    break
                else:
                    r = worker_tb(wid, src, sids, tpl, cid, idxs, no_bugfix)
                    if r: 
                        rs.append(r)
                        V.value = V.value + 1

            Q.put(rs)
            return None



def tb(src, combs, no_bugfix, no_parallel, no_stop):

    tasks = []
    for sids,tpl,tpl_level,l in combs:
        rs_ = get_data(tpl,l)
        rs_ = [(src, sids, tpl, tpl_level) + r for r in rs_]
        tasks.extend(rs_)

    from random import shuffle
    shuffle(tasks)

    print "KR: tasks {}".format(len(tasks))

    if no_parallel:
        wrs = wprocess(0, tasks, no_stop, no_bugfix, V=None, Q=None)
        
    else: #parallel
        from multiprocessing import (Process, Queue, Value,
                                     current_process, cpu_count)
        Q = Queue()
        V = Value("i",0)

        workloads = get_workloads(tasks, max_nprocesses=cpu_count(), chunksiz=2)
        print ("workloads {}: {}".format(len(workloads), map(len,workloads)))
               
        workers = [Process(target=wprocess,args=(i,wl,no_stop, no_bugfix, V, Q)) 
                   for i,wl in enumerate(workloads)]

        for w in workers: w.start()
        wrs = []
        for i,_ in enumerate(workers): 
            wrs.extend(Q.get())
        
    wrs = [r for r in wrs if r]
    
    rs = "\n".join(["{}. {}".format(i,r) for i,r in enumerate(wrs)])

    print ("KR: summary "
           "(bugfix: {}, stop after a repair found: {}, parallel: {}), "
           "'{}', {} / {}\n"
           "{}"
           .format(not no_bugfix, not no_stop, not no_parallel, 
                   src,len(wrs),len(tasks),
                   rs))


if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser()
    
    aparser.add_argument("file", help="file name")

    aparser.add_argument("--debug",
                         help="shows debug info ",
                         action="store_true")

    aparser.add_argument("--do_tb",
                         help='transform file and bug fix, e.g.,'\
                             '--do_tb "(1,1,5); (5,1,2); (9,1,5)"',
                         dest='clist',
                         action="store")
                         
    aparser.add_argument("--no_parallel",
                         help="don't use multiprocessing",
                         action="store_true")
                        
    aparser.add_argument("--no_bugfix",
                         help="don't run klee to find fixes",
                         action="store_true")
                         
    aparser.add_argument("--no_stop",
                         action="store_true",
                         help="don't stop after finding a fix")

    args = aparser.parse_args()

    vdebug = args.debug

    assert args.clist         #[(1,5), (5,2), (9,5)]
    split_ = lambda l: l.strip().split() #1 2 3 -> [1,2,3]

    clist = [c.strip() for c in args.clist.split(";")]
    clist = [c[1:][:-1] for c in clist] #remove ( )
    clist = [c.split(',') for c in clist]

    clist = [([int(c_) for c_ in split_(c[0])], #stmt id
              int(c[1]), #template id
              int(c[2]), #template level
              [int(c_) for c_ in split_(c[3])]) #data
             for c in clist]
    print clist
    
    tb(args.file,
        clist,
        no_bugfix=args.no_bugfix,
        no_parallel=args.no_parallel,
        no_stop=args.no_stop)
