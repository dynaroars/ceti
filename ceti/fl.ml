(*Fault Localization*)

open Cil
open Vu_common
open Ceti_common
module E = Errormsg
module H = Hashtbl
module P = Printf

type inp_t = string list  (*e.g., *)
type outp_t = string 
type testcase_t = inp_t*outp_t

let string_of_tc (tc:testcase_t) : string = 
  let inp,outp = tc in 
  let inp = string_of_list ~delim:"; " inp in
  "([" ^ inp ^ "]" ^ ", " ^ outp ^ "]"

let string_of_tcs (tcs:testcase_t list) :string = 
  let tcs = L.map string_of_tc tcs in 
  let tcs = string_of_list ~delim:"; " tcs in
  "["^ tcs ^ "]"


let mk_testscript (testscript:string) (tcs:testcase_t list) =
  (*"($1 1071 1029 | diff ref/output.1071.1029 - && (echo "1071 1029" >> $2)) &"*)

  let content = L.map (fun (inp,_) ->
    let inp = string_of_list ~delim:" " inp in

    (*if use & then things are done in parallel but order mesed up*)
    P.sprintf "($1 %s >> $2) ;" inp 
  ) tcs in
  let content = string_of_list ~delim:"\n" content in
  let content = 
    P.sprintf "#!/bin/bash\nulimit -t 1\n%s\nwait\nexit 0\n" content in
      
  if!vdebug then P.printf "Script '%s'\n%s\n%!" testscript content;
  write_file_str testscript content
    

let run_testscript (testscript:string) (prog:string) (prog_output:string) =
  (* "sh script.sh prog prog_output" *)

  (try Unix.unlink prog_output with _ -> () ) ; 

  let prog = P.sprintf "%s" prog in (*"./%s"*)
  let cmd = P.sprintf "sh %s %s %s &> /dev/null" testscript prog prog_output in
  exec_cmd cmd


let mk_run_testscript testscript prog prog_output (tcs:testcase_t list) = 

  assert (not (Sys.file_exists testscript));
  mk_testscript testscript tcs;
  run_testscript testscript prog prog_output


class uTest (filename:string) = object(self)

  val filename = filename

  val mutable mytcs = []
  val mutable mygoods = []
  val mutable mybads = []

  method mytcs   = mytcs
  method mygoods = mygoods
  method mybads  = mybads

  (*read testcases *)
  method get_tcs (inputs:string) (outputs:string) = 
    
    if !vdebug then E.log "Read tcs from '%s' and '%s' for '%s'\n" 
      inputs outputs filename;
    
    let inputs = read_lines inputs in
    let outputs = read_lines outputs in 

    assert (L.length inputs = L.length outputs);
    
    let tcs:testcase_t list = 
      L.fold_left2 (fun acc inp outp ->
	let inp = str_split  inp in
	(try (inp,outp)::acc
	 with _ -> 
	   E.error "Ignore (%s, %s)" (string_of_list inp) outp;
	   acc
	)
      ) [] inputs outputs 
    in
    let tcs = L.rev tcs in

    if L.length tcs = 0 then (ealert "No tcs !"; exit 1);

    if !vdebug then P.printf "|tcs|=%d\n%!" (L.length tcs);
    (*E.log "%s\n" (string_of_tcs tcs);*)

    mytcs <- tcs;
    self#get_goodbad_tcs


  method private get_goodbad_tcs = 
    P.printf "*** Get good/bad tcs ***\n%!";
    
    (*compile and run program on tcs*)
    let prog:string = compile filename in
    
    let testscript =  filename ^ ".sh" in
    let prog_output:string = filename ^ ".routputs" in
    mk_run_testscript testscript prog prog_output mytcs;
    
    (*check if prog passes all inputs:
      If yes then exit. If no then there's bug to fix*)
    let goods,bads = self#compare_outputs prog_output mytcs in 
    let nbads = L.length bads in
    if nbads = 0 then (ealert "All tests passed. Exit!"; exit 0)
    else (ealert "%d/%d tests failed. Processing .." nbads (L.length mytcs));
    
    mygoods <- goods;
    mybads <- bads


  method private compare_outputs 
    (*
      Returns good and bad inputs.
      Good/bad inputs are when expected outputs eq/neq program outputs,
    *)
    (prog_outputs:string) (tcs:testcase_t list): testcase_t list * testcase_t list = 

    let prog_outputs = read_lines prog_outputs in 
    assert (L.length prog_outputs = L.length tcs) ;
    
    let goods, bads = L.partition (
      fun ((_,e_outp),p_outp) -> 
	(try e_outp = p_outp 
	 with _ -> false)
    ) (L.combine tcs prog_outputs) in
    
    let goods,_ = L.split goods in
    let bads,_ =  L.split bads in
    
    goods, bads

end


(******************* Fault Localization *******************)

(*
  walks over AST and preceeds each stmt with a printf that writes out its sid
  create a stmt consisting of 2 Call instructions
  fprintf "_coverage_fout, sid"; 
  fflush();
*)
let stderr_vi = mk_vi ~ftype:(TPtr(TVoid [], [])) "_coverage_fout"

class coverageVisitor = object(self)
  inherit nopCilVisitor

  method private create_fprintf_stmt (sid : sid_t) :stmt = 
  let str = P.sprintf "%d\n" sid in
  let stderr = exp_of_vi stderr_vi in
  let instr1 = mk_call "fprintf" [stderr; Const (CStr(str))] in 
  let instr2 = mk_call "fflush" [stderr] in
  mkStmt (Instr([instr1; instr2]))
    
  method vblock b = 
    let action (b: block) :block= 
      let insert_printf (s: stmt): stmt list = 
	if s.sid > 0 then [self#create_fprintf_stmt s.sid; s]
	else [s]
      in
      let stmts = L.map insert_printf b.bstmts in 
      {b with bstmts = L.flatten stmts}
    in
    ChangeDoChildrenPost(b, action)
      
  method vfunc f = 
    let action (f: fundec) :fundec = 
      (*print 0 when entering main so we know it's a new run*)
      if f.svar.vname = "main" then (
	f.sbody.bstmts <- [self#create_fprintf_stmt 0] @ f.sbody.bstmts
      );
      f
    in
    ChangeDoChildrenPost(f, action)
end

type sscore = int*float (* sscore = (sid,suspicious score) *)
class faultloc 
  (ast:file) 
  (goods:testcase_t list) 
  (bads:testcase_t list) 
  (stmt_ht:(sid_t,stmt*fundec) H.t) = 
object(self)

  val ast = ast
  val goods = goods
  val bads = bads
  val stmt_ht = stmt_ht

  method fl fl_alg min_sscore: sid_t list = 
    E.log "*** Fault Localization ***\n";

    assert (L.length bads > 0) ;
    let sscores:sscore list = 
      if L.length goods = 0 then 
	H.fold (fun sid _ rs -> (sid,min_sscore)::rs) stmt_ht [] 
      else
	let ast_bn =  
	  let tdir = Filename.dirname ast.fileName in
	  let tdir = mkdir_tmp ~temp_dir:tdir "faultloc" "" in
	  Filename.concat tdir (Filename.basename ast.fileName) 
	in
	
	(*create cov file*)
	let fileName_cov = ast_bn ^ ".cov.c"  in
	let fileName_path = ast_bn ^ ".path"  in
	self#coverage (copy_obj ast) fileName_cov fileName_path;
	
	(*compile cov file*)
	let prog:string = compile fileName_cov in
	
	(*run prog to obtain good/bad paths*)
	let path_generic = ast_bn ^ ".path" in
	let path_g = ast_bn ^ ".gpath" in
	let path_b = ast_bn ^ ".bpath" in
	
	(*good path*)
	mk_run_testscript (ast_bn ^ ".g.sh") prog 
	  (ast_bn ^ ".outputs_g_dontcare") goods;
	Unix.rename path_generic path_g;
	
	(*bad path*)
	mk_run_testscript (ast_bn ^ ".b.sh") prog 
	  (ast_bn ^ ".outputs_bad_dontcare") bads;
	Unix.rename path_generic path_b;
	
	let n_g, ht_g = self#analyze_path path_g in
	let n_b, ht_b = self#analyze_path path_b in
	self#compute_sscores fl_alg n_g ht_g n_b ht_b
    in

    (*remove all susp stmts in main, which cannot have anything except call
      to mainQ, everything in main will be deleted when instrumenting main*)
    let idx = ref 0 in 
    let sscores = L.filter (fun (sid,score) -> 
      let s,f = H.find stmt_ht sid in
      if score >= min_sscore && f.svar.vname <> "main" then(
	E.log "%d. sid %d in fun '%s' (score %g)\n%a\n"
	  !idx sid f.svar.vname score dn_stmt s;
	incr idx;
	true
      ) else false
    ) sscores in

    ealert "FL: found %d stmts with sscores >= %g" 
      (L.length sscores) min_sscore;
    
    L.map fst sscores

      
  method private coverage (ast:file) (filename_cov:string) (filename_path:string) = 

  (*add printf stmts*)
  visitCilFileSameGlobals (new coverageVisitor) ast;

  (*add to global
    _coverage_fout = fopen("file.c.path", "ab");
  *)
  let new_global = GVarDecl(stderr_vi, !currentLoc) in
  ast.globals <- new_global :: ast.globals;

  let lhs = var(stderr_vi) in
  let arg1 = Const(CStr(filename_path)) in
  let arg2 = Const(CStr("ab")) in
  let instr = mk_call ~av:(Some lhs) "fopen" [arg1; arg2] in
  let new_s = mkStmt (Instr[instr]) in 

  let fd = getGlobInit ast in
  fd.sbody.bstmts <- new_s :: fd.sbody.bstmts;
  
  write_src filename_cov  ast

  (* Analyze execution path *)    
  method private analyze_path (filename:string): int * (int,int) H.t= 

    if !vdebug then E.log "** Analyze exe path '%s'\n" filename;

    let tc_ctr = ref 0 in
    let ht_stat = H.create 1024 in 
    let mem = H.create 1024 in 
    let lines = read_lines filename in 
    L.iter(fun line -> 
      let sid = int_of_string line in 
      if sid = 0 then (
	incr tc_ctr;
	H.clear mem;
      )
      else (
	let sid_tc = (sid, !tc_ctr) in
	if not (H.mem mem sid_tc) then (
	  H.add mem sid_tc ();
	  
	  let n_occurs = 
	    if not (H.mem ht_stat sid) then 1
	    else succ (H.find ht_stat sid)
	      
	  in H.replace ht_stat sid n_occurs
	)
      )
    )lines;
    !tc_ctr, ht_stat


  method private compute_sscores 
    (fl_alg:int)
    (n_g:int) (ht_g:(int,int) H.t) 
    (n_b:int) (ht_b:(int,int) H.t) 
    : sscore list =
    
    assert(n_g <> 0);
    assert(n_b <> 0);
    
    let alg = if fl_alg = 1 
      then self#alg_ochiai else self#alg_tarantula in

    let ht_sids = H.create 1024 in 
    let set_sids ht =
      H.iter (fun sid _ ->
	if not (H.mem ht_sids sid) then H.add ht_sids sid ()
      ) ht;
    in
    set_sids ht_g ;
    set_sids ht_b ;

    let n_g = float_of_int n_g in
    let n_b = float_of_int n_b in

    let rs = H.fold (fun sid _ rs ->
      let get_n_occur sid (ht: (int,int) H.t) : float=
	if H.mem ht sid then float_of_int(H.find ht sid) else 0. 
      in
      let good = get_n_occur sid ht_g in
      let bad = get_n_occur sid ht_b in
      let score =  alg bad n_b good n_g in
      
      (sid,score)::rs

    ) ht_sids [] in 

    let rs = L.sort (fun (_,score1) (_,score2) -> compare score2 score1) rs in
    rs


  (*
    Tarantula (Jones & Harrold '05)
    score(s) = (bad(s)/total_bad) / (bad(s)/total_bad + good(s)/total_good)
    
    Ochiai (Abreu et. al '07)
    score(s) = bad(s)/sqrt(total_bad*(bad(s)+good(s)))
  *)

  method private alg_tarantula bad tbad good tgood =
      (bad /. tbad) /. ((good /. tgood) +. (bad /. tbad))

  method private alg_ochiai bad tbad good tgood = 
      bad /. sqrt(tbad *. (bad +. good))
    
end


let fl_alg = ref 1 (*1: ochiai, ow: tarantula*)
let min_sscore:float ref = ref 0.5
let top_n_sids:int ref = ref 10


