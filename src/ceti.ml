(*ocamlfind ocamlopt -package str,batteries,cil  cil_common.cmx -linkpkg -thread tf.ml*)
(*Takes in a preprocess file , e.g., cil.i 
for i in {1..41}; do cilly bug$i.c --save-temps --noPrintLn --useLogicalOperators; done
 *)

(*open Ceti_common*)
open Cil
module E = Errormsg
module L = List
module H = Hashtbl 
module P = Printf
module FL = Fl

module CC = Cil_common
module VC = Vu_common
module ST = Settings
module MC = Common
	      
(* let forceOption (ao : 'a option) : 'a = *)
(*   match ao with  | Some a -> a | None -> raise(Failure "forceOption") *)

(*filename formats*)

let group_sids (sids:CC.sid_t list) (l:MC.spy_t list): MC.spy_t list = 

  let l0,l1 = L.partition (fun (sids',_,_,_) -> 
			   assert (L.length sids' = 1);
			   L.mem (L.hd sids') sids) l 
  in

  let l1 = L.map (fun (sids,t,l,i) -> (sids,t,l,i)) l1 in
  if L.length l0 = 0 then
    l1
  else
    let _,t,l,i = L.hd l0 in
    let sids':CC.sid_t list list = L.map (fun (s,_,_,_) -> s) l0 in 
    [(L.flatten sids',t,l,i)]@l1

(* specific options for this program *)
let fl_sids = ref [] (*manually provide fault loc info*)

let no_global_vars = ref false
let no_parallel = ref false
let no_bugfix = ref false
let no_stop = ref false

let only_synthesis = ref false
let only_spy = ref false
let only_peek = ref false (*for debugging only, peeking at specific stmt*)
let python_script = "kl.py" (*name of the python script, must be in same dir*)


(********************** PROTOTYPE **********************)

let () = begin
    E.colorFlag := true;

    let filename = ref "" in
    let inputs   = ref "" in
    let outputs  = ref "" in 
    let version = P.sprintf "%s (%s) %f (CIL version %s)" 
			    ST.progname ST.progname_long ST.progversion cilVersion 
    in 

    let arg_descrs = [
      "--debug", Arg.Set VC.vdebug, 
      P.sprintf " shows debug info (default %b)" !VC.vdebug;
      
      "--no_parallel", Arg.Set no_parallel, 
      P.sprintf " don't use multiprocessing (default %b)" !no_parallel;
      
      "--no_bugfix", Arg.Set no_bugfix, 
      P.sprintf " don't do bugfix (default %b)" !no_bugfix;
      
      "--no_stop", Arg.Set no_stop, 
      P.sprintf " don't stop after finding a fix (default %b)" !no_stop;
      
      "--no_global_vars", Arg.Set no_global_vars,
      P.sprintf " don't consider global variables when modify stmts (default %b)" 
		!no_global_vars;

      "--fl_sids", Arg.String (fun s -> 
			       fl_sids := L.map int_of_string (VC.str_split s)),
      (P.sprintf "%s" 
		 " don't run fault loc, use the given suspicious stmts, " ^
	 "e.g., --fl_sids \"1 3 7\".");
      
      "--fl_alg", Arg.Set_int FL.fl_alg,
      P.sprintf
	" use fault loc algorithm: 1 Ochia, 2 Tarantula (default %d)" 
	!FL.fl_alg;
      
      "--top_n_sids", Arg.Set_int FL.top_n_sids,
      P.sprintf " consider this # of suspicious stmts (default %d)" 
		!FL.top_n_sids;
      
      "--min_sscore", Arg.Set_float FL.min_sscore,
      P.sprintf " fix suspicious stmts with at least this score (default %g)" 
		!FL.min_sscore;
      
      "--tpl_ids", Arg.String (
		       fun s -> ST.tpl_ids :=
				  L.map int_of_string (VC.str_split s)
		     ),
      " only use these bugfix template ids, e.g., --tpl_ids \"1 3\"";
      
      "--tpl_level", Arg.Set_int ST.tpl_level,
      P.sprintf " fix tpls up to and including this level (default %d)" 
		!ST.tpl_level;
      
      "--only_spy", Arg.Set only_spy, 
      P.sprintf " only do spy (default %b)" 
		!only_spy;

      "--only_peek", Arg.Set only_peek, 
      P.sprintf " only do peek the stmt given in --sid (default %b)" 
		!only_peek;
      
    ] in
    
    let handle_arg s =
      if !filename = "" then (
	VC.chk_exist s ~msg:"require filename"; filename := s
      )
      else if !inputs = "" then inputs := s
      else if !outputs = "" then outputs := s
      else raise (Arg.Bad "too many input args")
    in
    
    let usage = P.sprintf "%s\nusage: ceti src in_file out_file [options]\n" version in

    Arg.parse (Arg.align arg_descrs) handle_arg usage;
    
    initCIL();
    Cil.lineDirectiveStyle := None;
    Cprint.printLn := false; (*don't print line #*)

    (* for Cil to retain &&, ||, ?: instead of transforming them to If stmts *)
    Cil.useLogicalOperators := true; 


    (*** some initialization, getting testcases etc***)
    (*
    Note: src (filename) must be preprocessed by cil by running 
    cilly src.c --save-temps; the result is called src.cil.c

    Also, must have certain format  
    void main(..) {
    printf(mainQ);...
    }
     *)
    
    VC.chk_exist !inputs  ~msg:"require inputs file";
    VC.chk_exist !outputs ~msg:"require outputs file";

    (*create a temp dir to process files*)
    let tdir = VC.mkdir_tmp ~temp_dir:"/var/tmp" ST.progname "" in
    let fn' = P.sprintf "%s/%s" tdir (Filename.basename !filename) in 
    VC.exec_cmd (P.sprintf "cp %s %s" !filename fn');
    
    let filename,inputs,outputs = fn', !inputs, !outputs in
    at_exit (fun () ->  E.log "Note: temp files created in dir '%s'\n" tdir);

    let tcObj = (new FL.uTest) filename in
    tcObj#get_tcs inputs outputs;
    
    let ast = Frontc.parse filename () in 

    visitCilFileSameGlobals (new CC.everyVisitor) ast;
    visitCilFileSameGlobals (new FL.breakCondVisitor :> cilVisitor) ast;

    let stmt_ht:(CC.sid_t,stmt*fundec) H.t =
      CC.mk_stmt_ht ast CC.can_modify ~create_stmt_ids:true in
    CC.write_src (ast.fileName ^ ".preproc.c") ast;

    if !only_peek then (
      ignore (visitCilFileSameGlobals ((new MC.peekVisitor) !ST.sids) ast);
      exit 0);

    (* determine if file contains synthesis stmts*)
    let syn_sids = MC.find_synstmts ast in 
    only_synthesis := L.length syn_sids > 0 ;

    let perform_s = ref "" in 
    if !only_synthesis then (
      perform_s := "Synthesis";
      ST.sids := syn_sids;
      ST.tpl_ids := [3] (*CONST template*)
    )
    else ( 
      perform_s := "BugFix";
      (*** fault localization ***)

      let fl_sids:CC.sid_t list = 
	if L.length !fl_sids > 0 then !fl_sids 
	else (
	  let flVis = (new FL.faultloc) ast tcObj#mygoods tcObj#mybads stmt_ht in
	  let ssids = flVis#get_susp_sids !FL.fl_alg in

	  (*remove all susp stmts in main, which cannot have anything except call
	  to mainQ, everything in main will be deleted when instrumenting main*)

	  let idx = ref 0 in 
	  let ssids = L.filter (
			  fun (sid,score) -> 
			  let s,f = H.find stmt_ht sid in
			  if score >= !FL.min_sscore && f.svar.vname <> "main" then(
			    E.log "%d. sid %d in fun '%s' (score %g)\n%a\n"
				  !idx sid f.svar.vname score dn_stmt s;
			    incr idx;
			    true
			  ) else false
			) ssids in
	  CC.ealert "FL: found %d ssids with sscores >= %g" 
		    (L.length ssids) !FL.min_sscore;
	  
	  let ssids = VC.take !FL.top_n_sids ssids in (*consider only n top susp stmts*)
	  L.map fst ssids
	)
      in
      ST.sids := fl_sids
    );

    CC.ealert "Perform ** %s **" !perform_s;

    let sids = !ST.sids in
    if L.length sids = 0 then (CC.ealert "No suspicious stmts !"; exit 0);
    
    (*** transformation and bug fixing ***)
    (* find mainQ *)
    let mainQ_fd = MC.find_fun ast ST.mainfunname in
    
    if not !no_global_vars then (
      iterGlobals ast (function 
			|GVar (vi,_,_) -> ST.extra_vars := vi::!ST.extra_vars 
			|_ -> ());
      
      if !VC.vdebug then 
	E.log "Consider %d gloval vars [%s]\n" 
	      (L.length !ST.extra_vars) 
	      (VC.string_of_list (L.map (fun vi -> vi.vname) !ST.extra_vars));
    );

    (*spy on suspicious stmts*)
    if !VC.vdebug then E.log "Spy %d sids: [%s] with tpl_ids: [%s]\n" 
			     (L.length sids) (VC.string_of_ints sids)
			     (VC.string_of_ints !ST.tpl_ids);

    let rs = L.map (MC.spy ast.fileName stmt_ht) sids in
    let rs' = L.filter (function |[] -> false |_ -> true) rs in
    let rs = L.flatten rs' in 
    CC.ealert "Spy: Got %d info from %d sids" (L.length rs) (L.length rs');
    if (L.length rs) = 0 then (CC.ealert "No spied info. Exit!"; exit 0);

    let rs = 
      if !only_synthesis then 
	group_sids sids rs (*synthesize multiple statements simultenously*)
      else
	rs
    in
    let rs = L.map MC.string_of_spys rs in

    (*call Python script to do transformation*)
    let rs = String.concat "; " rs in
    let kr_opts = [
      if !VC.vdebug then "--debug" else "";
      if !no_parallel then "--no_parallel" else "";
      if !no_bugfix then  "--no_bugfix"  else "";
      if !no_stop then "--no_stop" else ""
    ] in
    let kr_opts = String.concat " " (L.filter (fun o -> o <> "") kr_opts) in

    let cmd = P.sprintf "python2.7 %s %s --do_tb \"%s\" %s"
			python_script ast.fileName rs kr_opts in

    if !only_spy then exit 0;

    (*write info to disk for parallelism use*)
    VC.write_file_bin (ST.ginfo_s ast.fileName) (ast,mainQ_fd,tcObj#mytcs);
    VC.exec_cmd cmd
		

  end

(*IMPORTANT: main must be empty and only call mainQ
TODO: after getting everything working again:  no need to write vs arr to disk, can just reconstruct it from main_fd
*)
