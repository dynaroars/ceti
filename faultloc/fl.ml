(*Fault Localization*)

open Cil
open Vu_common

module E = Errormsg
module H = Hashtbl
module P = Printf
module CC = Cil_common

(*break conditional / loop guard to 
  if(complex_exp) to 
  int tmp = complex_exp; 
  if(tmp) 
  Assigning id's to stmts 
*)

(*Todo: 
  - coverageVisitor already in cil_common (not exactly the same though)
  - Also merge faultloc.ml from ~/Dropbox/config/alg here 
*)

class breakCondVisitor = object(self)
  inherit nopCilVisitor

  val mutable cur_fd = None
    
  method vfunc f = cur_fd <- (Some f); DoChildren

  method private mk_stmt s e loc: lval*stmt= 
    let fd = match cur_fd with 
      | Some f -> f | None -> E.s(E.error "not in a function") in
    let v:lval = var(makeTempVar fd (typeOf e)) in
    let i:instr = Set(v,e,loc) in
    v, {s with skind = Instr[i]} 

  (* method private can_break e =  *)
  (*   match e with  *)
  (*   (\*|Const _ -> false (\*put this in will make things fast, but might not fix a few bugs*\)*\) *)
  (*   |Lval _ -> true *)
  (*   | _-> true *)


  method vblock b = 
    let action (b: block) : block = 

      let rec change_stmt (s: stmt) : stmt list = 
	match s.skind with
	(*if (e){b1;}{b2;} ->  int t = e; if (t){b1;}{b2;} *)
	|If(e,b1,b2,loc) -> 
	  let v, s1 = self#mk_stmt s e loc in
	  let s1s = change_stmt s1 in
	  let s2 = mkStmt (If (Lval v,b1,b2,loc)) in
	  let rs = s1s@[s2] in
	    (* if !vdebug then E.log "(If) break %a\n ton%s\n"  *)
	    (*   dn_stmt s (String.concat "\n" (L.map string_of_stmt rs)); *)
	  
	  rs
	    
	(*return e; ->  int t = e; return t;*)
	|Return(Some e,loc) ->
	  let v, s1 = self#mk_stmt s e loc in
	  let s1s = change_stmt s1 in
	  
	  let s2 = mkStmt (Return (Some (Lval v), loc)) in
	  let rs =  s1s@[s2] in
		  (* if !vdebug then E.log "(Return) break %a\nto\n%s\n"  *)
		  (*   dn_stmt s (String.concat "\n" (L.map string_of_stmt rs)); *)
	  
	  rs
	    
	(*x = a?b:c  -> if(a){x=b}{x=c} *)
	|Instr[Set(lv,Question (e1,e2,e3,ty),loc)] ->
	  let i1,i2 = Set(lv,e2,loc), Set(lv,e3,loc) in
	  let sk = If(e1,
		      mkBlock [mkStmtOneInstr i1],
		      mkBlock [mkStmtOneInstr i2], 
		      loc) in
	  let s' = mkStmt sk in
	  let rs = change_stmt s' in 
	  
	  (* if !vdebug then E.log "(Question) break %a\nto\n%s\n" *)
	  (*   dn_stmt s (String.concat "\n" (L.map string_of_stmt rs)); *)
	  
	  rs
	    
	|_ -> [s]
      in
      let stmts = L.flatten (L.map change_stmt b.bstmts) in
      {b with bstmts = stmts}
    in
    ChangeDoChildrenPost(b, action)
end



let fl_alg = ref 1 (*1: ochiai, ow: tarantula*)
let min_sscore:float ref = ref 0.5
let top_n_sids:int ref = ref 10

type inp_t = string list  (*e.g., *)
type outp_t = string 
type testcase_t = inp_t*outp_t


let string_of_tc ?(delim="; ") (tc:testcase_t) : string = 
  let inp,outp = tc in 
  let inp = string_of_list ~delim:delim inp in
  "inp: " ^ inp ^ ", outp: " ^ outp

let string_of_tcs ?(delim="; ") (tcs:testcase_t list) :string = 
  let tcs = L.map string_of_tc tcs in 
  string_of_list ~delim:delim tcs


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
  write_file_ascii testscript content
    

let run_testscript (testscript:string) (prog:string) (prog_output:string) =
  (* "sh script.sh prog prog_output" *)

  (try Unix.unlink prog_output with _ -> () ) ; 

  let prog = P.sprintf "%s" prog in (*"./%s"*)
  let cmd = P.sprintf "/bin/bash %s %s %s &> /dev/null" testscript prog prog_output in
  exec_cmd cmd


let mk_run_testscript testscript prog prog_output (tcs:testcase_t list) = 

  assert (not (Sys.file_exists testscript));
  mk_testscript testscript tcs;
  run_testscript testscript prog prog_output


class uTest (filename:string) = object(self)

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
    
    let inputs = read_file_ascii inputs in
    let outputs = read_file_ascii outputs in 

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

    if L.length tcs = 0 then (CC.ealert "No tcs !"; exit 1);

    if !vdebug then P.printf "|tcs|=%d\n%!" (L.length tcs);
    (*E.log "%s\n" (string_of_tcs tcs);*)

    mytcs <- tcs;
    self#get_goodbad_tcs


  method private get_goodbad_tcs = 
    P.printf "*** Get good/bad tcs ***\n%!FUCK";
    
    (*compile and run program on tcs*)
    let prog:string = compile filename in
    P.printf "gh0";    
    let testscript =  filename ^ ".sh" in
    let prog_output:string = filename ^ ".routputs" in
    mk_run_testscript testscript prog prog_output mytcs;
    P.printf "gh1";    
    (*check if prog passes all inputs:
      If yes then exit. If no then there's bug to fix*)
    let goods,bads = self#compare_outputs prog_output mytcs in 
    let nbads = L.length bads in
    if nbads = 0 then (CC.ealert "All tests passed. Exit!"; exit 0)
    else (CC.ealert "%d/%d tests failed." nbads (L.length mytcs));
    P.printf "%s\n%!" (string_of_tcs ~delim:"\n" bads);
    
    if !vdebug then (
      let tgoods = L.sort (fun (_,o1) (_,o2) -> compare o1 o2) goods in
      P.printf "%d good inputs\n%s\n%!" (L.length goods) (string_of_tcs ~delim:"\n" tgoods);
      let tbads = L.sort (fun (_,o1) (_,o2) -> compare o1 o2) bads in
      P.printf "%d bad inputs\n%s\n%!" (L.length bads) (string_of_tcs ~delim:"\n" tbads);

    );

    mygoods <- goods;
    mybads <- bads


  method private compare_outputs 
    (*
      Returns good and bad inputs.
      Good/bad inputs are when expected outputs eq/neq program outputs,
    *)
    (prog_outputs:string) (tcs:testcase_t list): testcase_t list * testcase_t list = 

    let prog_outputs = read_file_ascii prog_outputs in 
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
let stderr_vi = CC.mk_vi ~ftype:(TPtr(TVoid [], [])) "_coverage_fout"

class coverageVisitor = object(self)
  inherit nopCilVisitor

  method private create_fprintf_stmt (sid : CC.sid_t) :stmt = 
  let str = P.sprintf "%d\n" sid in
  let stderr = CC.exp_of_vi stderr_vi in
  let instr1 = CC.mk_call "fprintf" [stderr; Const (CStr(str))] in 
  let instr2 = CC.mk_call "fflush" [stderr] in
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

type sidscore_t = CC.sid_t*float (* sidscore_t = (sid,suspicious score) *)
class faultloc 
  (ast:file) 
  (goods:testcase_t list) 
  (bads:testcase_t list) 
  (stmt_ht:(CC.sid_t,stmt*fundec) H.t) = 
object(self)

  val ast = ast
  val goods = goods
  val bads = bads
  val stmt_ht = stmt_ht

  method get_susp_sids fl_alg : sidscore_t list = 
    P.printf "*** Fault Localization ***\n%!";

    assert (L.length bads > 0) ;
    if L.length goods = 0 then(
      P.printf "No good tests, faultloc will not be accurate !\n%!";
      H.fold (fun sid _ rs -> (sid,1.)::rs) stmt_ht [] 
    )
    else(
      
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
      let trace_generic = ast_bn ^ ".path" in
      let trace_g = ast_bn ^ ".gpath" in
      let trace_b = ast_bn ^ ".bpath" in
      
      (*good path*)
      mk_run_testscript (ast_bn ^ ".g.sh") prog 
	(ast_bn ^ ".outputs_g_dontcare") goods;
      Unix.rename trace_generic trace_g;
	
      (*bad path*)
      mk_run_testscript (ast_bn ^ ".b.sh") prog 
	(ast_bn ^ ".outputs_b_dontcare") bads;
      Unix.rename trace_generic trace_b;
	
      let (n_g:int), ht_g = self#analyze_trace trace_g in
      assert (n_g = L.length goods);
      
      let (n_b:int), ht_b = self#analyze_trace trace_b in
      assert (n_b = L.length bads);
      
      self#get_sscores fl_alg n_g ht_g n_b ht_b
    )

  method get_top_n (ssids:sidscore_t list) (top_n:int) (filter_f: sidscore_t -> bool) 
    : sidscore_t list = 

    let ssids = L.filter filter_f ssids in
    CC.ealert "FL: found %d ssids with after filtering" (L.length ssids);
    let ssids = take top_n ssids in (*consider only n top susp stmts*)      
    L.iter (fun (sid,score) -> P.printf "sid %d, score %g\n%!" sid score) ssids;
    ssids

      
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
  let instr = CC.mk_call ~av:(Some lhs) "fopen" [arg1; arg2] in
  let new_s = mkStmt (Instr[instr]) in 

  let fd = getGlobInit ast in
  fd.sbody.bstmts <- new_s :: fd.sbody.bstmts;
  
  CC.write_src filename_cov  ast

  (* Analyze execution path *)    
  method private analyze_trace (filename:string): int * (int,int) H.t= 

    if !vdebug then E.log "** Analyze exe path '%s'\n" filename;

    let tc_ctr = ref 0 in (*which test traces belong to*)
    let ht_occurs:(CC.sid_t,int) H.t = H.create 1024 in 
    let mem:(CC.sid_t*int,unit) H.t = H.create 1024 in 

    let lines = read_file_ascii filename in 

    L.iter(function
    | 0 -> incr tc_ctr; H.clear mem  (*0 markes the beginning of a test run*)

    | _ as sid ->
      let sid_tc = (sid, !tc_ctr) in
      if not (H.mem mem sid_tc) then (
	H.add mem sid_tc ();
	
	let n_occurs = 
	  if not (H.mem ht_occurs sid) then 1
	  else succ (H.find ht_occurs sid)
	in 
	H.replace ht_occurs sid n_occurs
      )
    ) (L.map int_of_string lines);

    (* P.printf "tc_ctr %d\n%!" !tc_ctr; *)
    (* H.iter (fun sid noccurs ->  *)
    (*   P.printf "sid %d occurs %d times \n%!" sid noccurs) ht_occurs; *)

    !tc_ctr, ht_occurs


  method private get_sscores 
    (fl_alg:int)
    (n_g:int) (ht_g:(CC.sid_t,int) H.t) 
    (n_b:int) (ht_b:(CC.sid_t,int) H.t) 
    : sidscore_t list =
    
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

    let sscores:(CC.sid_t*float) list  = H.fold (fun sid _ sscores ->
      let get_n_occur sid (ht: (int,int) H.t) : float=
	if H.mem ht sid then float_of_int(H.find ht sid) else 0. 
      in
      let good = get_n_occur sid ht_g in
      let bad = get_n_occur sid ht_b in
      (*P.printf "sid %d, bad %g n_bad %g good %g n_good %g\n%!" sid bad n_b good n_g;*)
      let score =  alg bad n_b good n_g in
      (*P.printf "score %g\n%!" score ;*)

      (sid,score)::sscores

    ) ht_sids [] in 

    let sscores:sidscore_t list = 
      L.sort (fun (_,score1) (_,score2) -> compare score2 score1) sscores in

    (*L.iter (fun (sid,score) -> P.printf "sid %d has score %g\n%!" sid score) sscores;*)

    sscores


  (*
    Tarantula (Jones & Harrold '05)
    score(s) = (bad(s)/total_bad) / (bad(s)/total_bad + good(s)/total_good)
    
    Ochiai (Abreu et. al '07)
    score(s) = bad(s)/sqrt(total_bad*(bad(s)+good(s)))
  *)

  method private alg_tarantula bad tbad good tgood =
      (bad /. tbad) /. ((good /. tgood) +. (bad /. tbad))

  method private alg_ochiai bad tbad good tgood = 
      bad /. sqrt(tbad *.tgood)
    
end


