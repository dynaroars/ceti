(*ocamlfind ocamlopt -package str,batteries,cil  cil_common.cmx -linkpkg -thread tf.ml*)

open Cil
module E = Errormsg
module L = List
module A = Array
module H = Hashtbl 
module P = Printf

let strip s =
  let is_space = function
    | ' ' | '\012' | '\n' | '\r' | '\t' -> true
    | _ -> false in
  let len = String.length s in
  let i = ref 0 in
  while !i < len && is_space (String.get s !i) do
    incr i
  done;
  let j = ref (len - 1) in
  while !j >= !i && is_space (String.get s !j) do
    decr j
  done;
  if !i = 0 && !j = len - 1 then
    s
  else if !j >= !i then
    String.sub s !i (!j - !i + 1)
  else
    ""

(*check if s1 is a substring of s2*)
let in_str s1 s2 = 
  try ignore(Str.search_forward (Str.regexp_string s1) s2 0); true
  with Not_found -> false

let str_split s:string list =  Str.split (Str.regexp "[ \t]+")  s

(* let forceOption (ao : 'a option) : 'a = *)
(*   match ao with  | Some a -> a | None -> raise(Failure "forceOption") *)

let write_file_str (filename:string) (content:string): unit = 
  let fout = open_out filename in
  P.fprintf fout "%s" content; 
  close_out fout;
  E.log "write_file_str: '%s'\n" filename

let write_file_bin (filename:string) content: unit = 
  let fout = open_out_bin filename in
  Marshal.to_channel fout content [];
  close_out fout;
  E.log "write_file_bin: '%s'\n" filename

let read_file_bin (filename:string) =
  let fin = open_in_bin filename in
  let content = Marshal.from_channel fin in
  close_in fin;
  E.log "read_file: '%s'\n" filename;
  content

let write_src ?(use_stdout:bool=false) (filename:string) (ast:file): unit = 
  let df oc =  dumpFile defaultCilPrinter oc filename ast in
  if use_stdout then df stdout else (
    let fout = open_out filename in
    df fout;
    close_out fout;
    E.log "write_src: '%s'\n" filename
  )

let rec take n = function 
  |[] -> [] 
  |h::t -> if n = 0 then [] else h::take (n-1) t

(* let rec drop n = function *)
(*   | [] -> [] *)
(*   | h::t as l -> if n = 0 then l else drop (n-1)  *)

let rec range ?(a=0) b = if a >= b then [] else a::range ~a:(succ a) b 
let copy_obj (x : 'a) = 
  let s = Marshal.to_string x [] in (Marshal.from_string s 0 : 'a)

(*create a temp dir*)
let mk_tmp_dir ?(use_time=false) ?(temp_dir="") dprefix dsuffix = 
  let dprefix = if use_time 
    then P.sprintf "%s_%d" dprefix  (int_of_float (Unix.time())) 
    else dprefix 
  in 
  let dprefix = dprefix ^ "_" in 

  let td = 
    if temp_dir = "" then Filename.temp_file dprefix dsuffix 
    else Filename.temp_file ~temp_dir:temp_dir dprefix dsuffix
  in
      
  Unix.unlink td;
  Unix.mkdir td 0o755;
  td
    
let exec_cmd cmd = 
  E.log "$ %s\n" cmd ;
  match Unix.system cmd with
    |Unix.WEXITED(0) -> ()
    |_ -> E.s(E.error "cmd failed '%s'" cmd)

let chk_file_exist ?(msg="") (filename:string) : unit =
  if not (Sys.file_exists filename) then (
    if msg <> "" then E.log "%s\n" msg;
    E.s(E.error "file '%s' not exist" filename)
  )
  
let econtextMessage name d = 
  if name = "" then 
    ignore (Pretty.fprintf !E.logChannel  "%a@!" Pretty.insert d)
  else
    ignore (Pretty.fprintf !E.logChannel  "%s: %a@!" name Pretty.insert d);

  E.showContext ()
let ealert fmt : 'a = 
  let f d =
    if !E.colorFlag then output_string !E.logChannel E.purpleEscStr;
    econtextMessage "Alert" d;
    if !E.colorFlag then output_string !E.logChannel E.resetEscStr;
    flush !E.logChannel
  in
  Pretty.gprintf f fmt


(*filename formats*)
let ginfo_s = P.sprintf "%s.info" (*f.c.info*)
let arr_s = P.sprintf "%s.s%d.t%d.arr" (*f.c.s1.t3.arr*)
let transform_s = P.sprintf "%s.s%d.%s.tf.c" (*f.c.s5.z3_c2.tf.c*)

(*commands*)
let gcc_cmd = P.sprintf "gcc %s -o %s >& /dev/null"

let boolTyp:typ = intType
type inp_t = int list 
type outp_t = int 
type testcase = inp_t * outp_t
type sid_t = int

(* Specific options for this program *)
let vdebug:bool ref = ref false
let dlog s = if !vdebug then E.log "%s" s else ()
let dalert s = if !vdebug then ealert "%s" s else ()



let fl_ssids = ref [] (*manually provide fault loc info*)
let fl_alg = ref 1 

let no_global_vars = ref false
let no_parallel = ref false
let no_bugfix = ref false
let no_stop = ref false


let only_transform = ref false
let ssid = ref (-1) (*only do transformation on vs_idxs*)
let tpl = ref 0
let idxs = ref []
let xinfo = ref "" (*helpful info for debuggin*)

let only_spy = ref false
let only_peek = ref false (*for debugging only, peeking at specific stmt*)


let python_script = "kl.py" (*name of the python script, must be in same dir*)

let uk_const_min:int = -100000
let uk_const_max:int =  100000
let uk_min :int = -1 
let uk_max :int =  1

let min_sscore:float ref = ref 0.5
let top_n_ssids:int ref = ref 10
let tpl_ids:int list ref = ref [] (*apply only these specific template ids*)
let tpl_level:int ref = ref 3 (*apply only templates with <= levels*)
let extra_vars:varinfo list ref = ref []

(******************* Helper Functions *******************)
let find_fun (ast:file) (funname:string) : fundec = 
  let fd = ref None in
  iterGlobals ast (function 
  |GFun(f,_) when f.svar.vname = funname -> fd := Some f
  |_ -> ()
  );
  match !fd with
  |Some f -> f
  |None -> E.s (E.error "fun '%s' not in '%s'!" funname ast.fileName)


let mk_vi ?(ftype=TVoid []) fname: varinfo = makeVarinfo true fname ftype

(*av = fname(args)*)
let mk_call ?(ftype=TVoid []) ?(av=None) fname args : instr = 
  let f = var(mk_vi ~ftype:ftype fname) in
  Call(av, Lval f, args, !currentLoc)

let exp_of_vi (vi:varinfo): exp = Lval (var vi)

let string_of_stmt (s:stmt) = Pretty.sprint ~width:80 (dn_stmt () s) 
let string_of_exp (s:exp) = Pretty.sprint ~width:80 (dn_exp () s) 
let string_of_instr (s:instr) = Pretty.sprint ~width:80 (dn_instr () s) 
let string_of_lv (s:lval) = Pretty.sprint ~width:80 (dn_lval () s) 
let string_of_list =   String.concat ", " 
let string_of_ints (l:int list): string = string_of_list (L.map string_of_int l)

let string_of_binop = function
  |Lt -> "<"
  |Gt -> ">"
  |Le -> "<="
  |Ge -> ">="
  |Eq -> "="
  |Ne -> "!="

  |LAnd -> "&&"
  |LOr  -> "||"

  |BAnd -> "&"
  |BOr -> "|"
  |BXor -> "^"
  |Shiftlt -> "<<"
  |Shiftrt -> ">>"
    
  |_ -> E.s (E.error "unknown binop")

let string_of_unop = function
  |Neg -> "unary -"
  |BNot -> "~"
  |LNot -> "!"
  

(*gcc filename.c;  return "filename.exe" if success else None*)
let compile (src:string): string = 
  let exe = src ^ ".exe" in 
  (try Unix.unlink exe with _ -> () ) ; 
  let cmd = gcc_cmd src exe in
  E.log "cmd '%s'\n" cmd ;
  exec_cmd cmd ;
  exe


(*returns a list of lines from an ascii file*)
let read_lines (filename:string) :string list =
  let lines:string list ref = ref [] in
  (try
    let fin = open_in filename in
    (try
       while true do 
	 let line = strip (input_line fin) in 
	 lines := line::!lines
       done
     with _ -> close_in fin)
   with _ -> ());
  L.rev !lines

(*apply binary op to a list of exps, e.g, + [v1,..,vn] =>  v1 + .. + vn*)
let apply_binop (op:binop) (exps:exp list): exp = 
  assert (L.length exps > 0);
  let e0 = L.hd exps in 
  let ty = typeOf e0 in
  L.fold_left (fun e e' -> BinOp(op,e,e',ty)) e0 (L.tl exps)


let isSimpleExp = function
  | Const _ 
  | Lval _ -> true 
  |_->false



(******************* Helper Visistors *******************)
(*Find variables of type bool, so that we don't do int var*/+ bool var 
  during instrumentation 
  TODO:  I am still confused if I should use DoChildren or SkipChildren
*)

class findBoolVars (bvs:varinfo list ref) = object
  inherit nopCilVisitor

  method vstmt (s:stmt) = 
    match s.skind with 
    |If(Lval (Var vi,_),_,_,_) -> bvs := vi::!bvs; DoChildren  
    |_->DoChildren

end

(*********************** Reading Testcases ***********************)

let string_of_tc (tc:int list * int) : string = 
  let inp,outp = tc in 
  let inp = String.concat "; " (L.map string_of_int inp) in
  let outp = string_of_int outp in 
  "([" ^ inp ^ "]" ^ ", " ^ outp ^ "]"

let string_of_tcs (tcs:testcase list) :string = 
  let tcs = L.map string_of_tc tcs in 
  let tcs = String.concat "; " tcs in
  "["^ tcs ^ "]"
  
(*read testcases *)
let get_tcs (filename:string) (inputs:string) (outputs:string): (int list * int) list = 

  if !vdebug then E.log "read tcs from '%s' and '%s' for '%s'" inputs outputs filename;

  let inputs = read_lines inputs in
  let outputs = read_lines outputs in 
  assert (L.length inputs = L.length outputs);

  let tcs = 
    L.fold_left2 (fun acc inp outp ->
      let inp = str_split  inp in
      (try
       let inp = L.map int_of_string inp in 
       let outp = int_of_string outp in 
       (inp,outp)::acc

       with _ -> 
	 E.error "Ignoring (%s, %s)" (String.concat ", " inp) outp;
	 acc
      )
    ) [] inputs outputs 
  in
    
  let tcs = L.rev tcs in			    
  if !vdebug then E.log "|tcs|=%d\n" (L.length tcs);

  (*E.log "%s\n" (string_of_tcs tcs);*)
  
  tcs

(******************* Initialize *******************)
(*break conditional / loop guard to 
  if(complex_exp) to 
  int tmp = complex_exp; 
  if(tmp) 
  Assigning id's to stmts 
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
    v, {s with skind = Instr [i]} 

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
	  if !vdebug then E.log "(If) break %a\n ton%s\n" 
	    dn_stmt s (String.concat "\n" (L.map string_of_stmt rs));

	  rs

	(*return e; ->  int t = e; return t;*)
	|Return(Some e,loc) ->
	  let v, s1 = self#mk_stmt s e loc in
	  let s1s = change_stmt s1 in

	  let s2 = mkStmt (Return (Some (Lval v), loc)) in
	  let rs =  s1s@[s2] in
	  if !vdebug then E.log "(Return) break %a\nto\n%s\n" 
	    dn_stmt s (String.concat "\n" (L.map string_of_stmt rs));
	  
	  rs

	(*x = a?b:c  -> if(a){x=b}{x=c} *)
	|Instr [Set (lv,Question (e1,e2,e3,ty),loc)] ->
	  let i1,i2 = Set(lv,e2,loc), Set(lv,e3,loc) in
	  let sk = If(e1,
		      mkBlock [mkStmtOneInstr i1],
		      mkBlock [mkStmtOneInstr i2], 
		      loc) in
	  let s' = mkStmt sk in
	  let rs = change_stmt s' in 

	  if !vdebug then E.log "(Question) break %a\nto\n%s\n"
	    dn_stmt s (String.concat "\n" (L.map string_of_stmt rs));

	  rs


	|_ -> [s]
      in
      let stmts = L.flatten (L.map change_stmt b.bstmts) in
      {b with bstmts = stmts}
    in
    ChangeDoChildrenPost(b, action)


end


(*Makes every instruction into its own statement*)
class everyVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    let action (b: block) : block = 
      let change_stmt (s: stmt) : stmt list = 
	match s.skind with
	|Instr(h::t) -> {s with skind = Instr([h])}::L.map mkStmtOneInstr t
	|_ -> [s]
      in
      let stmts = L.flatten (L.map change_stmt b.bstmts) in
      {b with bstmts = stmts}
    in
    ChangeDoChildrenPost(b, action)
end



(* Walks over AST and builds a hashtable that maps int to stmt*fundec *)
class numVisitor ht = object(self)
  inherit nopCilVisitor

  val mutable mctr = 1
  val mutable cur_fd = None

  method vfunc f = cur_fd <- (Some f); DoChildren

  (*Stmts that can be tracked for fault loc and modified for bug fix *)
  method private can_modify : stmtkind -> bool = function 
  |Instr [Set(_)] -> true
  |_ -> false

  method vblock b = 
    let action (b: block) : block= 
      let change_sid (s: stmt) : unit = 
	if self#can_modify s.skind then (
	  s.sid <- mctr;
	  let fd = match cur_fd with 
	    | Some f -> f | None -> E.s(E.error "not in a function") in
	  H.add ht mctr (s, fd);
	  mctr <- succ mctr
	)
	else s.sid <- 0;  (*Anything not considered has sid 0 *)
      in 
      L.iter change_sid b.bstmts; 
      b
    in 
    ChangeDoChildrenPost(b, action)



end


(********************** Initial Check **********************)

let mk_testscript (testscript:string) (tcs:(int list * int) list) =
  (*"($1 1071 1029 | diff ref/output.1071.1029 - && (echo "1071 1029" >> $2)) &"*)

  let content = L.map (fun (inp,_) ->
    let inp = String.concat " " (L.map string_of_int inp) in

    (*if use & then things are done in parallel but order mesed up*)
    P.sprintf "($1 %s >> $2) ;" inp 
  ) tcs in
  let content = String.concat "\n" content in
  let content = P.sprintf "#!/bin/bash\nulimit -t 1\n%s\nwait\nexit 0\n" content in
  
  if!vdebug then E.log "Script %s\n%s\n" testscript content;
  write_file_str testscript content
    

let run_testscript (testscript:string) (prog:string) (prog_output:string) =
  (* "sh script.sh prog prog_output" *)

  (try Unix.unlink prog_output with _ -> () ) ; 

  let prog = P.sprintf "%s" prog in (*"./%s"*)
  let cmd = P.sprintf "sh %s %s %s &> /dev/null" testscript prog prog_output in
  exec_cmd cmd


let mk_run_testscript testscript prog prog_output tcs = 

  assert (not (Sys.file_exists testscript));
  mk_testscript testscript tcs;
  run_testscript testscript prog prog_output
    
    
(*partition tcs into 2 sets: good / bad*)
let compare_outputs (prog_outputs:string) (tcs:testcase list) : testcase list * testcase list = 
  let prog_outputs = read_lines prog_outputs in 
  assert (L.length prog_outputs == L.length tcs) ;

  let goods, bads = L.partition (fun ((_,e_outp),p_outp) -> 
    (try e_outp = int_of_string p_outp 
     with _ -> false)
  ) (L.combine tcs prog_outputs) in

  let goods,_ = L.split goods in
  let bads,_ =  L.split bads in

  goods, bads


(*do some prelim checking and obtain good/test testcases*)
let get_goodbad_tcs (filename:string) (tcs:(int list * int) list)  = 
  E.log "*** Get good/bad tcs ***\n";

  (*compile and run program on tcs*)
  let prog:string = compile filename in

  let testscript =  filename ^ ".sh" in
  let prog_output:string = filename ^ ".routputs" in
  mk_run_testscript testscript prog prog_output tcs;

  (*check if prog passes all inputs:
    If yes then exit. If no then there's bug to fix*)
  let goods,bads = compare_outputs prog_output tcs in 
  let nbads = L.length bads in
  if nbads = 0 then (ealert "All tests passed ... no bug found. Exit !"; exit 0)
  else (ealert "%d/%d tests failed ... bug found. Processing" nbads (L.length tcs));
  
  goods, bads



(******************* Fault Localization *******************)

(********** Create Coverage Info **********)

(*walks over AST and preceeds each stmt with a printf that writes out its sid*)

(*create a stmt consisting of 2 Call instructions
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


let coverage (ast:file) (filename_cov:string) (filename_path:string) = 

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
let analyze_path (filename:string): int * (int,int) H.t= 

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


type sscore = int * float (* sid, suspicious score *)

let compute_sscores (n_g:int) (ht_g:(int,int) H.t) (n_b:int) (ht_b:(int,int) H.t) : sscore list=

  assert(n_g <> 0);
  assert(n_b <> 0);

  (*
    Tarantula (Jones & Harrold '05)
    score(s) = (bad(s)/total_bad) / (bad(s)/total_bad | good(s)/total_good)

    Ochiai (Abreu et. al '07)
    score(s) = bad(s)/sqrt(total_bad*(bad(s)+good(s)))
  *)
  let tarantula_heuristic bad tbad good tgood =
    (bad /. tbad) /. ((good /. tgood) +. (bad /. tbad))
  in

  let ochiai_heuristic bad tbad good tgood = 
    bad /. sqrt(tbad *. (bad +. good))
  in

  let alg = if !fl_alg = 1 then ochiai_heuristic else tarantula_heuristic in

  let ht_sids = H.create 1024 in 
  let set_sids ht =
    H.iter (fun sid _ ->
      if not (H.mem ht_sids sid) then H.add ht_sids sid ()
    ) ht;
  in
  set_sids ht_g ;
  set_sids ht_b ;

  let n_g' = float_of_int(n_g) in
  let n_b' = float_of_int(n_b) in

  let rs = H.fold (fun sid _ rs ->
    let get_n_occur sid (ht: (int,int) H.t) : float=
      if H.mem ht sid then float_of_int(H.find ht sid) else 0. 
    in
    let good = get_n_occur sid ht_g in
    let bad = get_n_occur sid ht_b in
    let score =  alg bad n_b' good n_g' in
      
    (sid,score)::rs

  ) ht_sids [] in 

  let rs = L.sort (fun (_,score1) (_,score2) -> compare score2 score1) rs in
  rs


let fault_loc (ast:file) (goods:testcase list) (bads:testcase list) 
    (stmt_ht:(sid_t,stmt*fundec) H.t): sid_t list = 
  E.log "*** Fault Localization ***\n";

  assert (L.length goods > 0) ;
  assert (L.length bads  > 0) ;


  let tdir = mk_tmp_dir ~temp_dir:(Filename.dirname ast.fileName) "fautloc" "" in
  let ast_bn =  P.sprintf "%s/%s" tdir (Filename.basename ast.fileName) in

  (*create cov file*)
  let fileName_cov = ast_bn ^ ".cov.c"  in
  let fileName_path = ast_bn ^ ".path"  in
  coverage (copy_obj ast) fileName_cov fileName_path;

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

  let n_g, ht_g = analyze_path path_g in
  let n_b, ht_b = analyze_path path_b in
  let sscores = compute_sscores n_g ht_g n_b ht_b in

  (*remove all susp stmts in main, which cannot have anything except call
    to mainQ, everything in main will be deleted when instrumenting main*)
  let idx = ref 0 in 
  let sscores = L.filter (fun (sid,score) -> 
    let s,f = H.find stmt_ht sid in
    if score >= !min_sscore && f.svar.vname <> "main" then(
      E.log "%d. sid %d in fun '%s' (score %g)\n%a\n"
	!idx sid f.svar.vname score dn_stmt s;
      incr idx;
      true
    )else false
  )sscores in


  ealert "FL: found %d stmts with sscores >= %g" (L.length sscores) !min_sscore;
  
  L.map fst sscores


class faultloc = object(self)
    
  method coverage (ast:file) (filename_cov:string) (filename_path:string) = 

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
  method analyze_path (filename:string): int * (int,int) H.t= 

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

  method compute_sscores 
    (n_g:int) (ht_g:(int,int) H.t) 
    (n_b:int) (ht_b:(int,int) H.t) : sscore list=

    assert(n_g <> 0);
    assert(n_b <> 0);
    
    (*
      Tarantula (Jones & Harrold '05)
      score(s) = (bad(s)/total_bad) / (bad(s)/total_bad | good(s)/total_good)
      
      Ochiai (Abreu et. al '07)
      score(s) = bad(s)/sqrt(total_bad*(bad(s)+good(s)))
    *)
    let tarantula_heuristic bad tbad good tgood =
      (bad /. tbad) /. ((good /. tgood) +. (bad /. tbad))
    in

    let ochiai_heuristic bad tbad good tgood = 
      bad /. sqrt(tbad *. (bad +. good))
    in

    let alg = if !fl_alg = 1 then ochiai_heuristic else tarantula_heuristic in

    let ht_sids = H.create 1024 in 
    let set_sids ht =
      H.iter (fun sid _ ->
	if not (H.mem ht_sids sid) then H.add ht_sids sid ()
      ) ht;
    in
    set_sids ht_g ;
    set_sids ht_b ;

    let n_g = float_of_int(n_g) in
    let n_b = float_of_int(n_b) in

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

  method fl (ast:file) (goods:testcase list) (bads:testcase list) 
    (stmt_ht:(sid_t,stmt*fundec) H.t): sid_t list = 
    E.log "*** Fault Localization ***\n";

    assert (L.length goods > 0) ;
    assert (L.length bads  > 0) ;

    let ast_bn =  
      let tdir = Filename.dirname ast.fileName in
      let tdir = mk_tmp_dir ~temp_dir:tdir "fautloc" "" in
      P.sprintf "%s/%s" tdir (Filename.basename ast.fileName) 
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
    let sscores = self#compute_sscores n_g ht_g n_b ht_b in

    (*remove all susp stmts in main, which cannot have anything except call
      to mainQ, everything in main will be deleted when instrumenting main*)
    let idx = ref 0 in 
    let sscores = L.filter (fun (sid,score) -> 
      let s,f = H.find stmt_ht sid in
      if score >= !min_sscore && f.svar.vname <> "main" then(
	E.log "%d. sid %d in fun '%s' (score %g)\n%a\n"
	  !idx sid f.svar.vname score dn_stmt s;
	incr idx;
	true
      )else false
    )sscores in


    ealert "FL: found %d stmts with sscores >= %g" (L.length sscores) !min_sscore;
    
    L.map fst sscores
    
end
(******************* For debugging a Cil construct *******************)

let rec peek_exp e: string = 
  match e with 
  |Const _ -> "Cconst"
  |Lval lv -> string_of_lv lv
  |SizeOf _ -> "SizeOf"
  |SizeOfE _ -> "SizeOfE"
  |SizeOfStr _ -> "SizeOfStr"    
  |AlignOf _ -> "AlignOf"
  |AlignOfE _ -> "AlignOfE"
  |UnOp (uop,e',_) -> P.sprintf "%s (%s)" (string_of_unop uop) (peek_exp e)
  |BinOp (bop,e1,e2,_) -> 
    P.sprintf "%s %s %s" (peek_exp e1) (string_of_binop bop) (peek_exp e2)
  |Question _ -> "Question"
  |CastE _ -> "CastE"
  |AddrOf _-> "AddrOf"
  |AddrOfLabel _-> "AddrOfLabel"
  |StartOf _ -> "StartOf"
    
and peek_instr ins: string = 
  match ins with 
  |Set(lv,e,_) -> P.sprintf "%s = %s" (string_of_lv lv) (peek_exp e)
  |Call _ -> "Call"
  |_ -> "(unimp instr: "  ^ string_of_instr ins ^ ")"
    
class peekVisitor sid = object(self)
  inherit nopCilVisitor
  method vstmt s = 
    if s.sid = sid then (
      ealert "Peek: ssid %d\n%a" s.sid dn_stmt s;
      match s.skind with 
      |Instr ins -> 
	let rs = L.map peek_instr ins in 
	E.log "%s\n" (String.concat "\n" rs);
      |_ -> E.unimp "stmt : %a" dn_stmt s
    );
    DoChildren
end

  
(******************* Transforming File *******************)
(*declare and set constraints on uk:
  int uk;
  klee_make_symbol(&uk,sizeof(uk),"uk");
  mk_klee_assume(min<=uk<=max);
*)




(*sets of compatible operators so we can change, e.g., <= to >= but not <= to && *)
(* let ops_comp = [Gt;Ge;Eq;Ne;Lt;Le] *)
(* let ops_logical = [LAnd; LOr] *)
(* let ops_bitwise = [BAnd; BOr; BXor; Shiftlt; Shiftrt] *)



(*add uk's to function args, e.g., fun(int x, int uk0, int uk1);*)
class funInstrVisitor (uks:varinfo list) = object
  inherit nopCilVisitor

  val ht = H.create 1024 
  method ht = ht

  method vfunc fd = 
    if fd.svar.vname <> "main" then (
      setFormals fd (fd.sformals@uks) ;
      H.add ht fd.svar.vname () 
    );
    DoChildren
end

(*insert uk's as input to all function calls
e.g., fun(x); -> fun(x,uk0,uk1); *)
class instrCallVisitor (uks:varinfo list) (funs_ht:(string,unit) H.t)= object
  inherit nopCilVisitor

  method vinst (i:instr) =
    match i with 
    | Call(lvopt,(Lval(Var(va),NoOffset)), args,loc) 
	when H.mem funs_ht va.vname ->
      let uks' = L.map exp_of_vi uks in 
      let i' = Call(lvopt,(Lval(Var(va),NoOffset)), args@uks',loc) in
      ChangeTo([i'])

    |_ -> SkipChildren
end

let mk_uk (uid:int) (min_v:int) (max_v:int)
    (main_fd:fundec) 
    (vs:varinfo list ref)
    (instrs:instr list ref) 
    :varinfo =
    
  let vname = ("uk_" ^ string_of_int uid) in 
  
  (*declare uks*)
  let vi:varinfo = makeLocalVar main_fd vname intType in 
  let lv:lval = var vi in 
  
  (*klee_make_symbolic(&uk,sizeof(uk),"uk") *)
  let mk_sym_instr:instr = mk_call "klee_make_symbolic" 
    [mkAddrOf(lv); SizeOfE(Lval lv); Const (CStr vname)] in
  
  let klee_assert_lb:instr = mk_call "klee_assume" 
    [BinOp(Le,integer min_v,Lval lv, boolTyp)] in 
  
  let klee_assert_ub:instr = mk_call "klee_assume" 
    [BinOp(Le,Lval lv, integer max_v, boolTyp)] in 
  
  vs := !vs@[vi];
  instrs := !instrs@[mk_sym_instr;  klee_assert_lb; klee_assert_ub];

  vi 

(*make calls to mainQ on test inp/oupt:
  mainQ_typ temp;
  temp = mainQ(inp0,inp1,..);
  temp == outp
*)
let mk_main (main_fd:fundec) (mainQ_fd:fundec) (tcs:testcase list) 
    (uks:varinfo list) (instrs1:instr list) :stmt list= 
  
  let rs = L.map (fun (inps, outp) -> 
    let mainQ_typ:typ = match mainQ_fd.svar.vtype with 
      |TFun(t,_,_,_) -> t
      |_ -> E.s(E.error "%s is not fun typ %a\n" 
		  mainQ_fd.svar.vname d_type mainQ_fd.svar.vtype)
    in
  
    (*mainQ_typ temp;*)
    let temp:lval = var(makeTempVar main_fd mainQ_typ) in 
  
    (*tmp = mainQ(inp, uks);*)
    (*todo: should be the types of mainQ inps , not integer*)
    let args = L.map integer inps in 
    let i:instr = mk_call ~ftype:mainQ_typ ~av:(Some temp) "mainQ" args in
    
    (*mk tmp == outp*)
    (*todo: should convert outp according to mainQ type*)
    let e:exp = BinOp(Eq,Lval temp,integer outp, boolTyp) in 
    i,e
  ) tcs in

  let instrs2, exps = L.split rs in 

  (*creates reachability "goal" statement 
    if(e_1,..,e_n){printf("GOAL: uk0 %d, uk1 %d ..\n",uk0,uk1);klee_assert(0);}
  *)
  let s = L.map (fun vi -> vi.vname ^ " %d") uks in
  let s = "GOAL: " ^ (String.concat ", " s) ^ "\n" in 
  let print_goal:instr = mk_call "printf" 
    (Const(CStr(s))::(L.map exp_of_vi uks)) in 
  
  (*klee_assert(0);*)
  let klee_assert_zero:instr = mk_call "klee_assert" [zero] in 
  
  let and_exps = apply_binop LAnd exps in
  let if_skind = If(and_exps, 
		    mkBlock [mkStmt (Instr([print_goal; klee_assert_zero]))], 
		    mkBlock [], 
		    !currentLoc) 
  in
  
  let instrs_skind:stmtkind = Instr(instrs1@instrs2) in
  [mkStmt instrs_skind; mkStmt if_skind]


class modStmtVisitor (ssid:int) 
  (mk_instr:instr -> varinfo list ref -> instr list ref -> instr) = 
object (self)

  inherit nopCilVisitor 
    
  val mutable status = ""

  val uks   :varinfo list ref = ref []
  val instrs:instr list ref = ref []

  method status = status
  method uks = !uks
  method instrs = !instrs

  method vstmt (s:stmt) = 
    let action (s: stmt) :stmt = 
      (match s.skind with 
      |Instr ins when s.sid = ssid ->
	assert (L.length ins = 1);

	(*ealert "debug: stmt %d\n%a\n" ssid dn_stmt s;*)

	let old_i = L.hd ins in 
	let new_i = mk_instr old_i uks instrs in	
	s.skind <- Instr [new_i];

	status <- (P.sprintf "%s ## %s"  (*the symbol is used when parsing*)
		  (string_of_instr old_i) (string_of_instr new_i));

	if !vdebug then ealert "%s" status

      |_ -> ()
      ); s in
    ChangeDoChildrenPost(s, action)  
end
  

class virtual tpl (cname:string) (cid:int) (level:int) = object

  val cname = cname
  val cid = cid
  val level = level

  method cname: string = cname
  method cid : int = cid
  method level: int = level

  method virtual spy : string -> sid_t -> fundec -> instr -> string
  method virtual mk_instr : file -> fundec -> int -> int -> int list -> string -> 
    (instr -> varinfo list ref -> instr list ref -> instr)
end 


class tpl_CONSTS = object(self)
  inherit tpl "CONSTS" 3 1 as super

  method spy (filename:string) (sid:sid_t) (fd:fundec) = function
  |Set (_,e,_) ->
    let rec find_consts ctr e: int = match e with
      |Const _ -> succ ctr
      |Lval _ -> ctr
      |UnOp(_,e1,_) -> find_consts ctr e1
      |BinOp (_,e1,e2,_) -> find_consts ctr e1 + find_consts ctr e2

      | _ -> 
	ealert "%s: don't know how to deal with exp '%a' (sid %d)" 
	super#cname dn_exp e sid;
    	ctr
    in
    let n_consts:int = find_consts 0 e in
    
    if !vdebug then E.log "%s: found %d consts\n" super#cname n_consts;

    if n_consts > 0 then 
      P.sprintf "(%d, %d, %d, %d)" sid super#cid super#level n_consts
      
    else ""
      
  |_ -> ""

  (*Functions used for stand alone prog*)

  (*idxs e.g., [3] means 3 consts found in the susp stmt*)

  (*from smt x = e , returns x = e' where e' is similar to e 
  but with all const in e replaced with uk's *)
  method mk_instr (ast:file) (main_fd:fundec) (ssid:int)  
    (tpl_id:int) (idxs:int list) (xinfo:string) 
    :(instr -> varinfo list ref -> instr list ref -> instr) = 

    assert (L.length idxs = 1);
    let n_consts = L.hd idxs in
    E.log "** %s: xinfo %s, consts %d\n" super#cname xinfo n_consts;

    fun a_i uks instrs -> (
      let mk_exp (e:exp): exp = 
	let new_uk uid = mk_uk uid 
	  uk_const_min uk_const_max main_fd uks instrs in
	let ctr = ref 0 in
	
	let rec find_const e = match e with
	  |Const _ -> let vi = new_uk !ctr in incr ctr; exp_of_vi vi
	  |Lval _ -> e
	  |UnOp (uop,e1,ty) -> UnOp(uop,find_const e1,ty)
	  |BinOp (bop,e1,e2,ty) -> BinOp(bop,find_const e1, find_const e2, ty)
	  | _ -> 
	    ealert "%s: don't know how to deal with exp '%a'" 
	      super#cname dn_exp e;
	    e
	in
	let r_exp = find_const e in

	r_exp
      in
	
      match a_i with
      |Set(v,e,l) -> Set(v, mk_exp e, l)
      |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)
    )

end

type bop_t = LOGIC_B | COMP_B 
let string_of_bop_t = function
  |LOGIC_B -> "LOGIC_B"
  |COMP_B -> "COMP_B"
let id_of_bop_t = function
  |LOGIC_B -> 5
  |COMP_B -> 6

class tpl_OPS (x:bop_t) = object(self)
  inherit tpl (P.sprintf "OPS_%s" (string_of_bop_t x)) (id_of_bop_t x) 2 as super

  val ops_ht:(binop, binop array) H.t = H.create 128
  initializer
  let logic_bops = [|LAnd; LOr|] in
  let comp_bops = [|Lt; Gt; Le; Ge; Eq; Ne|] in

  let ops = 
    match x with 
    |LOGIC_B -> logic_bops
    |COMP_B -> comp_bops
  in

  A.iter (fun b -> H.add ops_ht b ops) ops;

  (* L.iter(fun bl -> A.iter (fun b -> H.add ops_ht b bl) bl) *)
  (*     [(\*TODO: TOO LONG,  should consider only 1 group at a time .. *\) *)
  (* 	[|LAnd; LOr|]; *)
  (* 	[|Lt; Gt; Le; Ge; Eq; Ne|] *)
  (*     ]; *)
    
  E.log "%s: create bops ht (len %d)\n" super#cname (H.length ops_ht)

  method spy (filename:string) (sid:sid_t) (fd:fundec) = function
  |Set (_,e,_) ->
    let rec find_ops l e: binop list = match e with
      |Const _ -> l
      |Lval  _ -> l
      |UnOp(_,e1,_) -> find_ops l e1
      |BinOp (bop,e1,e2,_) ->  
	let e1_ops = find_ops l e1 in
	let e2_ops = find_ops l e2 in
	let e_ops = e1_ops@e2_ops in
	if H.mem ops_ht bop then bop::e_ops else e_ops

      |_ ->
	ealert "%s: don't know how to deal with exp '%a' (sid %d)" 
	  super#cname dn_exp e sid;
	l
    in
    let ops = find_ops [] e in
    let ops_lens = L.map (fun op -> A.length (H.find ops_ht op)) ops in 
    let len = L.length ops in 

    if !vdebug then E.log "%s: found %d ops [%s]\n" 
      super#cname len (string_of_list (L.map string_of_binop ops));

    if len > 0 then
      P.sprintf "(%d, %d, %d, %s)" sid super#cid super#level
	(String.concat " " (L.map string_of_int ops_lens))
    else
      ""
  |_ -> ""

  (*idxs = [3, 5, 7]*)
  method mk_instr (ast:file) (main_fd:fundec) (ssid:int) (tpl_id:int) 
    (idxs:int list) (xinfo:string) 
    :(instr -> varinfo list ref -> instr list ref -> instr) = 

    assert (L.length idxs > 0);
    assert (L.for_all (fun idx -> idx >= 0) idxs);

    E.log "**%s: wtf xinfo %s, idxs %d [%s]\n" super#cname xinfo 
      (L.length idxs) (string_of_ints idxs);

    fun a_i uks instrs -> (
      let mk_exp (e:exp): exp = 
	let idxs = A.of_list idxs in
	let ctr = ref 0 in
	
	let rec find_ops e = match e with
	  |Const _ -> e
	  |Lval _ -> e
	  |UnOp(uop,e1,ty) -> UnOp(uop,find_ops e1,ty)
	  |BinOp (bop,e1,e2,ty) -> 

	    let bop' = 
	      if H.mem ops_ht bop then
		let arr:binop array = H.find ops_ht bop in
		let bop'' = arr.(idxs.(!ctr)) in
		incr ctr;
		bop''
	      else
		bop
	    in

	    let e1' = find_ops e1 in
	    let e2' = find_ops e2 in
	    BinOp(bop', e1', e2', ty)
	      
	  | _ -> ealert "%s: don't know how to deal with exp '%a'" 
	    super#cname dn_exp e;
	    e
	in
	let r_exp = find_ops e in 
	assert (!ctr = A.length idxs); (*make sure that all idxs are used*)
	r_exp   
      in
      
      match a_i with
      |Set(v,e,l) -> Set(v,mk_exp e,l)
      |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)
    )

end

class tpl_VS = object(self)
  inherit tpl "VS" 1 3 as super

  method spy (filename:string) (sid:sid_t) (fd:fundec)  = function
  |Set _ ->
    (*Find vars in sfd have type bool*)
    let bvs = ref [] in
    ignore(visitCilFunction ((new findBoolVars) bvs) fd);
    let bvs = !bvs in


    (*obtain usuable variables from fd*)
    let vs' = fd.sformals@fd.slocals in
    assert (L.for_all (fun vi -> not vi.vglob) vs');
    let vs' = !extra_vars@vs' in
    
    let vi_pred vi =
      vi.vtype = intType &&
      L.for_all (fun bv -> vi <> bv) bvs &&
      not (in_str "__cil_tmp" vi.vname) &&
      not (in_str "tmp___" vi.vname)
    in
    let vs = L.filter vi_pred vs' in
    let len = L.length vs in
    
    if !vdebug then (
      E.log "%s: found %d/%d avail vars in fun %s [%s]\n"
    	super#cname len (L.length vs') fd.svar.vname 
	(String.concat ", " (L.map (fun vi -> vi.vname) vs))
    );
    
    if len > 0 then(
      write_file_bin (arr_s filename sid super#cid) (A.of_list vs);
      P.sprintf "(%d, %d, %d, %d)" sid super#cid super#level len
    ) else ""

  |_ -> ""


  method mk_instr (ast:file) (main_fd:fundec) (ssid:int) (tpl_id:int) 
    (idxs:int list) (xinfo:string) 
    :(instr -> varinfo list ref -> instr list ref -> instr) =

    let vs:varinfo array = read_file_bin (arr_s ast.fileName ssid tpl_id) in
    let vs:varinfo list = L.map (fun idx ->  vs.(idx) ) idxs in
    let n_vs = L.length vs in 

    E.log "** xinfo %s, |vs|=%d, [%s]\n" xinfo n_vs
      (string_of_list (L.map (fun vi -> vi.vname) vs));

    fun a_i uks instrs -> (
      let mk_exp () = 
	let new_uk uid min_v max_v = mk_uk uid min_v max_v main_fd uks instrs in
	
	let n_uks = succ (L.length vs) in
	let my_uks = L.map (fun uid -> 
	  match uid with
	  |0 -> new_uk uid uk_const_min uk_const_max
	  |_ -> new_uk uid uk_min uk_max
	)  (range n_uks)
	in
	let my_uks = L.map exp_of_vi my_uks in 
	
	let vs = L.map exp_of_vi vs in 
	let uk0,uks' = (L.hd my_uks), (L.tl my_uks) in 
	let r_exp = L.fold_left2 (fun a x y -> 
	  BinOp(PlusA, a, BinOp(Mult, x, y, intType), typeOf uk0))
	  uk0 uks' vs in
	
	r_exp
      in
      
      match a_i with 
      |Set(v,_,l)->Set(v,mk_exp(),l)
      |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)      
    )

end


let tpl_classes:tpl list = 
  [(new tpl_CONSTS:> tpl); 
   ((new tpl_OPS) LOGIC_B :> tpl); 
   ((new tpl_OPS) COMP_B :> tpl); 
   (new tpl_VS:> tpl)]


let spy 
    (filename:string)
    (stmt_ht:(int,stmt*fundec) H.t)
    (sid:sid_t)
    = 
   let s,fd = H.find stmt_ht sid in
    if !vdebug then E.log "Spy stmt %d in fun %s\n%a\n" sid fd.svar.vname dn_stmt s;

   match s.skind with 
   |Instr ins ->
     assert (L.length ins = 1);
     let sinstr = L.hd ins in
     if L.length !tpl_ids > 0 then
       L.map (fun cl -> 
      	 if not (L.mem cl#cid !tpl_ids) then "" else cl#spy filename sid fd sinstr
       )tpl_classes 
	 
     else
       L.map(fun cl -> 
	 if cl#level > !tpl_level then "" else cl#spy filename sid fd sinstr
       )tpl_classes
	 
   |_ -> ealert "no info obtained on stmt %d\n%a" sid dn_stmt s; []


(*runs in parallel*)
let transform 
    (filename:string) 
    (ssid:sid_t) 
    (tpl_id:int) 
    (xinfo:string) 
    (idxs:int list)= 

  let (ast:file),(mainQ_fd:fundec),(tcs:testcase list) =
    read_file_bin (ginfo_s filename) in

  let main_fd = find_fun ast "main" in 

  (*modify statement*)  
  let cl = L.find (fun cl -> cl#cid = tpl_id ) tpl_classes in 
  let mk_instr:(instr-> varinfo list ref -> instr list ref -> instr) = 
    cl#mk_instr ast main_fd ssid tpl_id idxs xinfo in
  let visitor = (new modStmtVisitor) ssid (fun i -> mk_instr i) in
  
  visitCilFileSameGlobals (visitor:> cilVisitor) ast;
  let stat, uks, instrs = visitor#status, visitor#uks, visitor#instrs in 
  if stat = "" then E.s(E.error "stmt %d not modified" ssid);

  (*modify main*)
  let stmts = mk_main main_fd mainQ_fd tcs uks instrs in
  main_fd.sbody.bstmts <- stmts;

  (*add uk's to fun decls and fun calls*)
  let fiv = (new funInstrVisitor) uks in
  visitCilFileSameGlobals (fiv :> cilVisitor) ast;
  visitCilFileSameGlobals ((new instrCallVisitor) uks fiv#ht) ast;

  (*add include "klee/klee.h" to file*)
  ast.globals <- (GText "#include \"klee/klee.h\"") :: ast.globals;
  let fn = transform_s ast.fileName ssid xinfo in

  (*the symbol is useful when parsing the result, don't mess up this format*)
  E.log "Transform success: ## '%s' ##  %s\n" fn stat;
  write_src fn ast


(********************** Prototype **********************)

let () = begin
  E.colorFlag := true;

  let filename = ref "" in
  let inputs   = ref "" in
  let outputs  = ref "" in 
  
  let version = P.sprintf "Vug's bug fixer: v0.1 (Cil version %s)" cilVersion in 

  let arg_descrs = [
    "--debug", Arg.Set vdebug, 
    P.sprintf " shows debug info (default %b)" !vdebug;

    "--no_parallel", Arg.Set no_parallel, 
    P.sprintf " don't use multiprocessing (default %b)" !no_parallel;

    "--no_bugfix", Arg.Set no_bugfix, 
    P.sprintf " don't do bugfix (default %b)" !no_bugfix;
    
    "--no_stop", Arg.Set no_stop, 
    P.sprintf " don't stop after finding a fix (default %b)" !no_stop;

    "--no_global_vars", Arg.Set no_global_vars,
    P.sprintf " don't consider global variables when modify stmts (default %b)" !no_global_vars;

    "--fl_ssids", Arg.String (fun s -> fl_ssids := L.map int_of_string (str_split s)), 
    (P.sprintf "%s" 
       " don't run fault loc, use the given suspicious stmts, e.g., --fl_ssids \"1 3 7\".");

    "--fl_alg", Arg.Set_int fl_alg,
    P.sprintf " use fault localization algorithm, 1 Ochia, 2 Tarantula (default %d)" !fl_alg;
   
    "--top_n_ssids", Arg.Set_int top_n_ssids,
    P.sprintf " consider this number of suspicious stmts (default %d)" !top_n_ssids;

    "--min_sscore", Arg.Set_float min_sscore,
    P.sprintf " consider suspicious stmts with at least this score (default %g)" !min_sscore;
    
    "--tpl_ids", Arg.String (fun s -> tpl_ids := L.map int_of_string (str_split s)),
    " only use these bugfix template ids, e.g., --tpl_ids \"1 3\"";

    "--tpl_level", Arg.Set_int tpl_level,
    P.sprintf " consider fix tpls up to and including this level (default %d)" !tpl_level;

    "--only_spy", Arg.Set only_spy, 
    P.sprintf " only do spy (default %b)" !only_spy;

    "--only_peek", Arg.Set only_peek, 
    P.sprintf " only do peek a given stmt given in --ssid (default %b)" !only_peek;

    (*Options for transforming file (act as a stand alone program)*)
    "--only_transform", Arg.Set only_transform, 
    " stand alone prog to transform code, " ^ 
      "e.g., --only_transform --ssid 1 --tpl 1 --idxs \"3 7 8\" --xinfo z2_c5";

    "--ssid", Arg.Int (fun i -> 
      if i < 0 then raise (Arg.Bad "arg --ssid must be > 0"); 
      ssid:=i
    ), "e.g., --ssid 1";

    "--tpl", Arg.Int (fun i -> 
      if i < 0 then raise (Arg.Bad "arg --tpl must be > 0");
      tpl:=i), 
    " e.g., --tpl 3";

    "--xinfo", Arg.Set_string xinfo, " e.g., --xinfo z2_c5";
    "--idxs", Arg.String (fun s-> 
      let idxs' =  L.map int_of_string (str_split s) in
      if L.exists (fun i -> i < 0) idxs' then (
	raise(Arg.Bad (P.sprintf 
			 "arg --idxs must only contain non-neg ints, [%s]" 
			 (string_of_ints idxs'))));
      idxs:=idxs'), 
    " e.g., --idxs \"3 7 8\""

  ] in


  let handle_arg s =
    if !filename = "" then (
      chk_file_exist s ~msg:"require filename"; filename := s
    )
    else if !inputs = "" then inputs := s
    else if !outputs = "" then outputs := s
    else raise (Arg.Bad "too many input args")
  in

  let usage = P.sprintf "%s\nusage: tf src inputs outputs [options]\n" version in

  Arg.parse (Arg.align arg_descrs) handle_arg usage;

  initCIL();
  Cil.lineDirectiveStyle:= None;
  Cprint.printLn:=false; (*don't print line #*)
  Cil.useLogicalOperators := true; (*Must be set so that Cil doesn't && || *)


  (*Stand alone program for transformation*)
  if !only_transform then (
    transform !filename !ssid !tpl !xinfo !idxs;
    exit 0
  );

  (*** some initialization, getting testcases etc***)
  (*
    Note: src (filename) must be preprocessed by cil by running 
    cilly src.c --save-temps; the result is called src.cil.c

    Also, must have certain format  
    void main(..) {
    printf(mainQ);...
    }
  *)

  chk_file_exist !inputs  ~msg:"require inputs file";
  chk_file_exist !outputs ~msg:"require outputs file";

  (*create a temp dir to process files*)
  let tdir = mk_tmp_dir "cece" "" in
  let fn' = P.sprintf "%s/%s" tdir (Filename.basename !filename) in 
  exec_cmd (P.sprintf "cp %s %s" !filename fn');
  
  let filename,inputs,outputs = fn', !inputs, !outputs in
  at_exit (fun () ->  E.log "Note: temp files created in dir '%s'\n" tdir);

  let tcs = get_tcs filename inputs outputs in
  if L.length tcs = 0 then (ealert "No tcs !"; exit 1);

  let goods, bads = get_goodbad_tcs filename tcs in
  
  let ast = Frontc.parse filename () in 

  visitCilFileSameGlobals (new everyVisitor) ast;
  visitCilFileSameGlobals (new breakCondVisitor :> cilVisitor) ast;

  let stmt_ht:(sid_t,stmt*fundec) H.t = H.create 1024 in 
  visitCilFileSameGlobals ((new numVisitor) stmt_ht:> cilVisitor) ast;
  write_src (ast.fileName ^ ".preproc.c") ast;

  if !only_peek then (
    ignore(visitCilFileSameGlobals ((new peekVisitor) !ssid) ast);
    exit 0);


  (*** fault localization ***)
  let ssids:sid_t list = 
    if L.length !fl_ssids > 0 then !fl_ssids else (
      let ssids' = fault_loc ast goods bads stmt_ht in
      take !top_n_ssids ssids')   (*only consider ntop ones*)
  in 

  if L.length ssids = 0 then (ealert "No suspicious statements !";exit 0);
			      
  (*** transformation and bug fixing ***)
  (*find mainQ*)
  let mainQ_fd = find_fun ast "mainQ" in
  
  if not !no_global_vars then (
    iterGlobals ast (function 
    |GVar (vi,_,_) -> extra_vars := vi::!extra_vars 
    |_ -> ());
    
    if !vdebug then 
      E.log "Consider %d gloval vars [%s]\n" 
	(L.length !extra_vars) 
	(string_of_list (L.map (fun vi -> vi.vname) !extra_vars));
  );

 
  (*spy on suspicious stmts*)
  if !vdebug then E.log "Spy on %d ssids [%s]\n" 
    (L.length ssids) (string_of_list (L.map string_of_int ssids));

  let rs = L.map (spy ast.fileName stmt_ht) ssids in
  let rs' = L.filter (function |[] -> false |_ -> true) rs in
  let rs = L.filter (fun c -> c <> "") (L.flatten rs') in
  ealert "Spy: Got %d infos from %d ssids" (L.length rs) (L.length rs');
  
  if (L.length rs) = 0 then (ealert "No info spied .. Exiting"; exit 0);
    
  (*call Python script to do transformation*)
  let rs = String.concat "; " rs in
  let kr_opts = [if !no_parallel then "--no_parallel" else "";
  		 if !no_bugfix then  "--no_bugfix"  else "";
  		 if !no_stop then "--no_stop" else "";
  		 if !vdebug then "--debug" else "";
  		] in
  let kr_opts = String.concat " " (L.filter (fun o -> o <> "") kr_opts) in

  let cmd = P.sprintf "python %s %s --do_tb \"%s\" %s"
    python_script ast.fileName rs kr_opts in

  if !only_spy then exit 0;

  (*write info to disk for parallelism use*)
  write_file_bin (ginfo_s ast.fileName) (ast,mainQ_fd,tcs); 
  exec_cmd cmd
    

end

(*IMPORTANT: main must be empty and only call mainQ*)


(*TODO:
1. tpl that changes compatible operators 
2. useLogicalOperators ... so that means have to manually break stmt like in bug2  a = x ? b : c 
3. optimize fault loc 

TODO: after getting everything working again:  no need to write vs arr to disk, can just reconstruct it from main_fd
*)
