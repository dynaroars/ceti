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
  E.log "cmd '%s'\n" cmd ;
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
type tpl_t = TP_VS | TP2 | TP_CONSTS  | TP_LOGIC_BOPS |TP_BOPS
let id_of_tpl = function |TP_VS -> 1 |TP2 -> 2 | TP_CONSTS -> 3 | TP_LOGIC_BOPS -> 4 | TP_BOPS -> 5
let tpl_of_id tid = match tid with 
  |1 -> TP_VS 
  |2 -> TP2 
  |3 -> TP_CONSTS 
  |4 -> TP_LOGIC_BOPS 
  |5 -> TP_BOPS 
  |_ -> E.s(E.error "unknown template id %d" tid)

let level_of_tpl = function 
  |TP_CONSTS -> 1 
  |TP2 -> 1
  |TP_LOGIC_BOPS -> 2
  |TP_BOPS -> 2
  |TP_VS -> 3 


(* Specific options for this program *)
let vdebug:bool ref = ref false
let dlog s = if !vdebug then E.log "%s" s else ()
let dalert s = if !vdebug then ealert "%s" s else ()

let bf_template_ids: int list ref = ref []  (*use these bug fixtemplate ids*)


let uk_const_min:int = -100000
let uk_const_max:int =  100000
let uk_min :int = -1 
let uk_max :int =  1

let min_sscore:float ref = ref 0.5
let top_n_ssids:int ref = ref 10
let tpl_level:int ref = ref 3
let extra_vars:varinfo list ref = ref []

let bool_bops_ht:(binop, binop array) H.t = H.create 128
let bool_bops_ht_init () = 
  (*operators that return boolean,  xor, bit and/or are not part of these*)
  L.iter(fun bl ->
    A.iter (fun b -> H.add bool_bops_ht b bl) bl
  )
    [
      [|LAnd; LOr|];
      [|Lt; Gt; Le; Ge; Eq; Ne|]
    ]
    



(******************* Helper Functions *******************)
let mk_vi ?(ftype=TVoid []) fname: varinfo = makeVarinfo true fname ftype

(*av = fname(args)*)
let mk_call ?(ftype=TVoid []) ?(av=None) fname args : instr = 
  let f = var(mk_vi ~ftype:ftype fname) in
  Call(av, Lval f, args, !currentLoc)

let exp_of_vi (vi:varinfo): exp = Lval (var vi)

let string_of_stmt (s:stmt) = Pretty.sprint ~width:80 (dn_stmt () s) 
let string_of_exp (s:exp) = Pretty.sprint ~width:80 (dn_exp () s) 
let string_of_instr (s:instr) = Pretty.sprint ~width:80 (dn_instr () s) 
let string_of_list =   String.concat ", " 


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
  let tE = typeOf e0 in
  L.fold_left (fun e e' -> BinOp(op,e,e',tE)) e0 (L.tl exps)

(*
  apply a list of ops, e.g., 
  apply_bops x y + * [v1;v2] [<; =; >] gives
  (v1 * (e1 < e2)) + (v2* (e1 = e2)) + (v3 * (e1 > e2))
*)
let apply_bops 
    ?(o1:binop=PlusA) ?(o2:binop=Mult) 
    (e1:exp) (e2:exp) 
    (uks:exp list) (ops:binop list) :exp =

  assert (L.length uks > 0);
  assert (L.length uks = L.length ops);
  
  let uk0, uks = L.hd uks, L.tl uks in
  let op0, ops = L.hd ops, L.tl ops in 

  let a = BinOp(o2,uk0,BinOp(op0,e1,e2,intType),intType) in
  let tE = typeOf a in
  L.fold_left2 (fun a op uk ->
    BinOp(o1,a,BinOp(o2, uk, BinOp (op,e1,e2,intType), intType),tE)
  ) a ops uks
    

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

  method mk_stmt s e loc= 
    let fd = match cur_fd with 
      | Some f -> f | None -> E.s(E.error "not in a function") in
    let temp:lval = var(makeTempVar fd (typeOf e)) in
    let i:instr = Set(temp,e,loc) in
    temp, {s with skind = Instr [i]} 

  method can_break e = 
    match e with 
    |Lval _ -> false
    | _-> true

  method vblock b = 
    let action (b: block) : block = 
      let change_stmt (s: stmt) : stmt list = 
	match s.skind with
	|If(e,b1,b2,loc) when self#can_break e -> 
	  let temp, s1 = self#mk_stmt s e loc in
	  let s2 = mkStmt (If(Lval temp,b1,b2,loc)) in

	  if !vdebug then E.log "break %a\n to\n%a\n%a\n" 
	    dn_stmt s dn_stmt s1 dn_stmt s2;

	  [s1;s2]

	(*|While _ may be not really necessary*)

	|Return(e',loc) ->(
	  match e' with 
	  |Some e when self#can_break e -> 
	    let temp, s1 = self#mk_stmt s e loc in
	    let s2 = mkStmt (Return(Some (Lval temp), loc)) in

	    if !vdebug then E.log "break %a\nto\n%a\n%a\n" 
	      dn_stmt s dn_stmt s1 dn_stmt s2;

	    [s1;s2]

	  |_ -> [s]
	)

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
	|Instr(h::t) -> 
	  {s with skind = Instr([h])}::L.map mkStmtOneInstr t
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

  (* List of stmts that can be modified *)
  method can_modify : stmtkind -> bool = function 
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
let stderr_va = mk_vi ~ftype:(TPtr(TVoid [], [])) "_coverage_fout"

let create_fprintf_stmt (sid : sid_t) :stmt = 
  let str = P.sprintf "%d\n" sid in
  let stderr = exp_of_vi stderr_va in
  let instr1 = mk_call "fprintf" [stderr; Const (CStr(str))] in 
  let instr2 = mk_call "fflush" [stderr] in
  mkStmt (Instr([instr1; instr2]))
    
class coverageVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    let action (b: block) :block= 
      let insert_printf (s: stmt): stmt list = 
	if s.sid > 0 then [create_fprintf_stmt s.sid; s]
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
	f.sbody.bstmts <- [create_fprintf_stmt 0] @ f.sbody.bstmts
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
  let new_global = GVarDecl(stderr_va, !currentLoc) in
  ast.globals <- new_global :: ast.globals;

  let lhs = var(stderr_va) in
  let arg1 = Const(CStr(filename_path)) in
  let arg2 = Const(CStr("ab")) in
  let instr = mk_call ~av:(Some lhs) "fopen" [arg1; arg2] in
  let new_s = mkStmt (Instr[instr]) in 

  let fd = getGlobInit ast in
  fd.sbody.bstmts <- new_s :: fd.sbody.bstmts;
  
  write_src filename_cov  ast



(******** Tarantula Fault Loc ********)
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

let tarantula (n_g:int) (ht_g:(int,int) H.t) (n_b:int) (ht_b:(int,int) H.t) : sscore list=
  assert(n_g <> 0);
  assert(n_b <> 0);

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

    let freq_g = (get_n_occur sid ht_g) /. n_g' in
    let freq_b = (get_n_occur sid ht_b) /. n_b' in
    let score = freq_b /. (freq_g +. freq_b)  in
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
  let sscores = tarantula n_g ht_g n_b ht_b in

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

(******************* Tpls for file transformation *******************)

(*Instrument main function*)
class modMainVisitor 
  (mainQ_fd:fundec) 
  (n_uks:int) 
  (tcs:testcase list) 
  (uks:varinfo list ref)
  (tpl:tpl_t)
  = object(self)

  inherit nopCilVisitor

  method mk_uk (main_fd:fundec) (uid:int) (min_max_v:int*int): 
    (varinfo*lval) * (instr list) = 

    let vname = ("uk_" ^ string_of_int uid) in 
    
    (*declare uks*)
    let vi:varinfo = makeLocalVar main_fd vname intType in 
    let lv:lval = var vi in 
    
    (*klee_make_symbolic(&uk,sizeof(uk),"uk") *)
    let mk_sym_instr:instr = mk_call "klee_make_symbolic" 
      [mkAddrOf(lv); SizeOfE(Lval lv); Const (CStr vname)] in
    
    let min_v,max_v = min_max_v in 
    let klee_assert_lb:instr = mk_call "klee_assume" 
      [BinOp(Le,integer min_v,Lval lv, boolTyp)] in 

    let klee_assert_ub:instr = mk_call "klee_assume" 
      [BinOp(Le,Lval lv, integer max_v, boolTyp)] in 
    
    (vi,lv), [mk_sym_instr;  klee_assert_lb; klee_assert_ub]

  (*creates reachability "goal" statement 
    if(e_1,..,e_n){printf("GOAL: uk0 %d, uk1 %d ..\n",uk0,uk1);klee_assert(0);}
  *)
  method mk_goal (exps:exp list) (uks_exps:exp list):stmtkind = 
   
    (*printf("GOAL: uk0 %d uk1 %d .. \n",uk0,uk1,..); *)
    let str = L.map (
      function
      |Lval (Var vi,_) -> vi.vname ^ " %d"
      |_ -> failwith "not poss: uk must be Lval .."
    ) uks_exps in
    let str = "GOAL: " ^ (String.concat ", " str) ^ "\n" in 
    let print_goal:instr = mk_call "printf" ([Const(CStr(str))]@uks_exps) in 
    
    (*klee_assert(0);*)
    let klee_assert_zero:instr = mk_call "klee_assert" [zero] in 
    
    let and_exps = apply_binop LAnd exps in
    If(and_exps, 
       mkBlock [mkStmt (Instr([print_goal; klee_assert_zero]))], 
       mkBlock [], 
       !currentLoc) 


  (*make calls to mainQ on test inp/oupt:
    mainQ_typ temp;
    temp = mainQ(inp0,inp1,..);
    temp == outp
  *)
  method mk_mainQ_call (main_fd:fundec) (tc:testcase) = 

    let mainQ_typ:typ = match mainQ_fd.svar.vtype with 
      |TFun(t,_,_,_) -> t
      |_ -> E.s(E.error "%s is not fun typ %a\n" 
		  mainQ_fd.svar.vname d_type mainQ_fd.svar.vtype)
    in

    let inps,outp = tc in
    
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
      
  method mk_main (main_fd:fundec) : (varinfo list * stmt list) =

    let (min_max_f:int -> int*int), (xcstrs_f:exp list -> instr list) = 
      match tpl with
      |TP_VS -> 
	(function |0 -> uk_const_min, uk_const_max |_ -> uk_min,uk_max ), 
	(fun _ -> [])

      |TP2 -> 
	(fun _ -> 0,1), (*boolean vars*)
	(fun uks ->  (*xor uks, i.e., ^(uk0,uk1,..)*)
	  let xor_exp = apply_binop BXor uks in 
	  let klee_assert_xor:instr = mk_call "klee_assume" [xor_exp] in
	  [klee_assert_xor])


      |TP_CONSTS -> 
	(fun _ -> uk_const_min, uk_const_max), (*const uk*)
	(fun _ -> [])

      |TP_LOGIC_BOPS -> 
	(fun _ -> 0,1), (*boolean vars*)
	(fun uks ->  (*xor uks, i.e., ^(uk0,uk1,..)*)
	  let xor_exp = apply_binop BXor uks in 
	  let klee_assert_xor:instr = mk_call "klee_assume" [xor_exp] in
	  [klee_assert_xor])


      |TP_BOPS -> 
	(fun _ -> 0,1), (*boolean vars*)
	(fun _ -> [])

    in

    (*declare uks*)
    let uks, (instrs1:instr list list) = 
      L.split(L.map (fun uid -> 
	self#mk_uk main_fd uid (min_max_f uid)) (range n_uks)
      ) in 

    let instrs1 = L.flatten instrs1 in 
    let (uks_vi:varinfo list), (uks_lv: lval list) = L.split uks in 
    let uks_exps = L.map (fun lv -> Lval lv) uks_lv in 
    let instrs1 = instrs1@(xcstrs_f uks_exps) in

    (*make big if goal *)
    let instrs2,exps = L.split (L.map (self#mk_mainQ_call main_fd) tcs) in
    let if_skind:stmtkind = self#mk_goal exps uks_exps in
    let instrs_skind:stmtkind = Instr(instrs1@instrs2) in

    uks_vi, [mkStmt instrs_skind; mkStmt if_skind]


  method vfunc fd =
    let action(fd:fundec) : fundec =
      if fd.svar.vname = "main" then (
	let uks',stmts = self#mk_main fd in
	(*fd.sbody.bstmts <- stmts @ fd.sbody.bstmts;*)
	fd.sbody.bstmts <- stmts;
	uks := uks' 
      );
      fd
    in
    ChangeDoChildrenPost(fd,action)
end


(*from  stmt x = .. , vs = [v1,..,vn], uks =[u0,..,vn] returns
  uk0 + u1*v1 + .. + un*vn =>
*)
class modStmtVisitor_VS
  (ssid:int) 
  (vs:varinfo list) 
  (uks:exp list) 
  (modified:bool ref) = object(self)

  inherit nopCilVisitor

  method mk_instr (a_i:instr): instr = 
    match a_i with 
    |Set(v,_,l)->
      assert (L.length vs + 1  = L.length uks);
      let vs = L.map exp_of_vi vs in 
      let uk0,uks' = (L.hd uks), (L.tl uks) in 
      let r_exp = L.fold_left2 (fun a x y -> 
	BinOp(PlusA, a, BinOp(Mult, x, y, intType), typeOf uk0))
	uk0 uks' vs in
      Set(v,r_exp,l)
    |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)

 
  method vstmt (s:stmt) = 
    let action (s: stmt) :stmt = 
      (match s.skind with 
      |Instr instrs when s.sid = ssid & L.length instrs = 1 ->
	let old_i = L.hd instrs in 
	let new_i = self#mk_instr old_i in
	s.skind <- Instr [new_i];
	modified := true;

	if !vdebug then 
	  E.log "Change to '%s' from '%s'\n" (string_of_instr new_i) (string_of_instr old_i)

      |_ -> ()
      );
      s
    in
    ChangeDoChildrenPost(s, action)
end      
let msv_VS = new modStmtVisitor_VS


(*from  stmt x = e1 = e2 returns
  [<=; <] [uk0; uk1, uk2] e1 e2 returns 
  [e1 <= e2; e1 < e2] =>
  uk0 + uk1*(e1 <= e2) + uk2*(e1 < e2) =>
  also insert the constraint only one of uk's can be 1, i.e., uk0^uk1^uk2^uk3
*)

class modStmtVisitor2
  (ssid:int) 
  (bops:binop list) 
  (uks:exp list) 
  (modified:bool ref) = object(self)

  inherit nopCilVisitor

  method mk_instr (a_i:instr) : instr =
    match a_i with
    |Set(v,BinOp (bo,e1,e2,_),l) ->
      assert (L.length bops + 1 = L.length uks);
      let uk0,uks' = (L.hd uks), (L.tl uks) in
      let r_exp = L.fold_left2 (fun a bop uk ->
  	BinOp(PlusA,a,BinOp(Mult, uk, BinOp (bop,e1,e2,intType), intType),intType)
      ) uk0 bops uks' in
      Set(v,r_exp,l)
    |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)
 
  method vstmt (s:stmt) = 
    let action (s: stmt) :stmt = 
      (match s.skind with 
      |Instr instrs when s.sid = ssid & L.length instrs = 1 ->
	let old_i = L.hd instrs in 
	let new_i = self#mk_instr old_i in
	if !vdebug then 
	  E.log "Change to '%s' from '%s'\n" (string_of_instr new_i) (string_of_instr old_i);
	s.skind <- Instr [new_i];
	modified := true
      |_ -> ()
      );
      s
    in
    ChangeDoChildrenPost(s, action)
end      


let logic_bops = [LAnd; LOr]
class modStmtVisitor_LOGIC_BOPS
  (ssid:int) 
  (uks:exp list) 
  (modified:bool ref) = object(self)

  inherit nopCilVisitor

  method mk_exp (e:exp) = 
    let uks:exp array = A.of_list(uks) in
    let idx = ref 0 in
    let rec find_ops e = match e with
      |Const _ -> e
      |Lval _ -> e
      |UnOp(uop,e1,tE) -> UnOp(uop,find_ops e1,tE)
      |BinOp (bop,e1,e2,_) when L.mem bop logic_bops -> 
	let e1' = find_ops e1 in
	let e2' = find_ops e2 in
	let len_ops = L.length logic_bops in
	let uks':exp array = A.sub uks !idx len_ops in
	idx  :=  !idx + len_ops;

	apply_bops e1' e2' (A.to_list uks') logic_bops

      | _ -> ealert "don't know how to deal with exp '%a'" dn_exp e;
	e
    in
    let r_exp = find_ops e in 
    assert (!idx = A.length uks); (*make sure that # of consts = uks*)
    r_exp
    

  method mk_instr (a_i:instr) : instr =
    match a_i with
    |Set(v,e,l) -> Set(v, self#mk_exp e, l)

    |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)
 
  method vstmt (s:stmt) = 
    let action (s: stmt) :stmt = 
      (match s.skind with 
      |Instr instrs when s.sid = ssid & L.length instrs = 1 ->
	let old_i = L.hd instrs in 
	let new_i = self#mk_instr old_i in
	if !vdebug then 
	  E.log "Change to '%s' from '%s'\n" (string_of_instr new_i) (string_of_instr old_i);
	s.skind <- Instr [new_i];
	modified := true
      |_ -> ()
      );
      s
    in
    ChangeDoChildrenPost(s, action)
end  
let msv_LOGIC_BOPS = new modStmtVisitor_LOGIC_BOPS    




class modStmtVisitor_BOPS
  (ssid:int) 
  (idxs:int array) 
  (modified:bool ref) = object(self)

  inherit nopCilVisitor

  val cname = "BOPS"

  method mk_exp (e:exp) = 
    E.log "idxs %s\n" (string_of_list (L.map string_of_int (A.to_list idxs)));

    let idx = ref 0 in

    (*H.iter (fun a b -> E.log "%s %d\n" (string_of_binop a) (A.length b)) bool_bops_ht;*)

    let rec find_ops e = match e with
      |Const _ -> e
      |Lval _ -> e
      |UnOp(uop,e1,tE) -> UnOp(uop,find_ops e1,tE)
      |BinOp (bop,e1,e2,tE) when H.mem bool_bops_ht bop -> 
	
	let arr:binop array = H.find bool_bops_ht bop in
	let bop':binop = arr.(idxs.(!idx)) in
	incr idx;

	let e1' = find_ops e1 in
	let e2' = find_ops e2 in
	BinOp(bop',e1',e2',tE)

      | _ -> 
	ealert "%s: don't know how to deal with exp '%a'" cname dn_exp e;
	e
    in
    let r_exp = find_ops e in 
    assert (!idx = A.length idxs); (*make sure that all idxs are used*)
    r_exp
    

  method mk_instr (a_i:instr) : instr =
    match a_i with
    |Set(v,e,l) -> Set(v,self#mk_exp e,l)

    |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)
 
  method vstmt (s:stmt) = 
    let action (s: stmt) :stmt = 
      (match s.skind with 
      |Instr instrs when s.sid = ssid & L.length instrs = 1 ->
	let old_i = L.hd instrs in 
	let new_i = self#mk_instr old_i in
	if !vdebug then 
	  E.log "Change to '%s' from '%s'\n" (string_of_instr new_i) (string_of_instr old_i);
	s.skind <- Instr [new_i];
	modified := true
      |_ -> ()
      );
      s
    in
    ChangeDoChildrenPost(s, action)
end  
let msv_BOPS = new modStmtVisitor_BOPS  

(*from smt x = e , returns x = e' where e' is similar to e 
  but with all const in e replaced with uk's *)
class modStmtVisitor_CONSTS 
  (ssid:int)
  (uks:exp list)
  (modified:bool ref)   = object (self)
  inherit nopCilVisitor 
    
  method mk_exp (e:exp) =
    let uks:exp array = A.of_list(uks) in
    let idx = ref 0 in
    let rec find_const e = match e with
      |Const _ -> let e' = uks.(!idx) in incr idx; e'
      |Lval _ -> e
      |UnOp (uop,e1,ty) -> UnOp(uop,find_const e1,ty)
      |BinOp (bop,e1,e2,ty) -> BinOp(bop,find_const e1, find_const e2, ty)
      | _ -> ealert "don't know how to deal with exp '%a'" dn_exp e;
	e
    in

    let r_exp = find_const e in
    assert (!idx = A.length uks); (*make sure that # of consts = uks*)
    r_exp
      

  method mk_instr (a_i:instr) : instr =
    match a_i with
    |Set(v,e,l) -> Set(v, self#mk_exp e, l)
      
    |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)

  method vstmt (s:stmt) = 
    let action (s: stmt) :stmt = 
      (match s.skind with 
      |Instr instrs when s.sid = ssid ->
	assert (L.length instrs = 1);
	let old_i = L.hd instrs in 
	let new_i = self#mk_instr old_i in
	if !vdebug then 
	  ealert "Change to '%s' from '%s'\n" (string_of_instr new_i) (string_of_instr old_i);
	s.skind <- Instr [new_i];
	modified := true
      |_ -> ()
      );
      s
    in
    ChangeDoChildrenPost(s, action)  
  end

let msv_CONSTS = new modStmtVisitor_CONSTS



class testV = object(self)
  inherit nopCilVisitor
  method vstmt s = 
    if s.sid > 0 then
      E.log "ssid %d\n%a\n" s.sid dn_stmt s;
    DoChildren
end
  
(******************* Transforming File *******************)
(*declare and set constraints on uk:
  int uk;
  klee_make_symbol(&uk,sizeof(uk),"uk");
  mk_klee_assume(min<=uk<=max);
*)



(*sets of compatible operators so we can change, e.g., <= to >= but not <= to && *)
let ops_comp = [Gt;Ge;Eq;Ne;Lt;Le]
let ops_logical = [LAnd; LOr]
let ops_bitwise = [BAnd; BOr; BXor; Shiftlt; Shiftrt]



(*add uk's to function args, e.g., fun(int x, int uk0, int uk1);*)
class funInstrVisitor (uks:varinfo list) (funs_ht:(string, unit) H.t) = object

  inherit nopCilVisitor
  method vfunc fd = 
    if fd.svar.vname <> "main" then (
      setFormals fd (fd.sformals@uks) ;
      H.add funs_ht fd.svar.vname () 
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

(*runs in parallel*)
let transform 
    (filename:string) 
    (ssid:sid_t) 
    (tpl_id:int) 
    (xinfo:string) 
    (idxs:int list)= 
  (*read in saved files*)

  let (ast:file),(mainQ:fundec),(tcs:testcase list) =
    read_file_bin (ginfo_s filename) in

  let tpl = tpl_of_id tpl_id in

  let (n_uks:int), (visitor:exp list -> bool ref -> cilVisitor) = 
    match tpl with
    |TP_VS ->
      let vs:varinfo array = read_file_bin (arr_s filename ssid tpl_id) in
      let vs:varinfo list = L.map (fun idx ->  vs.(idx) ) idxs in
      let len = L.length vs in 
      E.log "** xinfo %s, |vs|=%d, [%s]\n" xinfo len
	(string_of_list (L.map (fun vi -> vi.vname) vs));
      
      succ len,
      fun uks modified -> (msv_VS ssid vs uks modified :> cilVisitor)

      
    |TP2 ->
      let bops:binop array = read_file_bin (arr_s filename ssid tpl_id) in
      let bops:binop list = L.map (fun idx -> bops.(idx)) idxs in
      let len = L.length bops in
      E.log "** xinfo %s, |bops|=%d [%s]\n" xinfo len
	(string_of_list (L.map string_of_binop bops));
      
      succ len,
      fun uks modified -> ((new modStmtVisitor2) ssid bops uks modified :> cilVisitor)
	
	
    |TP_CONSTS ->
      assert (L.length idxs = 1);
      let n_consts = L.hd idxs in
      E.log "** xinfo %s, n_consts=%d\n" xinfo n_consts;
      
      n_consts,
      fun uks modified -> (msv_CONSTS ssid uks modified :> cilVisitor)

    |TP_LOGIC_BOPS ->
      assert (L.length idxs = 1);
      let n_bops = L.hd idxs in
      E.log "** xinfo %s, n_bops=%d\n" xinfo n_bops;
      
      n_bops,
      fun uks modified -> (msv_LOGIC_BOPS ssid uks modified :> cilVisitor) 

    |TP_BOPS ->       
      (*idxs = [3, 5, 7]*)
      E.log "** xinfo %s, |idxs|=%d, [%s]\n" xinfo (L.length idxs) 
	(string_of_list (L.map string_of_int idxs));
      
      0,
      fun _ modified -> (msv_BOPS ssid (A.of_list idxs) modified :> cilVisitor) 
      
  in


  (*stay with this order, main, stmt, then others*)

  (*instr main*)
  let (uks:varinfo list ref) = ref [] in
  visitCilFileSameGlobals ((new modMainVisitor) mainQ n_uks tcs uks tpl :> cilVisitor) ast;
  let uks:varinfo list = !uks in
  assert (L.length uks = n_uks) ;
  if !vdebug then E.log "create %d uks\n" n_uks;
  

  (*modify suspStmt*)
  let modified = ref false in
  visitCilFileSameGlobals(visitor (L.map exp_of_vi uks) modified) ast;
  if not !modified then E.s(E.error "stmt %d not modified" ssid);

  (*add uk's to fun decls and fun calls*)
  let funs_ht = H.create 1024 in
  visitCilFileSameGlobals ((new funInstrVisitor) uks funs_ht) ast;
  visitCilFileSameGlobals ((new instrCallVisitor) uks funs_ht) ast;

  (*add include "klee/klee.h" to file*)
  ast.globals <- (GText "#include \"klee/klee.h\"") :: ast.globals;
  let fn = transform_s ast.fileName ssid xinfo in
  write_src fn ast



(*determine tpl suitable for this statement*)
let spy_LOGIC_BOPS: (instr -> 'a option) = function
  |Set (_,e,_) ->
    let rec find_ops ctr e: int = match e with
      |Const _ -> ctr
      |Lval  _ -> ctr
      |UnOp(_,e1,_) -> find_ops ctr e1
      |BinOp (bop,e1,e2,_) when L.mem bop logic_bops -> 
	L.length logic_bops + find_ops ctr e1 + find_ops ctr e2

      | _ ->
    	ealert "don't know how to deal with exp '%a'" dn_exp e;
    	ctr
    in
    let n_ops:int = find_ops 0 e in
    E.log "n_ops %d\n" n_ops;
    Some (TP_LOGIC_BOPS,
	  n_ops,
	  fun _ ->  ())

  |_ -> None





class virtual tpl (cname:string) (cid:int) (level:int)= 
object
  val cname = cname
  val cid = cid
  val level = level

  method cid : int = cid
  method level: int = level

  method virtual spy : string -> sid_t -> fundec -> instr -> string
end 


class tpl_CONSTS = 
object(self)
  inherit tpl "CONSTS" 3 1 as super

  method spy (filename:string) (sid:sid_t) (fd:fundec) = function
  |Set (_,e,_) ->
    let rec find_const ctr e: int = match e with
      |Const _ -> succ ctr
      |Lval _ -> ctr
      |UnOp(_,e1,_) -> find_const ctr e1
      |BinOp (_,e1,e2,_) -> find_const ctr e1 + find_const ctr e2

      | _ -> 
	ealert "don't know how to deal with exp '%a'" dn_exp e;
    	ctr
    in
    let n_consts:int = find_const 0 e in
    if n_consts > 0 then 
      P.sprintf "(%d, %d, %d)" sid super#cid n_consts
    else
      ""

  |_ -> ""

end


class tpl_VS = 
object(self)
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
      let vs_names =String.concat ", " (L.map (fun vi -> vi.vname) vs) in
      E.log "Using %d/%d avail vars in fun %s\n[%s]\n"
    	len (L.length vs') fd.svar.vname vs_names
    );
    
    if L.length vs > 0 then(
      write_file_bin (arr_s filename sid super#cid) (A.of_list vs);
      P.sprintf "(%d, %d, %d)" sid super#cid (L.length vs)
    ) else ""

  |_ -> ""


end

let tpl_classes:tpl list = 
  [(new tpl_CONSTS:> tpl); 
   (new tpl_VS:> tpl)]


let spy 
    (bf_tpls:int list)
    (filename:string)
    (stmt_ht:(int,stmt*fundec) H.t)
    (sid:sid_t)
    = 
   let s,fd = H.find stmt_ht sid in
    if !vdebug then E.log "Spy stmt %d in fun %s\n%a\n" sid fd.svar.vname dn_stmt s;

   match s.skind with 
   |Instr instrs ->
     assert (L.length instrs = 1);
     let sinstr = L.hd instrs in
     E.log "spying on %a\n" dn_instr sinstr;
     
     if L.length bf_tpls <> 0 then
       L.map (fun cl -> 
      	 if not (L.mem cl#cid bf_tpls) then "" else cl#spy filename sid fd sinstr
       )tpl_classes 
	 
     else
       L.map(fun cl -> 
	 if cl#level > !tpl_level then "" else cl#spy filename sid fd sinstr
       )tpl_classes
	 
   |_ -> 
     ealert "no info obtained on stmt %d\n%a" sid dn_stmt s;
     []
  
let tbf
    (filename:string) 
    (mainQ:fundec) 
    (ssids:sid_t list)
    (tcs:testcase list)
    (stmt_ht:(int,stmt*fundec) H.t)
    (bf_tpls:int list)
    : string list =

  E.log "*** TBF ***\n";

  assert (L.length ssids > 0);

  (*iterate through top n ssids*)
  let ssids = take !top_n_ssids ssids in

  if !vdebug then E.log "Obtain info from %d ssids\n" (L.length ssids);

  let rs = L.map (spy bf_tpls filename stmt_ht) ssids in
  let rs' = L.filter (function |[] -> false |_ -> true) rs in
  let rs = L.filter (fun c -> c <> "") (L.flatten rs') in
  ealert "Spy: Got %d info from %d ssids" (L.length rs) (L.length rs');
  
  if (L.length rs) < 1 then(
    ealert "No stmts for transformation .. Exiting\n";
    exit 0
  );

  rs


(********************** Prototype **********************)

let () = begin

  let filename = ref "" in
  let inputs   = ref "" in
  let outputs  = ref "" in 

  let fl_ssids = ref "" in (*manually provide fault loc info*)
  let bf_tpls = ref "" in 

  let no_global_vars = ref false in
  let no_parallel = ref false in 
  let no_bugfix = ref false in 
  let no_break = ref false in 


  
  let do_ssid = ref (-1) in  (*only do transformation on vs_idxs*)
  let tpl = ref 0 in 
  let xinfo = ref "" in  (*helpful info for debuggin*)
  let idxs = ref "" in 

  let only_spy = ref false in
  
  let version = P.sprintf "Vug's bug fixer: v0.1 (Cil version %s)" cilVersion in 

  let argDescr = [
    "--debug", Arg.Set vdebug, 
    P.sprintf " shows debug info (default %b)" !vdebug;

    "--no_bugfix", Arg.Set no_bugfix, 
    P.sprintf " don't do bugfix (default %b)" !no_bugfix;
    
    "--no_break", Arg.Set no_break, 
    P.sprintf " don't do break after finding at least a bugfix (default %b)" !no_break;

    "--no_global_vars", Arg.Set no_global_vars,
    P.sprintf " don't consider global variables when modify stmts (default %b)" !no_global_vars;

    "--fl_ssids", Arg.Set_string fl_ssids, 
    (P.sprintf "%s\n%s" 
       " don't run fault loc, use the given suspicious stmts, e.g., --fl_ssids \"1 3 7\"."
       "Trick: if want to stop process after fault loc then do --fl_ssids \" \"");

    "--bf_tpls", Arg.Set_string bf_tpls, 
    " only use the given buf fix templates, e.g., --bf_tpls \"1 3\"";

    "--no_parallel", Arg.Set no_parallel, 
    P.sprintf " don't use multiprocessing (default %b)" !no_parallel;

    "--only_spy", Arg.Set only_spy, 
    P.sprintf " only do spy (default %b)" !only_spy;
    
    "--top_n_ssids", Arg.Set_int top_n_ssids,
    P.sprintf " consider this number of suspicious stmts (default %d)" !top_n_ssids;

    "--tpl_level", Arg.Set_int tpl_level,
    P.sprintf " consider fix tpls up to and including this level (default %d)" !tpl_level;

    "--min_sscore", Arg.Set_float min_sscore,
    P.sprintf " consider suspicious stmts with at least this score (default %g)" !min_sscore;
    
      
    "--do_ssid", Arg.Set_int do_ssid, 
    " stand alone prog to modify code wrt this statement id, " ^ 
      "e.g., --do_ssid 1 --tpl 1 --xinfo z2_c5 --idxs \"3 7 8\"";
    "--tpl", Arg.Set_int tpl, " e.g., --tpl z2_c5";
    "--xinfo", Arg.Set_string xinfo, " e.g., --xinfo z2_c5";
    "--idxs", Arg.Set_string idxs, " e.g., --idxs \"3 7 8\""




  ] in

  let usage = P.sprintf "%s\nusage: tf src inputs outputs [options]\n" version in

  let handleArg s =
    if !filename = "" then filename := s
    else if !inputs = "" then inputs := s
    else if !outputs = "" then outputs := s
    else raise (Arg.Bad "too many input args")
  in

  Arg.parse (Arg.align argDescr) handleArg usage;
  E.colorFlag := true;

  chk_file_exist !filename ~msg:"require filename";

  (*intialize global vars*)
  bool_bops_ht_init ();

  initCIL();
  Cil.lineDirectiveStyle:= None;
  (*Cprint.printLn:=false; (*don't print line # *)*)
  Cil.useLogicalOperators := true; (*don't break && || *)


  (*Stand alone program for transformation*)
  if !do_ssid > -1 then (
    let ssid   = !do_ssid in
    let tpl = !tpl in
    let xinfo  = !xinfo in 
    let idxs =  L.map int_of_string (str_split !idxs) in

    assert (ssid > 0);
    assert (tpl > 0);
    assert (L.length idxs >= 0 && L.for_all (fun idx -> idx >= 0) idxs);

    transform !filename ssid tpl xinfo idxs;
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
  let stmt_ht:(sid_t,stmt*fundec) H.t = H.create 1024 in 
  visitCilFileSameGlobals (new everyVisitor) ast;
  visitCilFileSameGlobals (new breakCondVisitor :> cilVisitor) ast;
  visitCilFileSameGlobals ((new numVisitor) stmt_ht:> cilVisitor) ast;


  (*** fault localization ***)
  let ssids:sid_t list = 
    if !fl_ssids = "" then fault_loc ast goods bads stmt_ht 
    else L.map int_of_string (str_split !fl_ssids) 
  in 

  if L.length ssids = 0 then (
    ealert "No suspicious statements !";
    exit 0);


  (*** transformation and bug fixing ***)

  (*find mainQ*)
  let mainQ_fd = 
    let qf = ref None in
    iterGlobals ast (function 
    |GFun(f,_) when f.svar.vname = "mainQ" -> qf := Some f
    |_ -> ()
    );
    match !qf with
    |Some f -> f
    |None -> E.s (E.error "'%s' does not have a mainQ function\n" ast.fileName)
  in

  
  if not !no_global_vars then (
    iterGlobals ast (function 
    |GVar (vi,_,_) -> extra_vars := vi::!extra_vars 
    |_ -> ());
    
    if !vdebug then 
      E.log "Consider %d gloval vars\n%s\n" 
	(L.length !extra_vars) 
	(string_of_list (L.map (fun vi -> vi.vname) !extra_vars));
  );

  (*write info to disk for parallelism use*)
  write_src (ast.fileName ^ ".preproc.c") ast;
  write_file_bin (ginfo_s ast.fileName) (ast,mainQ_fd,tcs); 
  
  let rs = tbf ast.fileName mainQ_fd ssids tcs stmt_ht  
    (L.map int_of_string (str_split !bf_tpls)) in

  if !only_spy then exit 0;

  (*call Python script to do transformation*)
  let rs = String.concat "; " rs in
  let kr_opts = [if !no_parallel then "--no_parallel" else "";
  		 if !no_bugfix then  "--no_bugfix"  else "";
  		 if !no_break then "--no_break" else "";
  		 if !vdebug then "--debug" else "";
  		] in
  let kr_opts = String.concat " " (L.filter (fun o -> o <> "") kr_opts) in

  let cmd = P.sprintf "python klee_reader.py %s --do_tbf \"%s\" %s"
    ast.fileName rs kr_opts in

  exec_cmd cmd
    

end

(*IMPORTANT: main must be empty and only call mainQ*)


(*TODO:
1. tpl that changes compatible operators 
2. useLogicalOperators ... so that means have to manually break stmt like in bug2  a = x ? b : c 
3. optimize fault loc 


*)
