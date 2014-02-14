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

let forceOption (ao : 'a option) : 'a =
  match ao with  | Some a -> a | None -> raise(Failure "forceOption")

let write_file_str (filename:string) (content:string): unit = 
  let fout = open_out filename in
  P.fprintf fout "%s" content; 
  close_out fout;
  E.log "write_file_str: \"%s\"\n" filename

let write_file_bin (filename:string) content: unit = 
  let fout = open_out_bin filename in
  Marshal.to_channel fout content [];
  close_out fout;
  E.log "write_file_bin: \"%s\"\n" filename

let read_file_bin (filename:string) =
  let fin = open_in_bin filename in
  let content = Marshal.from_channel fin in
  close_in fin;
  E.log "read_file: \"%s\"\n" filename;
  content

let write_src ?(use_stdout=false) (filename:string) (ast:file): unit = 
  let df oc =  dumpFile defaultCilPrinter oc filename ast in
  if use_stdout then df stdout else (
    let fout = open_out filename in
    df fout;
    close_out fout;
    E.log "write_src: \"%s\"\n" filename
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
let mk_tmp_dir ?(use_time=true) ?(temp_dir="") dprefix dsuffix = 
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

let str_split s:string list =  Str.split (Str.regexp "[ \t]+")  s

  
(* Specific options for this program *)
let vdebug:bool ref = ref false
let vlog s = if !vdebug then E.log "%s" s else ()


let uk0_min:int = -100000
let uk0_max:int =  100000
let uk_min :int = -1 
let uk_max :int =  1

let min_sscore:float ref = ref 0.5
let top_n_ssids:int ref = ref 10
let extra_vars:varinfo list ref = ref []

let boolTyp:typ = intType

(*filename formats*)
let ginfo_s = P.sprintf "%s.info" (*f.c.info*)
let arr_s = P.sprintf "%s.s%d.arr" (*f.c.sid1.arr*)
let transform_s = P.sprintf "%s.s%d.%s.tf.c" (*f.c.s5.z3_c2.tf.c*)

(*commands*)
let gcc_cmd = P.sprintf "gcc %s -o %s >& /dev/null"

type inp_t = int list 
type outp_t = int 
type testcase = inp_t * outp_t
type sid_t = int
type vb_l_t  = VL of varinfo list | BL of binop list
type vb_a_t  = VA of varinfo array | BA of binop array
  
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

let string_of_binop bop = 
  match bop with
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
    
  |_ -> failwith "unknown binop"
  
let get_names (vs:vb_l_t) : (string list) = 
  match vs with
  |VL l -> L.map (fun vi -> vi.vname) l
  |BL l -> L.map string_of_binop l
  

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

(*apply binary op to a list, e.g, + [v1,..,vn] =>  v1 + .. + vn*)
let apply_binop (bop:binop) (exps:exp list): exp = 
  assert (L.length exps > 0);
  let e0 = L.hd exps in 
  if L.length exps = 1 then e0
  else(
    let typ = typeOf e0 in
    L.fold_left (fun e e' -> BinOp(bop,e,e',typ)) e0 (L.tl exps)
  )


let isSimpleExp e = 
  match e with
  | Const _ | Lval _ -> true 
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

  vlog (P.sprintf "read tcs from '%s' and '%s' for program '%s'\n" inputs outputs filename);

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
  assert(L.length tcs > 0);

  E.log "|tcs|=%d\n" (L.length tcs);
  (*E.log "%s\n" (string_of_tcs tcs);*)

  tcs

(******************* Initialize *******************)
(*break conditional / loop guard to 
  if(complex_exp) to 
  int tmp = complex_exp; 
  if(tmp) 
  Assigning id's to stmts 
*)



(*Attempt to convert global variables to local,  that's because KLEE runs much faster without global variables*)


class breakCondVisitor = object(self)
  inherit nopCilVisitor

  val mutable cur_fd = None
    
  method vfunc f = cur_fd <- (Some f); DoChildren

  method mk_stmt s e loc= 
    let temp:lval = var(makeTempVar (forceOption cur_fd) (typeOf e)) in
    let i:instr = Set(temp,e,loc) in
    temp, {s with skind = Instr [i]} 


  (*Note: won't modify and hence won't repair 'simple' expr e.g., 
    if(const|val), return(const|val)*)  

  method vblock b = 
    let action (b: block) : block = 
      let change_stmt (s: stmt) : stmt list = 
	match s.skind with
	|If(e,b1,b2,loc) when not (isSimpleExp e) -> 
	  let temp, s1 = self#mk_stmt s e loc in
	  let s2 = mkStmt (If(Lval temp,b1,b2,loc)) in

	  vlog (P.sprintf "break %s\n to\n %s\n" 
		  (string_of_stmt s) 
		  ((string_of_stmt s1) ^ "\n" ^(string_of_stmt s2)));

	  [s1;s2]

	(*|While _ may be not really necessary*)

	|Return(e',loc) ->(
	  match e' with 
	  |Some e when not (isSimpleExp e) -> 
	    let temp, s1 = self#mk_stmt s e loc in
	    let s2 = mkStmt (Return(Some (Lval temp), loc)) in
	    vlog (P.sprintf "breaking %s\n to\n %s\n" 
		    (string_of_stmt s) 
		    ((string_of_stmt s1) ^ "\n" ^(string_of_stmt s2)));
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
	  H.add ht mctr (s, forceOption cur_fd);
	  mctr <- succ mctr
	)
	else s.sid <- 0;  (*Anything not considered has sid 0 *)
      in 
      L.iter change_sid b.bstmts; 
      b
    in 
    ChangeDoChildrenPost(b, action)



end


let preprocess (ast:file) (stmt_ht:(int,stmt*fundec) H.t):fundec= 
  E.log "*** Preprocessing***\n";
 
  visitCilFileSameGlobals (new everyVisitor) ast;
  visitCilFileSameGlobals (new breakCondVisitor :> cilVisitor) ast;

  visitCilFileSameGlobals ((new numVisitor) stmt_ht:> cilVisitor) ast;

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


  E.log "*** Proprocessing .. done ***\n";
  mainQ_fd


let initialize_files filename inputs outputs = 
  let tdir = mk_tmp_dir "cece" "" in

  let ck_cp fn msg = 
    let fn' = P.sprintf "%s/%s" tdir (Filename.basename fn) in 
    exec_cmd (P.sprintf "cp %s %s" fn fn');
    fn'
  in
  
  let filename = ck_cp filename "src" in
  let inputs = ck_cp inputs "inputs" in
  let outputs = ck_cp outputs "outputs" in 
  tdir,filename, inputs, outputs


let cleanup tdir = 
  E.log "Note: temp files created in dir '%s'\n" tdir 
    

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
  
  vlog content;
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


let checkInit (filename:string) (tcs:(int list * int) list)  = 
  (*do some prelim checking and obtain good/test testcases*)
  E.log "*** Init Check ***\n";

  (*compile and run program on tcs*)
  let prog:string = compile filename in

  let testscript =  filename ^ ".sh" in
  let prog_output:string = filename ^ ".routputs" in
  mk_run_testscript testscript prog prog_output tcs;

  (*check if prog passes all inputs:
    If yes then exit. If no then there's bug to fix*)
  let goods,bads = compare_outputs prog_output tcs in 
  let nbads = L.length bads in
  if nbads = 0 then (E.log "All tests passed .. no bug found .. done\n"; exit 0)
  else (E.log "%d tests failed ... bug found .. processing\n" nbads);
  
  E.log "*** Init Check .. done ***\n";
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

  vlog (P.sprintf "** Analyze execution path '%s'\n" filename);
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

  (*keep scores > 0*)
  let rs = L.filter (fun (_,score) -> score >= !min_sscore) rs in 
  rs


let fault_loc (ast:file) (goods:testcase list) (bads:testcase list) 
    (stmt_ht:(sid_t,stmt*fundec) H.t): sid_t list = 
  E.log "*** Fault Localization ***\n";

  assert (L.length goods > 0) ;
  assert (L.length bads  > 0) ;


  let tdir = mk_tmp_dir 
    ~use_time:false ~temp_dir:(Filename.dirname ast.fileName) "fautloc" "" in
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

  E.log "===== FL results for %d stmts =====\n" (L.length sscores);
  L.iter (fun (sid,score) -> 
    let s,f = H.find stmt_ht sid in
    E.log "sid %d in fun '%s' has score %g\n%a\n" sid f.svar.vname score dn_stmt s
  ) sscores;

  let ssids:sid_t list = L.map fst sscores in  

  E.log "*** Fault Localization .. done ***\n";
  ssids


(******************* Transforming File *******************)
(*declare and set constraints on uk:
  int uk;
  klee_make_symbol(&uk,sizeof(uk),"uk");
  mk_klee_assume(min<=uk<=max);
*)



let mk_uk (main_fd:fundec) (opt:int) (uid:int) : (varinfo*lval) * (instr list) = 
  let mk_klee_asserts lv min_ max_ = 
    let klee_assert_lb:instr = mk_call "klee_assume" 
      [BinOp(Le,integer min_,Lval lv, boolTyp)] in 
    let klee_assert_ub:instr = mk_call "klee_assume" 
      [BinOp(Le,Lval lv, integer max_, boolTyp)] in 
    [klee_assert_lb; klee_assert_ub]
  in

  let vname = ("uk_" ^ string_of_int uid) in 
  
  (*declare uks*)
  let vi:varinfo = makeLocalVar main_fd vname intType in 
  let lv:lval = var vi in 
  
  (*klee_make_symbolic(&uk,sizeof(uk),"uk") *)
  let mk_sym_instr:instr = mk_call "klee_make_symbolic" 
    [mkAddrOf(lv); SizeOfE(Lval lv); Const (CStr vname)] in
  
  let cstrs = 
    if opt = 1 then ( 
      let min_,max_ = if uid = 0 then uk0_min,uk0_max else uk_min,uk_max in
      mk_klee_asserts lv min_ max_ (*int vars within a rage*)
    )
    else mk_klee_asserts lv 0 1 (*bool var*)
  in 
  
  (vi,lv), mk_sym_instr::cstrs


(*Instrument main function*)
class mainVisitor (mainQ_fd:fundec) (n_uks:int) (tcs:testcase list) 
  (uks:varinfo list ref)
  (opt:int)
  = object(self)

  inherit nopCilVisitor


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

    let uks, (instrs1:instr list list) = 
      L.split(L.map (mk_uk main_fd opt) (range n_uks)) in 
    let instrs1 = L.flatten instrs1 in 

    let (uks_vi:varinfo list), (uks_lv: lval list) = L.split uks in 
    
    (*declare uks and setup big if cond*)
    let uks_exps = L.map (fun lv -> Lval lv) uks_lv in 

    (*xor uks, i.e., ^(uk0,uk1,..)*)
    let xinstrs:instr list = 
      if opt = 2 then (
	let xor_exp = apply_binop BXor uks_exps in 
	let klee_assert_xor:instr = mk_call "klee_assume" [xor_exp] in
	[klee_assert_xor]
      ) else []
    in
    let instrs1 = instrs1@xinstrs in
    
    (*make mainQ calls and expressions based on testcases*)
    
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


(*sets of compatible operators so we can change, e.g., <= to >= but not <= to && *)
let ops_comp = [Gt;Ge;Eq;Ne;Lt;Le]
let ops_logical = [LAnd; LOr]
let ops_bitwise = [BAnd; BOr; BXor; Shiftlt; Shiftrt]


class modStmtVisitor 
  (ssid:int) 
  (vs:vb_l_t) 
  (uks:varinfo list) 
  (modified:bool ref) = object(self)

  inherit nopCilVisitor
  
  (*from stmt x = .., create a new assignment stmt x = v0 + uk1*v1 + uk2*v2 *)
  method mk_instr1 (a_i:instr) (vis:varinfo list): instr = 
    match a_i with 
    |Set(v,_,l)->
      assert (L.length vis + 1  = L.length uks);
      let uks = L.map exp_of_vi uks in
      let vis = L.map exp_of_vi vis in 
      let uk0,uks' = (L.hd uks), (L.tl uks) in 
      let r_exp = L.fold_left2 (fun a x y -> 
	BinOp(PlusA, a, BinOp(Mult, x, y, intType), typeOf uk0))
	uk0 uks' vis in
      Set(v,r_exp,l)
    |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)

  (*from  stmt x = e1 = e2 returns
    [<=; <] [uk0; uk1, uk2] e1 e2 returns 
    [e1 <= e2; e1 < e2] =>
    uk0 + uk1*(e1 <= e2) + uk2*(e1 < e2) =>
    also insert the constraint only one of uk's can be 1, i.e., uk0^uk1^uk2^uk3
  *)
  method mk_instr2 (a_i:instr) (bops:binop list): instr =
    match a_i with
    |Set(v,BinOp (bo,e1,e2,_),l) ->
      assert (L.length bops + 1 = L.length uks);
      let uks = L.map exp_of_vi uks in
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
	let new_i =  
	  match vs with
	  |VL l -> self#mk_instr1 old_i l
	  |BL l -> self#mk_instr2 old_i l
	in
	vlog (P.sprintf "Change to '%s' from '%s'\n" (string_of_instr new_i) (string_of_instr old_i));
	s.skind <- Instr [new_i];
	modified := true
      |_ -> ()
      );
      s
    in
    ChangeDoChildrenPost(s, action)
end      


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
    (ast:file) (mainQ:fundec)
    (tcs:testcase list) 
    (xinfo:string)
    (ssid:sid_t)
    (cvs:vb_l_t)  =
  
  let opt, cvs_len =
    match cvs with
    |VL l -> 1, L.length(l)
    |BL l -> 2, L.length(l)
  in

  E.log "** comb %s. |vs|=%d [%s]\n" xinfo cvs_len
    (String.concat ", " (get_names cvs));

  let n_uks = succ cvs_len in
  let (uks:varinfo list ref) = ref [] in
  
  (*instr main*)
  visitCilFileSameGlobals ((new mainVisitor) mainQ n_uks tcs uks opt :> cilVisitor) ast;
  let uks = !uks in
  assert (L.length uks = n_uks) ;

  (*modify suspStmt: stay with this order, mod sstmt first before doing others*)
  let modified = ref false in
  visitCilFileSameGlobals ((new modStmtVisitor) ssid cvs uks modified :> cilVisitor) ast;
  assert (!modified);

  (*add uk's to fun decls and fun calls*)
  let funs_ht = H.create 1024 in
  visitCilFileSameGlobals ((new funInstrVisitor) uks funs_ht) ast;
  visitCilFileSameGlobals ((new instrCallVisitor) uks funs_ht) ast;

  (*add include "klee/klee.h" to file*)
  ast.globals <- (GText "#include \"klee/klee.h\"") :: ast.globals;
  write_src (transform_s ast.fileName ssid xinfo) ast



let spy_sid (ast:file) (s:stmt) (fd:fundec) = 

  match s.skind with 
  |Instr instrs when L.length instrs = 1 -> (
    let i = L.hd instrs in
    match i with

    (*important, can only do things like t = x && y ,  but not t = (x && y) || z *)
    |Set (_,BinOp (bop,e1,e2,_),_) when L.mem bop ops_comp  && isSimpleExp e1 && isSimpleExp e2 -> 
      let bops = BL (L.filter (fun bop' -> bop <> bop') ops_comp) in
      vlog (P.sprintf "[%s]\n" (String.concat ", " (get_names bops)));
      bops

    |Set (_,BinOp (bop,e1,e2,_),_) when L.mem bop ops_logical && isSimpleExp e1 && isSimpleExp e2-> 
      let bops = BL (L.filter (fun bop' -> bop <> bop') ops_logical) in
      vlog (P.sprintf "[%s]\n" (String.concat ", " (get_names bops)));
      bops


    |Set _ -> (
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

      vlog (P.sprintf "Using %d/%d avail vars in fun %s\n"
	      (L.length vs) (L.length vs') fd.svar.vname);
      
      let vs = VL vs in
      vlog (P.sprintf "[%s]\n" (String.concat ", " (get_names vs)));
      vs
    )

    |_ -> E.log "don't know how to modify instr %a\n" d_instr i; VL []
  )
  |_ -> E.log "don't know how to modify stmt %a\n" dn_stmt s; VL []


let tbf (ast:file) (mainQ:fundec) (ssids:sid_t list) 
    (tcs:testcase list) 
    (stmt_ht:(int,stmt*fundec) H.t)
    (no_bugfix:bool) 
    (no_break:bool)
    (no_parallel:bool) : unit=

  E.log "*** TBF ***\n";

  assert (L.length ssids > 0);

  (*iterate through top n ssids*)
  let ssids = take !top_n_ssids ssids in

  vlog (P.sprintf "Obtain info from %d ssids\n" (L.length ssids));
  let rs = L.map(fun sid -> 

    let s,f = H.find stmt_ht sid in 
    if !vdebug then E.log "Spy stmt %d in fun %s\n%a\n" sid f.svar.vname dn_stmt s;

    let l = spy_sid ast s f in 

    match l with
    |VL l' -> 
      let len = L.length l' in
      if len > 0 then write_file_bin (arr_s ast.fileName sid) (VA (A.of_list (l')));
      sid, len

    |BL l' -> 
      let len = L.length l' in
      if len > 0 then write_file_bin (arr_s ast.fileName sid) (BA (A.of_list (l'))); 
      sid, len
	
  ) ssids in 

  let rs = L.filter (fun (_,len) -> len > 0) rs in
  let ssids,lens = L.split rs in
  vlog (P.sprintf "Got info from %d ssids\n" (L.length ssids));

  if (L.length ssids) < 1 then(
    E.log "No ssids for transformation .. exiting\n";
    exit 0
  );

  (*call Python script to do transformation*)
  let combs = L.map2 (fun sid len -> 
    P.sprintf "(%d, %d)" sid len) ssids lens in
  
  let combs = String.concat "; " combs in 
  
  let kr_opts = [if no_parallel then "--no_parallel" else "";
		 if no_bugfix then  "--no_bugfix"  else "";
		 if no_break then "--no_break" else "";
		 if !vdebug then "--debug" else "";
		] in 
  let kr_opts = String.concat " " (L.filter (fun o -> o <> "") kr_opts) in 

  let cmd = P.sprintf "python klee_reader.py %s --do_tbf \"%s\" %s" 
    ast.fileName combs kr_opts in 

  exec_cmd cmd ;

  E.log "*** TBF .. done ***\n"



(********************** Prototype **********************)

let () = begin

  let filename = ref "" in
  let inputs   = ref "" in
  let outputs  = ref "" in 
  
  let no_global_vars = ref false in
  let no_parallel = ref false in 
  let no_bugfix = ref false in 
  let no_break = ref false in 
  let no_faultloc = ref "" in (*manually provide fault loc info*)

  let do_ssid = ref (-1) in  (*only do transformation on vs_idxs*)
  let xinfo = ref "" in  (*helpful info for debuggin*)
  let idxs = ref "" in 

  let only_faultloc = ref false in
  
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

    "--no_faultloc", Arg.Set_string no_faultloc, 
    " manually provide suspicious stmts for fault loc, e.g., --no_faultloc 1 3 7";

    "--no_parallel", Arg.Set no_parallel, 
    P.sprintf " don't use multiprocessing (default %b)" !no_parallel;


    "--only_faultloc", Arg.Set only_faultloc, 
    P.sprintf " only do faultloc (default %b)" !only_faultloc;
    
    "--do_ssid", Arg.Set_int do_ssid, 
    " stand alone prog to modify code wrt this statement id, e.g., --do_ssid 1 --xinfo z2_c5 --idxs \"3 7 8\"";
    "--xinfo", Arg.Set_string xinfo, " e.g., --xinfo z2_c5";
    "--idxs", Arg.Set_string idxs, " e.g., --idxs \"3 7 8\"";

    "--do_nssids", Arg.Set_int top_n_ssids,
    P.sprintf " consider this number of suspicious stmts (default %d)" !top_n_ssids;

    "--do_min_sscore", Arg.Set_float min_sscore,
    P.sprintf " consider suspicious stmts with at least this score (default %g)" !min_sscore

  ] in

  let usage = P.sprintf "%s\nusage: tf src inputs outputs [options]\n" version in

  let handleArg s =
    if !filename = "" then filename := s
    else if !inputs = "" then inputs := s
    else if !outputs = "" then outputs := s
    else raise (Arg.Bad "too many input args")
  in

  Arg.parse (Arg.align argDescr) handleArg usage;
  if !filename = "" or (not (Sys.file_exists !filename))then(E.log "%s" usage;exit 0);
  

  initCIL();

  Cil.lineDirectiveStyle:= None;
  (*Cprint.printLn:=false; (*don't print line # *)*)
  (*Cil.useLogicalOperators := true; (*does not break && || *)*)
  E.colorFlag := true;

  (*act as a stand alone program for transformation*)
  if !do_ssid > -1 then (
    let ssid   = !do_ssid in
    let xinfo  = !xinfo in 
    let idxs =  L.map int_of_string (str_split !idxs) in

    assert (ssid > 0);
    assert (L.length idxs >= 0 && L.for_all (fun idx -> idx >= 0) idxs);

    (*read in saved files*)
    let (ast:file),(mainQ:fundec),(tcs:testcase list) = 
      read_file_bin (ginfo_s !filename) in

    let arr:vb_a_t = read_file_bin (arr_s !filename ssid) in 
    
    (match arr with
    |VA a -> (
      let cvs = L.map (fun idx -> a.(idx)) idxs in
      transform ast mainQ tcs xinfo ssid (VL cvs)
      )
    |BA a -> (
      let cvs = L.map (fun idx -> a.(idx)) idxs in
      transform ast mainQ tcs xinfo ssid (BL cvs) 
    ));
      
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

  let tdir, filename, inputs, outputs = 
    initialize_files !filename !inputs !outputs in
  at_exit (fun () -> cleanup tdir);

  let tcs = get_tcs filename inputs outputs in
  let goods, bads = checkInit filename tcs in
  
  let ast = Frontc.parse filename () in 
  let stmt_ht:(sid_t,stmt*fundec) H.t = H.create 1024 in 
  let mainQ = preprocess ast stmt_ht in  (*modify ast, etc*)


  (*** fault localization ***)
  let ssids:sid_t list = 
    if !no_faultloc = "" then fault_loc ast goods bads stmt_ht 
    else L.map int_of_string (str_split !no_faultloc) 
  in 
  
  if !only_faultloc then exit 0;

  (*** transformation and bug fixing ***)

  (*write info to disk for parallelism use*)
  write_file_bin (ginfo_s ast.fileName) (ast,mainQ,tcs); 

  if not !no_global_vars then (
    iterGlobals ast (function 
    |GVar (vi,_,_) -> extra_vars := vi::!extra_vars 
    |_ -> ());
    
    vlog (P.sprintf "Consider %d gloval vars\n%s\n" 
	    (L.length !extra_vars) (String.concat ", " (get_names (VL !extra_vars))))
    
  );
  tbf ast mainQ ssids tcs stmt_ht !no_bugfix !no_break !no_parallel 
    


end




(*Questions:

1. how to make true/false in Cil  ,  is it just one/zero ?
2. how to add the directive  #include "klee/klee.h" ?
3. getting all variable at a particular location (including tmp vars in the functions at that loc)
5. Convert global to local



To fix bug involving expression, e.g., if(a<=b) instead of if(b<=a) ,  need to break if(a<=b) to 
t = a<=b ; if(t) ...
*)


(*
Fault Loc
Inputs: f.c, good_tcs, bad_tcs

(*create cov file*)
- add cov printfs info to file
- write file.cov.c 


(*get good/bad paths*)
- compile file.cov.c  to file.cov.c.exe

- create testscript_good 
- run file.cov.c with testscript_good 
- mv file.cov.c.path to file.cov.c.gpath


- create testscript_bad
- run file.cov.c with testscript_bad
- mv file.cov.c.path to file.cov.c.bpath


*)

(*
Input: f.c  
sanitize test:  
 -  assert f.c is compilable
 -  assert f.c.inputs exist
 -  assert f.c.outputs exist
 -  assert |f.c.outputs| = |f.c.inputs|

check if f.c passes all inputs:
  - Compile f.c to f.exe
  - run f.exe on f.c.inputs > f.c.outputs_real
  - diff f.c.outputs f.c.outputs_real 
  - if no diff,  return no bug, exit
  - good tcs: inputs and expected outputs where expected = real
  - bad tcs: inputs and expected outputs where expected # real

get good bad path
  - initialize f.c
  - create f.cov.c
  - compile f.cov.exe 
  - good_path:  ./f.cov.exe on good inputs 
  - bad_path:   ./f.cov.exe on bad inputs

fault localization
   - get suspicious statement by running tarantula on good and bad path

//bug fixing
transform 
   - f.c -> f.tf.0.c , f.tf.1.c  ...


run klee on transformed files



if stmt is s = x < y then
1. get compat bops, e.g.,  <= = >= ...
2. for each comb of bos
   1. main:  create uks ,  add constraints about uks 
   2. stmt:  s = combsvs + uks
   3. add uk's to decls and fun calls 
   4. ...


if stmt is s = __ then
1. find sfd , get vs in scope
2. for each combs of vs 
   1. main:  create uks ,  add constraints about uks 
   2. stmt:  s = combsvs + uks
   3. add uk's to decls and fun calls 
   4. ...

*)

