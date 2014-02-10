(*ocamlfind ocamlopt -package str,batteries,cil  cil_common.cmx -linkpkg -thread tf.ml*)

open Cil
(*open Cil_common*)
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
let combinations k list =
  let rec aux k acc emit = function
    | [] -> acc
    | h :: t ->
      if k = 1 then aux k (emit [h] acc) emit t else
        let new_emit x = emit (h :: x) in
        aux k (aux (k-1) acc new_emit t) emit t
  in
  let emit x acc = x :: acc in
  aux k [] emit list

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

(*check if s1 is a substring of s2*)
let in_str s1 s2 = 
  try ignore(Str.search_forward (Str.regexp_string s1) s2 0); true
  with Not_found -> false

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
  E.log "cmd '$ %s'\n" cmd ;
  match Unix.system cmd with
    |Unix.WEXITED(0) -> ()
    |_ -> E.s(E.error "cmd failed '%s'" cmd)

  
(* Specific options for this program *)

let uk0_min:int = -100000
let uk0_max:int =  100000
let uk_min :int = -1 
let uk_max :int =  1

let min_sscore:float = 0.5
let max_uks:int = 2 
let top_n_ssids:int = 10

let boolTyp:typ = intType

(*filename formats*)
let ginfo_s = P.sprintf "%s.info" (*f.c.info*)
let vs_a_s = P.sprintf "%s.s%d.arr" (*f.c.sid1.arr*)
let transform_s = P.sprintf "%s.s%d.%s.tf.c" (*f.c.s5.z3_c2.tf.c*)

(*commands*)
let gcc_cmd = P.sprintf "gcc %s -o %s >& /dev/null"

type inp_t = int list 
type outp_t = int 
type testcase = inp_t * outp_t
type sid_t = int
  
(******************* Helper Functions *******************)
let mk_vi ?(ftype=TVoid []) fname: varinfo = makeVarinfo true fname ftype

(*av = fname(args)*)
let mk_call ?(ftype=TVoid []) ?(av=None) fname args : instr = 
  let f = var(mk_vi ~ftype:ftype fname) in
  Call(av, Lval f, args, !currentLoc)

let exp_of_vi (vi:varinfo): exp = Lval (var vi)

let get_names:(varinfo list -> string list) = L.map (fun vi -> vi.vname)

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


(******************* Helper Visistors *******************)
(*Finds function containing stmt with id sid*)
class findFunVisitor (sid:int) (fd:fundec option ref)= object
  inherit nopCilVisitor

  val mutable c_fd = None

  method vfunc f = c_fd <- (Some f); DoChildren

  method vstmt s = 
    if s.sid = sid then (fd:= Some (forceOption c_fd); SkipChildren)
    else DoChildren

end

(*Find function containing stmt with id sid*)
let fd_of_sid (ast:file) (sid:int): fundec = 
  
  let fd = ref None in
  visitCilFileSameGlobals ((new findFunVisitor) sid fd) ast;
  let fd = forceOption !fd in

  E.log "Found sid %d in fun '%s'\n" sid fd.svar.vname ;
  fd


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

  E.log "read tcs from '%s' and '%s' for program '%s'\n" inputs outputs filename;

  let inputs = read_lines inputs in
  let outputs = read_lines outputs in 
  assert (L.length inputs = L.length outputs);

  let tcs = 
    L.fold_left2 (fun acc inp outp ->
      let inp = Str.split (Str.regexp "[ \t]+")  inp in

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

(******************* Initialize: Assigning id's to stmts *******************)
(*break conditional / loop guard to 
  if(complex_exp) to 
  int tmp = complex_exp; 
  if(tmp) 
*)

let can_break_exp (e:exp) : bool = 
    match e with
    |Lval _ -> false
    |_ -> true

class breakCondVisitor = object
  inherit nopCilVisitor
  val cur_fd = ref None
  method vfunc fd = cur_fd := (Some fd); DoChildren

  method vblock b = 
    let action (b: block) : block = 
      let change_stmt (s: stmt) : stmt list = 
	match s.skind with
	|If(e,b1,b2,loc) when can_break_exp e ->
	  let typ = typeOf e in
	  let temp:lval = var(makeTempVar (forceOption !cur_fd) typ) in
	  let i:instr = Set(temp,e,loc) in
	  let s1 = {s with skind = Instr [i]} in 
 
	  let new_skind:stmtkind = If(Lval temp,b1,b2,loc) in
	  let s2 = mkStmt new_skind in

	  E.log "breaking %a\n to\n %a\n%a\n" d_stmt s d_stmt s1 d_stmt s2;
	  
	  [s1;s2]

	(*|While _ may be not really necessary*)

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




(* List of stmts that can be modified *)
let can_modify:stmtkind->bool = function 
  |Instr [Set(_)] -> true
  |_ -> false

(* Walks over AST and builds a hashtable that maps ints to stmts *)
class numVisitor ht = object
  inherit nopCilVisitor
    
  val mutable mctr = 1
  method get_mctr () = mctr

  method vblock b = 
    let action (b: block) : block= 
      let change_sid (s: stmt) : unit = 
	if can_modify s.skind then (
	  H.add ht mctr s;
	  s.sid <- mctr;
	  mctr <- succ mctr
	)
	else s.sid <- 0;  (*Anything not considered has sid 0 *)
      in 
      L.iter change_sid b.bstmts; 
      b
    in 
    ChangeDoChildrenPost(b, action)


end


let initialize_ast (ast:file) (sid_stmt_ht:(int,stmt) H.t):fundec= 
  E.log "*** Initializing (assigning id's to stmts)***\n";
 
  visitCilFileSameGlobals (new everyVisitor) ast;
  visitCilFileSameGlobals (new breakCondVisitor) ast;

  let nv = (new numVisitor) sid_stmt_ht in 
  visitCilFileSameGlobals (nv:> cilVisitor) ast;
  assert (pred (nv#get_mctr()) = H.length sid_stmt_ht);

  (*find mainQ*)
  let mainQ_fd = ref None in
  iterGlobals ast (function
  |GFun(f,_) when f.svar.vname = "mainQ" -> mainQ_fd := Some f
  |_ -> ()
  );

  let mainQ_fd = 
    match !mainQ_fd with
    |Some f -> f
    |None -> E.s (E.error "'%s' does not have a mainQ function\n" ast.fileName)
  in


  E.log "*** Initializing .. done ***\n";
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
  E.log "Note: all temp files are created in dir '%s'\n" tdir 
    

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
  
  E.log "%s" content;
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
  if nbads = 0 then (E.log "All tests passed .. no bug found\n"; exit 0)
  else (E.log "%d tests failed\n" nbads);
  
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
  let stderr = Lval (var(stderr_va)) in
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

  E.log "*** Creating coverage info ***\n";

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
  
  write_src filename_cov  ast;

  E.log "*** Creating coverage info .. done ***\n"


(******** Tarantula Fault Loc ********)
(* Analyze execution path *)    
let analyze_path (filename:string): int * (int,int) H.t= 

  E.log "** Analyze execution path '%s'\n" filename;
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
  let rs = L.filter (fun (_,score) -> score >= min_sscore) rs in 
  rs


let fault_loc (ast:file) (goods:testcase list) (bads:testcase list): sscore list = 
  E.log "*** Fault Localization ***\n";

  assert (L.length goods > 0) ;
  assert (L.length bads  > 0) ;


  let tdir = mk_tmp_dir 
    ~use_time:false ~temp_dir:(Filename.dirname ast.fileName) "fautloc" "" in

  E.log "faultloc temp dir '%s'\n" tdir;

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

  E.log "*** Fault Localization .. done ***\n";
  sscores


(******************* Transforming File *******************)
(*declare and set constraints on uk:
  int uk;
  klee_make_symbol(&uk,sizeof(uk),"uk");
  mk_klee_assume(min<=uk<=max);
*)

let mk_uk (main_fd:fundec) (uid:int) : (varinfo*lval) * (instr list) = 
  let vname = ("uk_" ^ string_of_int uid) in 
  
  (*declare uks*)
  let vi:varinfo = makeLocalVar main_fd  vname intType in 
  let lv:lval = var vi in 
  
  (*klee_make_symbolic(&uk,sizeof(uk),"uk") *)
  let mk_sym_instr:instr = mk_call "klee_make_symbolic" 
    [mkAddrOf(lv); SizeOfE(Lval lv); Const (CStr vname)] in
  
  (*klee_assume(min <= uk) , klee_assume(uk <= max) *)
  let min_,max_ = if uid = 0 then uk0_min,uk0_max else uk_min,uk_max in
  let klee_assert_lb:instr = mk_call "klee_assume" 
    [BinOp(Le,integer min_,Lval lv, boolTyp)] in 
  let klee_assert_ub:instr = mk_call "klee_assume" 
    [BinOp(Le,Lval lv, integer max_, boolTyp)] in 

  (vi,lv), [mk_sym_instr; klee_assert_lb; klee_assert_ub]

(*make calls to mainQ on test inp/oupt:
  mainQ_typ temp;
  temp = mainQ(inp0,inp1,..);
  temp == outp
*)
let mk_mainQ_call (main_fd:fundec) (mainQ_typ:typ) (tc:testcase) = 
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

(*creates reachability "goal" statement 
  if(e_1,..,e_n){
  printf("GOAL: uk0 %d, uk1 %d ..\n",uk0,uk1);
  klee_assert(0);
  }
*)

let mk_goal (exps:exp list) (uks_exps:exp list):stmtkind = 

  let and_exps (exps:exp list): exp = 
    let e0 = L.hd exps in 
    if L.length exps = 1 then e0
    else(
      let typ = typeOf e0 in
      L.fold_left (fun e e' -> BinOp(LAnd,e,e',typ)) e0 (L.tl exps)
    )
    in
  
  (*printf("GOAL: uk0 %d uk1 %d .. \n",uk0,uk1,..); *)
  let str = L.map (
    function
    |Lval (Var vi,_) -> vi.vname ^ " %d"
    |_ -> failwith "not poss: uk must be Lval ..") uks_exps
  in
  let str = "GOAL: " ^ (String.concat ", " str) ^ "\n" in 
  let print_goal:instr = mk_call "printf" ([Const(CStr(str))]@uks_exps) in 
  
  (*klee_assert(0);*)
  let klee_assert_zero:instr = mk_call "klee_assert" [zero] in 
  
  
  If(and_exps exps, 
     mkBlock [mkStmt (Instr([print_goal; klee_assert_zero]))], 
     mkBlock [], !currentLoc) 


(*Instrument main function*)
let mk_main (main_fd:fundec) (mainQ_fd:fundec) (n_uks:int) (tcs:testcase list)
    : (varinfo list * stmt list) =
  let uks, instrs1 = L.split(L.map (mk_uk main_fd) (range n_uks)) in 
  let (uks_vi:varinfo list), (uks_lv: lval list) = L.split uks in 
  
  (*declare uks and setup constraints*)
  let uks_exps = L.map (fun lv -> Lval lv) uks_lv in 

  (*make mainQ calls and expressions based on testcases*)
  let mainQ_typ:typ = match mainQ_fd.svar.vtype with 
    |TFun(t,_,_,_) -> t
    |_ -> E.s(E.error "%s is not fun typ %a\n" 
		mainQ_fd.svar.vname d_type mainQ_fd.svar.vtype)
  in

  (*make big if goal *)
  let instrs2,exps = L.split (L.map (fun tc -> 
    mk_mainQ_call main_fd mainQ_typ tc) tcs) in
    

  let if_skind:stmtkind = mk_goal exps uks_exps in

  let instrs_skind:stmtkind = Instr(L.flatten(instrs1)@instrs2) in

  uks_vi, [mkStmt instrs_skind; mkStmt if_skind]
   

class mainVisitor  (mainQ_fd:fundec) (n_uks:int) (tcs:testcase list) (uks:varinfo list ref)= object
  inherit nopCilVisitor
  method vfunc fd =
    let action(fd:fundec) : fundec =
      if fd.svar.vname = "main" then (
	let uks',stmts = mk_main fd mainQ_fd n_uks tcs in
	(*fd.sbody.bstmts <- stmts @ fd.sbody.bstmts;*)
	fd.sbody.bstmts <- stmts;
	uks := uks' 
      );
      fd
    in
    ChangeDoChildrenPost(fd,action)
end


let mk_param_instr (a_i:instr) (vs:varinfo list) (uks:varinfo list): instr = 
  (*create a new assignment stmt x = v0 + uk1*v1 + uk2*v2 from given stmt x = .. *)
  assert (L.length vs + 1  = L.length uks);

  let mk_add_exp (a:exp) (x:exp) (y:exp) = 
    BinOp(PlusA, a, BinOp(Mult, x, y, intType), intType) in


  match a_i with 
  |Set(v,_,l)->
    let vs = L.map exp_of_vi vs in 
    let uks = L.map exp_of_vi uks in
    let uk0,uks' = (L.hd uks), (L.tl uks) in 
    let r_exp = L.fold_left2 mk_add_exp uk0 uks' vs in
    Set(v,r_exp,l)
  |_ -> E.s(E.error "incorrect assignment instruction %a" d_instr a_i)


class suspStmtVisitor (ssid:int) (vs:varinfo list) (uks:varinfo list) (modified:bool ref) = object(self)
  inherit nopCilVisitor
  method vstmt (s:stmt) = 
    let action (s: stmt) :stmt = 
      (match s.skind with 
      |Instr instrs when s.sid = ssid & L.length instrs = 1 ->
	let new_i = mk_param_instr (L.hd instrs) vs uks in
	s.skind <- Instr [new_i];
	modified := true
      |_ -> ()
      );
      s
    in
    ChangeDoChildrenPost(s, action)
end      


(*add uk's to function args, e.g., fun(int x, int uk0, int uk1);*)
class funInstrVisitor (uks:varinfo list) (funs_ht:(string, unit) H.t) = object(self)

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
class instrCallVisitor (uks:varinfo list) (funs_ht:(string,unit) H.t)= object(self)
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

 
type file_t =   FT of file         | FTS of string
type testcase_list_t =    TS of testcase list    | TSS of string

(*transform main/mainQ functions in ast wrt to given variables cvs*)

let transform_cvs (ast:file) (mainQ:fundec) 
    (tcs:testcase list) (xinfo:string) (ssid:sid_t) (cvs:varinfo list)  = 
    
  E.log "** comb %s. |vs|=%d [%s]\n" xinfo (L.length cvs) 
    (String.concat ", " (get_names cvs));

  let n_uks = succ (L.length cvs) in
  let (uks:varinfo list ref) = ref [] in
  
  (*instr main*)
  visitCilFileSameGlobals ((new mainVisitor) mainQ n_uks tcs uks) ast;
  let uks = !uks in
  assert (L.length uks = n_uks) ;


  (*modify suspStmt: stay with this order, mod sstmt first before doing others*)
  let modified = ref false in
  visitCilFileSameGlobals ((new suspStmtVisitor) ssid cvs uks modified) ast;
  assert (!modified);

  (*add uk's to fun decls and fun calls*)
  let funs_ht = H.create 1024 in
  visitCilFileSameGlobals ((new funInstrVisitor) uks funs_ht) ast;
  visitCilFileSameGlobals ((new instrCallVisitor) uks funs_ht) ast;

  (*add include "klee/klee.h" to file*)
  ast.globals <- (GText "#include \"klee/klee.h\"") :: ast.globals;
  
  write_src (transform_s ast.fileName ssid xinfo) ast
        
(*transform main/mainQ functions in ast wrt to given suspicious statement*)
let transform_sid (ast:file) (mainQ:fundec) (tcs:testcase list) (ssid:sid_t) = 

  E.log "** Transform file '%s' wrt sid '%d' with %d tcs\n"
    ast.fileName ssid (L.length tcs);
  (*E.log "%a\n" d_stmt (H.find sid_stmt_ht ssid);*)

  
  (*find which function contains suspicious stmt id*)
  let s_fd = fd_of_sid ast ssid in 

  (*obtain usuable variables from s_fd*)
  let vs' = s_fd.sformals@s_fd.slocals in 

  let vi_pred vi = 
    vi.vtype = intType && 
    not (in_str "__cil_tmp" vi.vname) &&
    not (in_str "tmp___" vi.vname)
  in

  let vs = L.filter vi_pred vs' in

  E.log "Using %d/%d avail vars in fun %s\n" 
    (L.length vs) (L.length vs') s_fd.svar.vname;
  E.log "[%s]\n" (String.concat ", " (get_names vs));

  (*let n_uks = L.length vs in*)
  let n_uks = max_uks in
  let cvss:varinfo list list = 
    L.flatten(L.map(fun siz -> combinations siz vs) (range (n_uks + 1))) in 
		
  let cvss = [[]]@cvss in
  E.log "total combs %d\n" (L.length cvss);
  
  L.iter2 (fun cid cvs -> 
    transform_cvs
      (copy_obj ast) mainQ tcs
      (P.sprintf "z%d_c%d" (L.length cvs) cid) ssid cvs)
    (range (L.length cvss)) cvss 


let transform (ast:file) (mainQ:fundec) (ssids:sid_t list) (tcs:testcase list) (do_parallel:bool) = 
  assert (L.length ssids > 0);

  E.log "*** Transform ***\n";  
  (*iterate through top n ssids*)
  let ssids = take top_n_ssids ssids in 
    E.log "Apply transformation to %d ssids (parallel: %b) \n" 
      (L.length ssids) do_parallel;
  
  if do_parallel then (
    let kr_option = if do_parallel then "--do_parallel" else "" in
    let ssids' = String.concat " " (L.map string_of_int ssids) in
    let cmd = P.sprintf "python klee_reader.py %s --do_instrument \"%s\" %s"
      ast.fileName ssids' kr_option in
    exec_cmd cmd
  )
  else(
    L.iter (fun (ssid:sid_t) -> transform_sid ast mainQ tcs ssid) ssids
  );

  E.log "*** Transform .. done ***\n"  


(****** WORKING CODE **********)
let spy_sid (ast:file) (ssid:sid_t): varinfo array =

  E.log "** Obtain vs info in scope of sid %d in file '%s'\n"
    ssid ast.fileName ;
  (*E.log "%a\n" d_stmt (H.find sid_stmt_ht ssid);*)

  (*find which function contains suspicious stmt id*)
  let sfd = fd_of_sid ast ssid in

  (*obtain usuable variables from sfd*)
  let vs' = sfd.sformals@sfd.slocals in

  let vi_pred vi =
    vi.vtype = intType &&
    not (in_str "__cil_tmp" vi.vname) &&
    not (in_str "tmp___" vi.vname)
  in
  let vs = L.filter vi_pred vs' in

  E.log "Using %d/%d avail vars in fun %s\n"
    (L.length vs) (L.length vs') sfd.svar.vname;
  E.log "[%s]\n" (String.concat ", " (get_names vs));

  Array.of_list(vs)  


let tbf (ast:file) (mainQ:fundec) (ssids:sid_t list) (tcs:testcase list) (do_parallel:bool) =
  assert (L.length ssids > 0);

  E.log "*** Transform ***\n";

  (*iterate through top n ssids*)
  let ssids = take top_n_ssids ssids in

  E.log "Obtain vs info from %d ssids\n"  (L.length ssids);
  let vs_arrs = L.map(fun sid -> spy_sid ast sid) ssids in 

  (*write info to disk for parallelism use*)
  L.iter2(fun sid vs_a -> write_file_bin (vs_a_s ast.fileName sid) vs_a) ssids vs_arrs ;
  
  (*call Python script to do the transformation in parallel*)

  let combs = L.map2 (fun sid vs_a ->    (*"(sid,length arr); () .."*)
    P.sprintf "(%d, %d)" sid (A.length vs_a)) ssids vs_arrs in
  let combs = String.concat "; " combs in 
  let kr_option = if do_parallel then "--do_parallel" else "" in 
  let cmd = P.sprintf "python klee_reader.py %s --do_tbf \"%s\" %s" 
    ast.fileName combs kr_option in 
  exec_cmd cmd ;

  E.log "*** Transform .. done ***\n"

(* (\*WORKING CODE*\) *)


let bug_fix (filename:string) (do_parallel:bool)= 
  E.log "*** Bug Fix ***\n";  

  (*run klee on transformed files
    $time python klee_reader.py tests/p.c --do_parallel
  *)
  E.log "Run Klee on transformed files from '%s' (parallel: %b)\n" 
    filename do_parallel;
    
  let kr_option = if do_parallel then "--do_parallel" else "" in
  let cmd = P.sprintf "python klee_reader.py %s %s" filename kr_option in 
  exec_cmd cmd ;
  
  E.log "*** Bug Fix .. done ***\n"



(********************** Prototype **********************)

let () = begin

  let filename = ref "" in
  let inputs   = ref "" in
  let outputs  = ref "" in 

  let do_faultloc = ref false in
  let do_transform = ref false in
  let do_bugfix = ref false in

  let do_instrument_ssid = ref (-1) in  (*only do transformation on ssids*)


  let do_ssid = ref (-1) in  (*only do transformation on vs_idxs*)
  let xinfo = ref "" in  (*helpful info for debuggin*)
  let idxs = ref "" in 

  let do_parallel = ref false in 

  let argDescr = [
    "--do_faultloc", Arg.Set do_faultloc, "do fault localization";
    "--do_transform", Arg.Set do_transform, "do transform";
    "--do_bugfix", Arg.Set do_bugfix, "do bugfix";
    "--do_parallel", Arg.Set do_parallel, "do parallel";

    "--do_instrument_ssid", Arg.Set_int do_instrument_ssid, "S instrument ssid";
    "--do_ssid", Arg.Set_int do_ssid, "X ssid";
    "--xinfo", Arg.Set_string xinfo, "S xinfo";
    "--idxs", Arg.Set_string idxs, "S idxs";
  ] in

  let usage = "usage: tf [src inputs outputs]\n" in

  let handleArg s =
    if !filename = "" then filename := s
    else if !inputs = "" then inputs := s
    else if !outputs = "" then outputs := s
    else raise (Arg.Bad "too many input args")
  in

  Arg.parse (Arg.align argDescr) handleArg usage;

  initCIL();

  (*E.g., ./tf /tmp/cece_1391897485_3bed37/p.c --do_instrument_ssid 1 *)
  if !do_instrument_ssid > -1 then (
    let ssid = !do_instrument_ssid in 
    assert (ssid > 0);

    (*read in saved info*)
    let (ast:file),(mainQ:fundec),(tcs:testcase list) = 
      read_file_bin (ginfo_s !filename) in

    transform_sid ast mainQ tcs ssid ;
    exit 0
  );


  if !do_ssid > -1 then (
    let ssid   = !do_ssid in
    let xinfo  = !xinfo in 
    let idxs =  L.map int_of_string (Str.split (Str.regexp "[ \t]+")  !idxs) in

    assert (ssid > 0);
    assert (L.length idxs >= 0 && L.for_all (fun idx -> idx >= 0) idxs);

    (*read in saved files*)
    let (ast:file),(mainQ:fundec),(tcs:testcase list) = 
      read_file_bin (ginfo_s !filename) in

    let vs_a:varinfo array = read_file_bin (vs_a_s !filename ssid) in 
      
    let cvs = L.map (fun idx -> vs_a.(idx)) idxs in
    transform_cvs ast mainQ tcs xinfo ssid cvs ;

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
  let sid_stmt_ht:(int,stmt) H.t = H.create 1024 in 
  let mainQ = initialize_ast ast sid_stmt_ht in  (*modify ast, etc*)

  (*write info to disk for parallelism use*)
  write_file_bin (ginfo_s ast.fileName) (ast,mainQ,tcs); 

  (*** fault localization ***)
  let sscores:sscore list = 
    if !do_faultloc then fault_loc ast goods bads else [(1,1.)] 
  in

  E.log "Suspicious scores for %d stmt\n" (L.length sscores);
  L.iter (fun (sid,score) -> 
    E.log "sid %d -> score %g\n%a\n" sid score d_stmt (H.find sid_stmt_ht sid)
  ) sscores;

  let ssids:sid_t list = L.map fst sscores in   

  if !do_transform then (
    tbf ast mainQ ssids tcs !do_parallel
    (*transform ast mainQ ssids tcs !do_parallel*)
  );

  if !do_bugfix then (bug_fix ast.fileName !do_parallel);

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


*)

