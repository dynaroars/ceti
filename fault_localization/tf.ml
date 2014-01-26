(*ocamlfind ocamlopt -I /usr/local/lib/ocaml/3.11.2/cil/ -package str,batteries cil.cmxa  cil_common.cmx -linkpkg -thread tf.ml*)

open Cil
open Cil_common
module E = Errormsg
module L = List

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
      
let rec range ?(a=0) b = if a >= b then [] else a::range ~a:(succ a) b 
let copy_obj (x : 'a) = let str = Marshal.to_string x [] in (Marshal.from_string str 0 : 'a)

(* Specific options for this file *)

let uk_min = -1 
let uk_max = 1

let boolTyp:typ = intType

type inp_t = int list 
type outp_t = int 
type tc_t = inp_t * outp_t
type testsuite = tc_t list
  
(******************* Helper Functions *******************)
let mk_vi ?(ftype=TVoid []) fname: varinfo = makeVarinfo true fname ftype

(*av = fname(args)*)
let mk_call ?(ftype=TVoid []) ?(av=None) fname args : instr = 
  let f = var(mk_vi ~ftype:ftype fname) in
  Call(av, Lval f, args, !currentLoc)


(*gcc filename.c;  return "filename.exe" if success else None*)
let compile (src:string): string option = 
  let gcc = "gcc" in 
  let ldflags = "" in 
  let exe = src ^ ".exe" in 
  (try Unix.unlink exe with _ -> () ) ; 

  let cmd = Printf.sprintf "%s %s -o %s %s >& /dev/null" gcc src exe ldflags in
    
  E.log "cmd '%s'\n" cmd ;

  match Unix.system cmd with 
  |Unix.WEXITED(0) -> Some exe
  |_ -> (E.log "cannot compile '%s'\n" src; None)


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


(*preprend a string to a file*)
let preprend (filename:string) (text:string) = 
()
  
(******************* Helper Visistors *******************)
class printStmtVisitor (sid:int option) = object
  inherit nopCilVisitor
  method vstmt s = 
    (match sid with
    |None -> E.log "sid %d:\n%a\n" s.sid d_stmt s
    |Some sid -> if s.sid = sid then E.log "sid %d:\n%a\n" sid d_stmt s);
    DoChildren (*or is it DoChildren ?*)
end

class spyFunVisitor (fname:string) (fd:fundec option ref)= object(self)
  inherit nopCilVisitor
  method vfunc f = 
    if f.svar.vname = fname then (
      fd := Some f; 
    );
    SkipChildren
end


(*********************** Reading Testcases ***********************)

let string_of_tc (tc:int list * int) : string = 
  let inp,outp = tc in 
  let inp = String.concat "; " (L.map string_of_int inp) in
  let outp = string_of_int outp in 
  "([" ^ inp ^ "]" ^ ", " ^ outp ^ "]"

let string_of_tcs (tcs:testsuite) :string = 
  let tcs = L.map string_of_tc tcs in 
  let tcs = String.concat "; " tcs in
  "["^ tcs ^ "]"
  

let get_tcs (filename:string) : (int list * int) list = 

  let inputs = filename ^ ".inputs" in
  let outputs =  filename ^ ".outputs" in
  assert (Sys.file_exists inputs);
  assert (Sys.file_exists outputs);

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
  E.log "%s\n" (string_of_tcs tcs);

  tcs

(******************* Initialize: Assigning id's to stmts *******************)

(*Makes every instruction into its own statement*)
class everyVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    let action (b: block) : block = 
      let change_stmt (s: stmt) : stmt list = 
	match s.skind with
	|Instr(h::t) -> 
	  ({s with skind = Instr([h])})::L.map mkStmtOneInstr t
	|_ -> [s]
      in
      let stmts = L.flatten (L.map change_stmt b.bstmts) in
      {b with bstmts = stmts}
    in
    ChangeDoChildrenPost(b, action)
end



let ht = Hashtbl.create 1024
let ctr = ref 1
let get_next_ct ct = let ct' = !ct in incr ct;  ct'

(* List of stmts that can be modified *)
let can_modify (sk:stmtkind) : bool= 
  match sk with 
  |Instr [Set(_)] -> true
  |_ -> false

(* Walks over AST and builds a hashtable that maps ints to stmts *)
class numVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    let action (b: block) : block= 
      let change_sid (s: stmt) : unit = 
	if can_modify s.skind then (
	  let ct = get_next_ct ctr in
	  Hashtbl.add ht ct s.skind;
	  s.sid <- ct
	)
	else s.sid <- 0;  (*Anything not considered has sid 0 *)
      in 
      L.iter change_sid b.bstmts; 
      b
    in 
    ChangeDoChildrenPost(b, action)
end


let initialize (ast:file) (filename:string) = 
  E.log "*** Initializing (assigning id's to stmts)***\n";

  visitCilFileSameGlobals (new everyVisitor) ast;
  visitCilFileSameGlobals (new numVisitor) ast;

  write_file_bin (filename ^ ".ht")  (!ctr-1, ht);
  write_file_bin (filename ^ ".ast") ast;
  write_src (filename ^ ".ast.c") ast;

  E.log "*** Initializing .. done ***\n"



(********************** Initial Check **********************)

let mk_testscript (testscript:string) (tcs:(int list * int) list) =
  (*"($1 1071 1029 | diff ref/output.1071.1029 - && (echo "1071 1029" >> $2)) &"*)

  let content = L.map (fun (inp,_) ->
    let inp = String.concat " " (L.map string_of_int inp) in

    (*if use & then things are done in parallel but order mesed up*)
    Printf.sprintf "($1 %s >> $2) ;" inp 
  ) tcs in
  let content = String.concat "\n" content in
  let content = Printf.sprintf "#!/bin/bash\nulimit -t 1\n%s\nwait\nexit 0\n" content in
  
  E.log "%s" content;
  write_file_str testscript content
    

let run_testscript (testscript:string) (prog:string) (prog_output:string) =
  (* "sh script.sh prog prog_output" *)

  (try Unix.unlink prog_output with _ -> () ) ; 

  let prog = Printf.sprintf "./%s" prog in
  let cmd = Printf.sprintf "sh %s %s %s &> /dev/null" testscript prog prog_output in
  E.log "cmd '%s'\n" cmd ; 

  match Unix.system cmd with
    |Unix.WEXITED(0) -> ()
    |_ -> E.s(E.error "'%s' failed" cmd)

let mk_run_testscript testscript prog prog_output tcs = 
  if Sys.file_exists testscript then E.log "script '%s' exists .. skipped\n" testscript
  else mk_testscript testscript tcs;

  run_testscript testscript prog prog_output
    
    
  


(*partition tcs into 2 sets: good / bad*)
let compare_outputs (prog_outputs:string) (tcs:testsuite) : testsuite * testsuite = 
  let prog_outputs = read_lines prog_outputs in 
  assert (L.length prog_outputs == L.length tcs) ;

  let goods, bads = L.partition (fun ((_,e_outp),p_outp) -> 
    (try e_outp = int_of_string p_outp 
     with _ -> false)
  ) (L.combine tcs prog_outputs) in

  let goods,_ = L.split goods in
  let bads,_ =  L.split bads in

  goods, bads


let init_check (filename:string) (tcs:(int list * int) list)  = 
  (*do some prelim checking and obtain good/test testcases*)
  E.log "*** Init Check ***\n";

  (*compile and run program on tcs*)
  let prog:string option = compile filename in
  let prog:string = forceOption prog in

  let testscript =  filename ^ ".sh" in
  let prog_output:string = filename ^ ".routputs" in
  mk_run_testscript testscript prog prog_output tcs;

  (*check if prog passes all inputs:
    If yes then exit. If no then there's bug to fix*)
  let goods,bads = compare_outputs prog_output tcs in 
  let nbads = L.length bads in
  if nbads = 0 then (E.log "All tests passed .. nothing else to do\n"; exit 1)
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

let create_fprintf_stmt (sid: int) :stmt = 
  let str = Printf.sprintf "%d\n" sid in
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


let coverage (ast:file) (filename:string) (filename_cov:string) = 

  E.log "*** Creating coverage info ***\n";

  (*add printf stmts*)
  visitCilFileSameGlobals (new coverageVisitor) ast;

  (*add to global
    _coverage_fout = fopen("file.c.path", "ab");
  *)
  let new_global = GVarDecl(stderr_va, !currentLoc) in
  ast.globals <- new_global :: ast.globals;

  let lhs = var(stderr_va) in
  let arg1 = Const(CStr(filename ^ ".path" )) in
  let arg2 = Const(CStr("ab")) in
  let instr = mk_call ~av:(Some lhs) "fopen" [arg1; arg2] in
  let new_s = Cil.mkStmt (Instr[instr]) in 

  let fd = getGlobInit ast in
  fd.sbody.bstmts <- new_s :: fd.sbody.bstmts;
  
  write_src filename_cov  ast;

  E.log "*** Creating coverage info .. done ***\n"


(******** Tarantula Fault Loc ********)
(* Analyze execution path *)    
let analyze_path (file_path:string): int * (int,int) Hashtbl.t= 

  E.log "Analyze '%s'\n" file_path;
  let tc_ctr = ref 0 in
  let ht_stat = Hashtbl.create 1024 in 
  let mem = Hashtbl.create 1024 in 
  let lines = read_lines file_path in 
  L.iter(fun line -> 
    let sid = int_of_string line in 
    if sid = 0 then (
      incr tc_ctr;
      Hashtbl.clear mem;
    )
    else (
      let sid_tc = (sid, !tc_ctr) in
      if not (Hashtbl.mem mem sid_tc) then (
	Hashtbl.add mem sid_tc ();
	
	let n_occurs = 
	  if not (Hashtbl.mem ht_stat sid) then 1
	  else succ (Hashtbl.find ht_stat sid)

	in Hashtbl.replace ht_stat sid n_occurs
      )
    )
  )lines;
  !tc_ctr, ht_stat


type sscore = int * float (* sid, suspicious score *)

let tarantula (n_g:int) (ht_g:(int,int) Hashtbl.t) (n_b:int) (ht_b:(int,int) Hashtbl.t) : sscore list=
  assert(n_g <> 0);
  assert(n_b <> 0);

  let ht_sids = Hashtbl.create 1024 in 
  let set_sids ht =
    Hashtbl.iter (fun sid _ ->
      if not (Hashtbl.mem ht_sids sid) then Hashtbl.add ht_sids sid ()
    ) ht;
  in
  set_sids ht_g ;
  set_sids ht_b ;

  let n_g' = float_of_int(n_g) in
  let n_b' = float_of_int(n_b) in

  let rs = Hashtbl.fold (fun sid _ rs ->
    let get_n_occur sid (ht: (int,int) Hashtbl.t) : float=
      if Hashtbl.mem ht sid then float_of_int(Hashtbl.find ht sid) else 0. 
    in

    let freq_g = (get_n_occur sid ht_g) /. n_g' in
    let freq_b = (get_n_occur sid ht_b) /. n_b' in
    let score = freq_b /. (freq_g +. freq_b)  in
    (sid,score)::rs

  ) ht_sids [] in 

  let rs = L.sort (fun (_,score1) (_,score2) -> compare score2 score1) rs in

  E.log "Tarantula stmt suspicious scores\n";
  L.iter(fun (sid,score) -> E.log "%d -> %g\n" sid score) rs;
  rs



let fault_loc (filename:string) (ast:file) (goods:testsuite) (bads:testsuite): sscore list = 
  E.log "*** Fault Localization ***\n";

  assert (L.length goods > 0) ;
  assert (L.length bads > 0) ;

  (*create cov file*)
  let ast_cov = copy_obj ast in
  let filename_cov = filename ^ ".cov.c"  in
  coverage ast_cov filename filename_cov;

  (*compile cov file*)
  let prog:string option = compile filename_cov in
  let prog:string = forceOption prog in
  
  (*run prog to obtain good/bad paths*)
  let path_generic = filename ^ ".path" in
  let path_g = filename ^ ".gpath" in
  let path_b = filename ^ ".bpath" in

  (*good path*)
  mk_run_testscript (filename ^ ".g.sh") prog 
    (filename ^ ".outputs_g_dontcare") goods;
  Unix.rename path_generic path_g;
  
  (*bad path*)
  mk_run_testscript (filename ^ ".b.sh") prog 
    (filename ^ ".outputs_bad_dontcare") bads;
  Unix.rename path_generic path_b;

  let n_g, ht_g = analyze_path path_g in
  let n_b, ht_b = analyze_path path_b in
  let sscores = tarantula n_g ht_g n_b ht_b in

  
  (*debug: print out sid and corresponding statement*)
  let filename_ast = filename ^ ".ast" in
  assert (Sys.file_exists filename_ast);
  let ast = read_file filename_ast in
  
  L.iter(fun (sid,score) ->
    E.log "score %g\n" score;
    visitCilFileSameGlobals (new printStmtVisitor (Some sid)) ast
  ) sscores;
  
  E.log "*** Fault Localization .. done ***\n";

  sscores

(******************* Transforming File *******************)


let mk_uks_main (fd:fundec) (n_uks:int) (myQ_typ:typ) (tcs:testsuite) : (varinfo list * stmt list) =
  (*
    declare uks, setup constraints
    insert uk to myQ calls
    create stmt if(e,l,..) from tcs s.t e is satisfied and l is reached
    only when tcs are passed
    also returns list of uks
  *)
  
  let mk_uk (uid:int) : (varinfo*lval) * (instr list) = 
    let vname = ("uk_" ^ string_of_int uid) in 

    (*declare uks*)
    let vi:varinfo = makeLocalVar fd  vname intType in 
    let lv:lval = var vi in 

    (* make klee_make_symbolic(&uk,sizeof(uk),"uk") *)
    let addrof_uk = mkAddrOf(lv) in 
    let sizeof_uk = SizeOfE(Lval lv) in 
    let const_str:exp = Const (CStr vname) in 
    let mk_sym_instr:instr = 
      mk_call "klee_make_symbolic" [addrof_uk; sizeof_uk; const_str] in

    
    (* make klee_assume(min <= uk) , klee_assume(uk <= max) for uk1 ...n*)
    let instrs = if uid = 0 then
	[mk_sym_instr]
      else (
	let e_lb = BinOp(Le,integer uk_min,Lval lv, boolTyp) in
	let e_ub = BinOp(Le,Lval lv, integer uk_max, boolTyp) in
	
	let klee_assert_lb:instr = mk_call "klee_assume" [e_lb] in 
	let klee_assert_ub:instr = mk_call "klee_assume" [e_ub] in 
	[mk_sym_instr; klee_assert_lb; klee_assert_ub]
      )
    in
    (vi,lv), instrs


  in

  let uks, instrs = L.split(L.map mk_uk (range n_uks)) in 
  let uks_vi,uks_lv = L.split uks in 

  let mk_Q_call tc = 
    let inps,outp = tc in

    (* mk  tmp = myQ(inp, uks) *)
    let v:lval = var(makeTempVar fd myQ_typ) in 
    let inp_args = (L.map integer inps)@(L.map (fun lv -> Lval lv) uks_lv) in 
    let i:instr = mk_call ~ftype:myQ_typ ~av:(Some v) "myQ" inp_args in
    
    (*mk tmp == outp*)
    let e:exp = BinOp(Eq,Lval v,integer outp, boolTyp) in 
    e, i
  in
  
  let exps,myQ_calls_instrs = L.split (L.map mk_Q_call tcs) in
  
  (*mk if(e,l,...)*)
  let if_skind:stmtkind = 
    let and_exps (exps:exp list): exp = 
      let e0 = L.hd exps in 
      if L.length exps = 1 then e0
      else(
	let typ = typeOf e0 in
	L.fold_left (fun e e' -> BinOp(LAnd,e,e',typ)) e0 (L.tl exps)
      )
    in

    let klee_assert_call:instr = mk_call "klee_assert" [zero] in 

    If(and_exps exps, 
       mkBlock [mkStmt (Instr([klee_assert_call]))], 
       mkBlock [], !currentLoc) 
  in 

  let instrs_skind:stmtkind = Instr(L.flatten(instrs)@myQ_calls_instrs) in

  uks_vi, [mkStmt instrs_skind; mkStmt if_skind]
   

class mainVisitor (n_uks:int) (myQ_typ:typ) (tcs:testsuite) (uks:varinfo list ref)= object
  inherit nopCilVisitor
  method vfunc fd =
    let action(fd:fundec) : fundec =
      if fd.svar.vname = "main" then (
	let uks',stmts = mk_uks_main fd n_uks myQ_typ tcs in
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
  let mk_exp (x:varinfo):exp = Lval (var x) in  

  match a_i with 
  |Set(v,_,l)->
    let vs = L.map mk_exp vs in 
    let uks = L.map mk_exp uks in
    let uk0,uks' = (L.hd uks), (L.tl uks) in 
    let r_exp = L.fold_left2 mk_add_exp uk0 uks' vs in
    Set(v,r_exp,l)
  |_ -> E.s(E.error "incorrect assignment instruction %a" d_instr a_i)



class myQVisitor sfname ssid (vs:varinfo list) (uks:varinfo list)= object(self)
  inherit nopCilVisitor
  val mutable in_fun:bool = false

  method vstmt s = 
    let action (s: stmt) :stmt = 
      (match s.skind with 
      |Instr instrs when in_fun & s.sid = ssid & L.length instrs = 1 ->
	E.log "Found s_stmt:\n%a\n" d_stmt s;
	let new_i = mk_param_instr (L.hd instrs) vs uks in
	s.skind <- Instr [new_i]
      |_ -> ()
      );
      s
    in
    ChangeDoChildrenPost(s, action)

  method vfunc fd = 
    if fd.svar.vname <> "main" then (
      setFormals fd (fd.sformals@uks) (*add uk to function args*)
    );
    in_fun <- fd.svar.vname = sfname ;
    DoChildren
end

 

let transform (ast:file) (filename:string) (sfname:string) (ssid:int) 
    (fd: fundec) (tcs:testsuite) = begin

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
  in

  
  let myQ_typ:typ = match fd.svar.vtype with 
    |TFun(t,_,_,_) -> t
    |_ -> E.s(E.error "%s is not fun typ %a\n" fd.svar.vname d_type fd.svar.vtype)
  in

  let transform' (id:int) (cvs:varinfo list) = 
    E.log "comb %d. |vs|=%d [%s]\n" id (L.length cvs) 
      (String.concat ", " (L.map (fun vi -> vi.vname) cvs));

    (*modify file*)
    let ast' = copy_obj ast in 
    let n_uks = succ (L.length cvs) in 
    let (uks:varinfo list ref) = ref [] in 

    (*instr main*)
    ignore(visitCilFileSameGlobals ((new mainVisitor) n_uks myQ_typ tcs uks) ast');
    assert (L.length !uks = n_uks) ;
    ignore(visitCilFileSameGlobals ((new myQVisitor) sfname ssid cvs !uks) ast');

    let filename_tf = filename ^ "." ^ string_of_int id ^ ".tf.c" in
    write_src filename_tf ast';

    (*hackish way to prepend #include "klee/klee.h" to the generated file*)
    let cmd = 
      Printf.sprintf "sed -i '1i #include \"klee/klee.h\"' %s" filename_tf in
    E.log "cmd '%s'\n" cmd;

    (match Unix.system cmd with
    |Unix.WEXITED(0) -> ()
    |_ -> E.s(E.error "'%s' failed" cmd))

  in


  let vs' = fd.sformals@fd.slocals in 
  let vs = L.filter (fun vi -> vi.vtype = intType) vs' in
  E.log "|vs| = %d (of int type %d)\n" (L.length vs') (L.length vs);

  let cvss = L.flatten(L.map(fun siz -> combinations siz vs) (range(L.length vs))) in 
  let cvss = [[]]@cvss in
  E.log "total combs %d\n" (L.length cvss);
  
  L.iter2 (fun id cvs -> transform' id cvs) (range (L.length cvss)) cvss 
  
    
end  



(********************** Prototype **********************)

let main () = begin

  let filename = ref "" in
  let do_faultloc = ref false in

  let argDescr = [
    "--faultloc", Arg.Set do_faultloc, "do fault localization";
  ] in

  let handleArg s =
    if !filename = "" then filename := s
    else raise (Arg.Bad "unexpected multiple input files")
  in

  Arg.parse (Arg.align argDescr) handleArg "usage: tf [file.c]\n";

  let filename = !filename in 
  

  E.log "*** Read testcases for program '%s'\n" filename ;
  let tcs = get_tcs filename in
  let goods, bads = init_check filename tcs in


  initCIL();
  (*
    Note: src (filename) must be preprocessed by cil by running 
    cilly src.c --save-temps; the result is called src.cil.c

    Also, must have certain format  
    void main(..) {
    printf(myQ);...
    }

  *)
  let ast = Frontc.parse filename () in 

  (*** Initalize: assigning id's to stmts ***)
  initialize ast filename ;
  (* visitCilFileSameGlobals ((new printStmtVisitor) None) ast; *)


  (*Fault Localization part -- optional*)
  let ssids:sscore list = if !do_faultloc then fault_loc filename ast goods bads else [] in
    
    
  (*Bug Fixing part*)
  let sfname = "myQ" in
  let ssid = fst (L.hd ssids) in
  let fd = ref None in

  E.log "*** Get info on suspicious fun '%s' and sid %d\n" sfname ssid;
  ignore(visitCilFileSameGlobals ((new spyFunVisitor) sfname fd) ast);
  (*from fd figure out args type of myQ then do the conversion for tcs*)
  let fd = forceOption !fd in


  E.log "*** Transform file '%s' wrt fun '%s', sid '%d' with %d tcs\n"
    filename sfname ssid (L.length tcs);
  transform ast filename sfname ssid fd tcs;

  


  (* (\* ignore(Cfg.computeFileCFG ast); *\) *)


  (* let ssid = 1 in *)


  E.log "*** done"

end


let () = main ()


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
