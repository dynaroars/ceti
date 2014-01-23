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
      
let rec range ?(a=0) b = if a >= b then [] else a::range ~a:(a+1) b 
let copy_obj (x : 'a) = let str = Marshal.to_string x [] in (Marshal.from_string str 0 : 'a)

let uk_min = -1 
let uk_max = 1

let boolTyp:typ = intType

let mk_lv ?(ftype=TVoid []) fname: lval = var(makeVarinfo true fname ftype)

let mk_call ?(ftype=TVoid []) ?(lv=None) fname args  : instr = 
  Call(lv, Lval (mk_lv ~ftype:ftype fname), args, !currentLoc)
  



class spyFunVisitor (fname:string) (fd:fundec option ref)= object(self)
  inherit nopCilVisitor
  method vfunc f = 
    if f.svar.vname = fname then (
      fd := Some f; 
    );
    SkipChildren
end

let mk_uks_main (fd:fundec) (n_uks:int) (myQ_typ:typ) (tcs:(int list * int) list) : (varinfo list * stmt list) =
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
    let i:instr = mk_call ~ftype:myQ_typ ~lv:(Some v) "myQ" inp_args in
    
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
   

class mainVisitor (n_uks:int) (myQ_typ:typ) (tcs:(int list * int) list) (uks:varinfo list ref)= object
  inherit nopCilVisitor
  method vfunc fd =
    let action(fd:fundec) : fundec =
      if fd.svar.vname = "main" then (
	let uks',stmts = mk_uks_main fd n_uks myQ_typ tcs in
	fd.sbody.bstmts <- stmts @ fd.sbody.bstmts;
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
    (fd: fundec) (tcs:(int list * int) list) = begin

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
    let n_uks = L.length cvs + 1 in 
    let (uks:varinfo list ref) = ref [] in 

    (*instr main*)
    ignore(visitCilFileSameGlobals ((new mainVisitor) n_uks myQ_typ tcs uks) ast');
    assert (L.length !uks = n_uks) ;
    ignore(visitCilFileSameGlobals ((new myQVisitor) sfname ssid cvs !uks) ast');

    write_src (filename ^ "." ^ string_of_int id ^ ".vu.c") ast'
  in


  let vs' = fd.sformals@fd.slocals in 
  let vs = L.filter (fun vi -> vi.vtype = intType) vs' in
  E.log "|vs| = %d (of int type %d)\n" (L.length vs') (L.length vs);

  let cvss = L.flatten(L.map(fun siz -> combinations siz vs) (range(L.length vs))) in 
  let cvss = [[]]@cvss in
  E.log "total combs %d\n" (L.length cvss);
  
  L.iter2 (fun id cvs -> 
    transform' id cvs
  ) (range (L.length cvss)) cvss 
    
end  


(*********************** Reading Testcases ***********************)

let string_of_tc (tc:int list * int) : string = 
  let inp,outp = tc in 
  let inp = String.concat "; " (L.map string_of_int inp) in
  let outp = string_of_int outp in 
  "([" ^ inp ^ "]" ^ ", " ^ outp ^ "]"

let string_of_tcs (tcs:(int list * int) list) :string = 
  let tcs = L.map string_of_tc tcs in 
  let tcs = String.concat "; " tcs in
  "["^ tcs ^ "]"
  

let get_tcs (filename:string) : (int list * int) list = 
  let finputs = filename ^ ".inputs" in
  let foutputs = filename ^ ".outputs" in 

  let tcs:(int list * int) list ref = ref [] in

  (try
     let fin = open_in finputs in
     let fout = open_in foutputs in 

     while true do 
       let outp = input_line fout in
       let inp = Str.split (Str.regexp "[ \t]+")  (input_line fin) in
       
       (try
	  let ios x = int_of_string (strip x) in 
	  let outp' = ios outp in 
	  let inp' = L.map ios inp in 
	  tcs := (inp',outp')::!tcs
	    
	with _ -> 
	  E.error "Ignoring (%s, %s)" (String.concat ", " inp) outp
       )
     done;
   with _ -> ()
  );  
  L.rev !tcs     


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
	else s.sid <- 0;
      in 
      List.iter change_sid b.bstmts; 
      b
    in 
    ChangeDoChildrenPost(b, action)
end


let initialize (ast:file) = 
  visitCilFileSameGlobals (new everyVisitor) ast ;
  visitCilFileSameGlobals (new numVisitor) ast



(******************* Fault Localization *******************)

(******************* 1. Coverage *******************)
(*walks over AST and preceeds each stmt with a printf that writes out its sid*)
  
let fprintf_va = makeVarinfo true "fprintf" (TVoid [])
let fprintf = Lval((Var fprintf_va), NoOffset)
let stderr_va = makeVarinfo true "_coverage_fout" (TPtr(TVoid [], []))
let stderr = Lval((Var stderr_va), NoOffset)
let fflush_va = makeVarinfo true "fflush" (TVoid [])
let fflush = Lval((Var fflush_va), NoOffset)
let fopen_va = makeVarinfo true "fopen" (TVoid [])
let fopen = Lval((Var fopen_va), NoOffset)

let create_fprintf_stmt (sid: int) :stmt = 
  let str = Printf.sprintf "%d\n" sid in
  let str_exp = Const(CStr(str)) in
  let instr1 = Call(None, fprintf, [stderr; str_exp], !currentLoc) in
  let instr2 = Call(None, fflush, [stderr], !currentLoc) in 
  let skind = Instr([instr1; instr2]) in
  let new_s = mkStmt skind in 
  new_s

class instrumentVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    let action (b: block) :block= 
      let insert_printf (s: stmt): stmt list = 
	if s.sid > 0 then [create_fprintf_stmt s.sid; s]
	else [s]
      in
      let result = List.map insert_printf b.bstmts in 
      {b with bstmts = List.flatten result}
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




(********************** Prototype **********************)

let main () = begin
  if Array.length Sys.argv < 2 then (E.log "usage: tf [file.c]\n";exit 1);
  initCIL();

  let filename = Sys.argv.(1) in 
  let ast = Frontc.parse filename () in 
  write_src (filename ^ ".orig.c") ast;



  (*** Initalize: assigning id's to stmts ***)
  initialize ast;
  write_src (filename ^ ".init.c") ast;

  


  (* E.log "*** Read testcases for program '%s'\n" filename ; *)
  (* let tcs = get_tcs filename in  *)
  (* if L.length tcs <= 0 then ( *)
  (*   E.log "no testcase found\n"; *)
  (*   exit 1 *)
  (* ); *)
  (* E.log "|tcs|=%d\n" (L.length tcs); *)
  (* (\*E.log "%s\n" (string_of_tcs tcs);*\) *)



  (* ignore(Cfg.computeFileCFG ast); *)

  (* let sfname = "myQ" in  *)
  (* let ssid = 2 in  *)
  (* let fd = ref None in  *)

  (* E.log "*** Get info on suspicious fun '%s' and sid %d\n" sfname ssid; *)
  (* ignore(visitCilFileSameGlobals ((new spyFunVisitor) sfname fd) ast); *)
  (* (\*from fd figure out args type of myQ then do the conversion for tcs*\) *)
  (* let fd = forceOption !fd in  *)


  (* E.log "*** Transform file '%s' wrt fun '%s', sid '%d' with %d tcs\n"  *)
  (*   filename sfname ssid (L.length tcs); *)
  (* transform ast filename sfname ssid fd tcs; *)


  E.log "*** done"

end


let () = main ()


(*Questions:

1. how to make true/false in Cil  ,  is it just one/zero ?
2. how to add the directive  #include "klee/klee.h" ?
3. getting all variable at a particular location (including tmp vars in the functions at that loc)
4. Break instruments into individual statement
5. Convert global to local
6. How to keep track of stmt after modifcation ? 
*)
