module H = Hashtbl
module P = Printf
module E = Errormsg
module L = List
open Cil

let write_src ?(use_stdout:bool=false) (filename:string) (ast:file): unit = 
  let df oc =  dumpFile defaultCilPrinter oc filename ast in
  if use_stdout then df stdout else (
    let fout = open_out filename in
    df fout;
    close_out fout;
    P.printf "write_src: '%s'\n%!" filename
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


let boolTyp:typ = intType


(*Cill common*)
type sid_t = int

let mk_vi ?(ftype=TVoid []) fname: varinfo = makeVarinfo true fname ftype

(*av = fname(args)*)
let mk_call ?(ftype=TVoid []) ?(av=None) (fname:string) args : instr = 
  let f = var(mk_vi ~ftype:ftype fname) in
  Call(av, Lval f, args, !currentLoc)

let sids_of_stmts = L.map (fun stmt -> stmt.sid)

let string_of_typ (s:typ) = Pretty.sprint ~width:80 (dn_type () s) 
let string_of_stmt (s:stmt) = Pretty.sprint ~width:80 (dn_stmt () s) 
let string_of_exp (s:exp) = Pretty.sprint ~width:80 (dn_exp () s) 
let string_of_instr (s:instr) = Pretty.sprint ~width:80 (dn_instr () s) 
let string_of_lv (s:lval) = Pretty.sprint ~width:80 (dn_lval () s) 

let exp_of_vi (vi:varinfo): exp = Lval (var vi)
(*"3" Int -> 3,  "3.2" Float -> 3.2*)
let const_exp_of_string (t:typ) (s:string): exp = match t with
  |TInt _ -> integer (int_of_string s)
  |TFloat(fk,_) -> Const(CReal(float_of_string s,fk,None))
  |_-> E.s(E.error "unexp typ %a " dn_type t)

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
    
  |_ -> E.s(E.error "unknown binop")

let string_of_unop = function
  |Neg -> "unary -"
  |BNot -> "~"
  |LNot -> "!"
  





(*** Visitors ***)

(* 
 * This visitor changes empty statement lists (e.g., the else branch in 
 * if (foo) { bar(); } ) into dummy statements that we can modify later. 
 *)
class emptyVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    ChangeDoChildrenPost(b,(fun b ->
      if b.bstmts = [] then 
        mkBlock [ mkEmptyStmt () ] 
      else b 
    ))
end   


(*Makes every instruction into its own stmt*)
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





let can_modify : stmtkind -> bool = function 
|Instr[Set(_)] -> true
|_ -> false



(*
  walks over AST and preceeds each stmt with a printf that writes out its sid
  create a stmt consisting of 2 Call instructions
  fprintf "_coverage_fout, sid";
  fflush();
*)
let stderr_vi = mk_vi ~ftype:(TPtr(TVoid [], [])) "_coverage_fout"

class coverageVisitor filter_f = object(self)
  inherit nopCilVisitor

  method private create_fprintf_stmt (s: string) :stmt =
  let stderr = exp_of_vi stderr_vi in
  let instr1 = mk_call "fprintf" [stderr; Const (CStr(s))] in
  let instr2 = mk_call "fflush" [stderr] in
  mkStmt (Instr([instr1; instr2]))
    
  method vblock b =
    let action (b: block) :block=
      let insert_printf (s: stmt): stmt list =
	if filter_f s.skind then 
	  [self#create_fprintf_stmt ((string_of_int s.sid)^"\n"); s]
	else
	  [s]
      in
      let stmts = L.map insert_printf b.bstmts in
      {b with bstmts = L.flatten stmts}
    in
    ChangeDoChildrenPost(b, action)
end

let mk_coverage (ast:file) (filter_f:stmtkind -> bool) (filename_cov:string) (filename_path:string) =

  (*add printf stmts*)
  visitCilFileSameGlobals ((new coverageVisitor) filter_f) ast;

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




(* Walks over AST and builds a hashtable that maps int to stmt*fundec 
   Creates new statement id
*)
class numVisitor ht filter_f = object(self)
  inherit nopCilVisitor

  val mutable mctr = 1
  val mutable cur_fd = None

  method vfunc f = cur_fd <- (Some f); DoChildren

  (*Stmts that can be tracked for fault loc and modified for bug fix *)
  method private can_modify : stmtkind -> bool = function 
  |Instr[Set(_)] -> true
  |_ -> false

  method vblock b = 
    let action (b: block) : block= 
      let change_sid (s: stmt) : unit = 
	if filter_f s.skind then (
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

(*like numvisitor but does not create new stmt id's 
  (assume these are computed, e.g., when doing CFG) *)
class storeHTVisitor ht filter_f = object(self)
  inherit nopCilVisitor

  val mutable cur_fd = None

  method vfunc f = cur_fd <- (Some f); DoChildren

  method vblock b = 
    let action (b: block) : block= 
      let change_sid (s: stmt) : unit = 
	if filter_f s.skind then (
	  let fd = match cur_fd with 
	    | Some f -> f | None -> E.s(E.error "not in a function") 
	  in
	  H.add ht s.sid (s, fd)
	)
      in 
      L.iter change_sid b.bstmts; 
      b
    in 
    ChangeDoChildrenPost(b, action)

end




(*Stmts that can be tracked for fault loc and modified for bug fix *)
let mk_stmt_ht ?(create_stmt_ids:bool=false) ast filter_f = 
  let stmt_ht:(int,stmt*fundec) H.t = H.create 1024 in 
  let cl = if create_stmt_ids then (new numVisitor) else (new storeHTVisitor) in
  visitCilFileSameGlobals (cl stmt_ht filter_f :> cilVisitor) ast; 
  stmt_ht

