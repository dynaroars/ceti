open Cil
open Vu_common
module E = Errormsg

let vdebug:bool ref = ref false


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

(*commands*)
let gcc_cmd = P.sprintf "gcc %s -o %s >& /dev/null"

(*gcc filename.c;  return "filename.exe" if success else None*)
let compile (src:string): string = 
  let exe = src ^ ".exe" in 
  (try Unix.unlink exe with _ -> () ) ; 
  let cmd = gcc_cmd src exe in
  E.log "cmd '%s'\n" cmd ;
  exec_cmd cmd ;
  exe


(*Cill common*)
type sid_t = int


let mk_vi ?(ftype=TVoid []) fname: varinfo = makeVarinfo true fname ftype

(*av = fname(args)*)
let mk_call ?(ftype=TVoid []) ?(av=None) fname args : instr = 
  let f = var(mk_vi ~ftype:ftype fname) in
  Call(av, Lval f, args, !currentLoc)


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
  

