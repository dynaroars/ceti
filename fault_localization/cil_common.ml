open Cil
module E = Errormsg

let printf = Printf.printf

let vDEBUG = ref true 

let write_src ?(use_stdout=false) (filename:string) (ast:file): unit = 
  let df o =  dumpFile defaultCilPrinter o filename ast in
  if use_stdout then df stdout else (
    let fout = open_out filename in
    df fout;
    close_out fout;
    if !vDEBUG then E.log "write_src: \"%s\"\n" filename
  )

let write_file ?(bin=true) (filename:string) content: unit = 
  let fout = (if bin then open_out_bin else open_out) filename in
  Marshal.to_channel fout content [];
  close_out fout;
  if !vDEBUG then E.log "write_bin_file: \"%s\"\n" filename

let read_file ?(bin=true) (filename:string): file =
  let fin = (if bin then open_in_bin else open_in) filename in
  let ast = Marshal.from_channel fin in
  close_in fin;
  if !vDEBUG then E.log "read_file: \"%s\"\n" filename;
  ast





(*Common utils*)

let array_find(f: 'a -> bool) (a:' a array): int list = 
  let rs = Array.fold_left (
    fun (idx,idxl) x -> idx+1, if f x then idxl@[idx] else idxl
  ) (0, []) a 
  in snd(rs)


let array_mem(a: 'a array) (x: 'a): int list = 
  array_find (fun y -> x = y) a

let int32_of_int64 (i: int64) : int32 = Int32.of_int (Int64.to_int i)

let forceOption (ao : 'a option) : 'a =
  match ao with
  | Some a -> a
  | None -> raise(Failure "forceOption")


let string_of_bool_array (ba : bool array) : string =
  let bs =
    let s = (List.map (fun b -> if b then "1" else "0") (List.rev (Array.to_list ba)))
    in String.concat "" s
  in
  "0b"^bs

let int64_of_bool_array (ba : bool array) : int64 =
  Int64.of_string (string_of_bool_array ba)



let rec findType (gl : global list) (typname : string) : typ =
  match gl with
  | [] -> E.s (E.error "Type not found: %s" typname)
  | GType(ti,_) :: _        when ti.tname = typname -> TNamed(ti,[])
  | GCompTag(ci,_) :: _     when ci.cname = typname -> TComp(ci,[])
  | GCompTagDecl(ci,_) :: _ when ci.cname = typname -> TComp(ci,[])
  | GEnumTag(ei,_) :: _     when ei.ename = typname -> TEnum(ei,[])
  | GEnumTagDecl(ei,_) :: _ when ei.ename = typname -> TEnum(ei,[])
  | _ :: rst -> findType rst typname

let rec findGlobalVar (gl : global list) (varname : string) : varinfo =
  match gl with
  | [] -> E.s (E.error "Global not found: %s" varname)
  | GVarDecl(vi, _) :: _ when vi.vname = varname -> vi
  | GVar(vi, _, _) :: _ when vi.vname = varname -> vi
  | _ :: rst -> findGlobalVar rst varname


let snd3 (_,b,_) = b
let fst3 (a,_,_) = a

let i2s (i : instr) : stmt = mkStmt(Instr [i])

let v2e (v : varinfo) : exp = Lval(var v)

let (|>) (a : 'a) (f : 'a -> 'b) : 'b = f a

let onlyFunctions (fn : fundec -> location -> unit) (g : global) : unit = 
  match g with
  | GFun(f, loc) -> fn f loc
  | _ -> ()

let function_elements (fe : exp) : typ * (string * typ * attributes) list =
  match typeOf fe with
  | TFun(rt, Some stal, _, _) -> rt, stal
  | TFun(rt, None,      _, _) -> rt, []
  | _ -> E.s(E.bug "Expected function expression")
