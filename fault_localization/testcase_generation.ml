open Cil
open Cil_common

(*conclic exp*)
type opkind = Constant | Address
let string_of_op (op: int64) (ok: opkind) : string =
  let op_str = Int64.to_string op in
  match ok with
  |Constant -> op_str
  |Address -> "[" ^ op_str ^ "]"


let opkind_of_int (i:int) : opkind = 
  match i with 
  |0 -> Constant
  |1 -> Address
  |_ -> failwith (Printf.sprintf "Bad opkind %d" i)


type bop =
|Plus |Minus |Times |Div |Mod
|Shiftl |Shiftrl |Shiftra
|Lt |Gt |Le |Ge |Eq |Ne
|BAnd |BXor | BOr
|LAnd |LOr

let string_of_bop (b: bop) : string =
  match b with
  |Plus     -> "+"  |Minus    -> "-"   |Times    -> "*"
  |Div      -> "/"  |Mod      -> "%"   |Shiftl   -> ">>"
  |Shiftrl  -> ">>" |Shiftra  -> ">>>" |Lt       -> "<"
  |Gt       -> ">"  |Le       -> "<="  |Ge       -> ">="
  |Eq       -> "==" |Ne       -> "!="  |BAnd     -> "&"
  |BXor     -> "^"  |BOr      -> "|"   |LAnd     -> "&&"
  |LOr      -> "||"



let bop_table = [|
  Plus; Minus; Times; Div; Mod;
  Shiftl; Shiftrl; Shiftra;
  Lt; Gt; Le; Ge; Eq; Ne;
  BAnd; BXor;  BOr;
  LAnd; LOr;
|]
  
let bop_of_int (b: int): bop = bop_table.(b)
let int_of_bop (b: bop): int = List.hd (array_mem bop_table b)

let apply_bop (b: bop) (x: int64) (y: int64): int64 = 
  match b with
  |Plus     -> Int64.add x y
  |Minus    -> Int64.sub x y
  |Times    -> Int64.mul x y
  |Div      -> Int64.div x y
  |Mod      -> Int64.rem x y
  |Shiftl   -> Int64.shift_left x (Int64.to_int y)
  |Shiftrl  -> Int64.shift_right_logical x (Int64.to_int y)
  |Shiftra  -> Int64.shift_right x (Int64.to_int y)
  |Lt       -> if x < y  then Int64.one else Int64.zero
  |Gt       -> if x > y  then Int64.one else Int64.zero
  |Le       -> if x <= y then Int64.one else Int64.zero
  |Ge       -> if x >= y then Int64.one else Int64.zero
  |Eq       -> if x = y  then Int64.one else Int64.zero
  |Ne       -> if x <> y then Int64.one else Int64.zero
  |BAnd     -> Int64.logand x y
  |BXor     -> Int64.logxor x y
  |BOr      -> Int64.logor  x y
  |LAnd     -> if x <> Int64.zero && y <> Int64.zero
    then Int64.one else Int64.zero
  |LOr      -> if x <> Int64.zero || y <> Int64.zero
    then Int64.one else Int64.zero

let bop_neg (b: bop): bop = 
  match b with
  |Lt -> Ge |Ge -> Lt |Le -> Gt |Gt -> Le |Eq -> Ne |Ne -> Eq
  |_ -> b

type uop =
| Neg
| BNot
| LNot

let uop_table = [| Neg; BNot; LNot; |]
let string_of_uop (u : uop) : string =
  match u with
  | Neg  -> "-" | BNot -> "~" | LNot -> "!"

let uop_of_int (u: int): uop = uop_table.(u)
let int_of_uop (u: uop): int = List.hd (array_mem uop_table u)

let apply_uop (u : uop) (o : int64) : int64 =
  match u with
  | Neg  -> Int64.neg o | BNot -> Int64.lognot o
  | LNot -> if o = Int64.zero then Int64.one else Int64.zero
      

let main () = ()
let () =  main ()
