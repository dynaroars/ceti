(*
  Common utilities for Ocaml
  by ThanhVu Nguyen
*)

module L = List
module H = Hashtbl
module P = Printf
let vdebug:bool ref = ref false

(*** general utils ***)
let combinations k l =
  let rec aux k acc emit = function
    | [] -> acc
    | h :: t ->
      if k = 1 then aux k (emit [h] acc) emit t else
        let new_emit x = emit (h :: x) in
        aux k (aux (k-1) acc new_emit t) emit t
  in
  let emit x acc = x :: acc in
  aux k [] emit l

let rec take n = function 
  |[] -> [] 
  |h::t -> if n = 0 then [] else h::take (n-1) t

let rec range ?(a=0) b = if a >= b then [] else a::range ~a:(succ a) b 

let list_uniq l = 
  let n = L.length l in 
  let ht = H.create (if n > 1024 then 1024 else n) in 
  let l = L.fold_left (
    fun l' e -> if H.mem ht e then l' else (H.add ht e (); e::l')
  ) [] l in
  L.rev l

(*[Some 1, None, Some 2] -> [1,2]*)
let list_of_some (l:'a option list):'a list = 
  let rs = 
    L.fold_left (fun l' -> function |Some f -> f::l' |None -> l') [] l
  in L.rev rs


let keys_of_ht ht = L.rev (H.fold (fun k _ l -> k::l) ht [])
let values_of_ht ht = L.rev (H.fold (fun _ v l -> v::l) ht [])
let items_of_ht ht = L.rev (H.fold (fun k v l -> (k,v)::l) ht [])


let ht_of_pair_list l = 
  let ht = H.create (L.length l) in 
  L.iter (fun (x,y) -> H.add ht x y) l;
  ht

(* map element e to its occurences *)
let set_ht_counter ht = 
  L.iter(fun e ->
    let n_occurs = try succ (H.find ht e) with _ -> 1 in
    H.replace ht e n_occurs
  ) 

let mk_ht_counter elems = 
  let ht = H.create 1024 in 
  set_ht_counter ht elems;
  ht


let merge_counters hts = 
  let ht = H.create 1024 in 
  L.iter (H.iter (fun e n -> try H.replace ht e (n + (H.find ht e)) with Not_found -> H.add ht e n)) hts;
  ht

(*** string utils ***)
let string_of_list ?(delim:string = ", ") =  String.concat delim
let string_of_ints ?(delim:string = ", ") (l:int list): string = 
  string_of_list ~delim (L.map string_of_int l)

let strip (s:string): string =
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
  try ignore (Str.search_forward (Str.regexp_string s1) s2 0); true
  with Not_found -> false

let str_split s:string list =  Str.split (Str.regexp "[ \t]+")  s

(*** file utils ***)
let copy_obj (x : 'a) = 
  let s = Marshal.to_string x [] in (Marshal.from_string s 0 : 'a)

(*create a temp dir*)
let mkdir_tmp ?(use_time=false) ?(temp_dir="") dprefix dsuffix =
  
  let dprefix = if use_time 
    then P.sprintf "%s_%d" dprefix (int_of_float (Unix.time())) 
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

(*returns a list of lines from an ascii file*)
let vassert ?(msg="") (cond:bool) : unit = if not cond then failwith msg
  
let chk_exist ?(msg="") (filename:string) : unit =
  vassert (Sys.file_exists filename) 
    ~msg:(P.sprintf "file '%s' not exist" filename)

let read_file_ascii  ?(keep_empty=true) (filename:string) :string list =
  let lines:string list ref = ref [] in
  chk_exist filename;
  let fin = open_in filename in
  (try
     while true do 
       let line = strip (input_line fin) in 
       lines := line::!lines
       done
   with _ -> close_in fin);

  let lines = L.rev !lines in 
  if keep_empty then lines else L.filter (fun l -> l <> "") lines

let read_lines filename =
  P.printf "W: 'read_lines' deprecated, use 'read_file_ascii' instead\n%!";
  read_file_ascii filename

let write_file_ascii (filename:string) (content:string): unit = 
  let fout = open_out filename in
  P.fprintf fout "%s" content; 
  close_out fout;
  if !vdebug then P.printf "write_file_str: '%s'\n%!" filename

let write_file_str filename =
  P.printf "W: 'write_file_str' deprecated, use 'write_file_ascii' instead\n%!";
  write_file_ascii filename

let write_file_bin (filename:string) content: unit = 
  let fout = open_out_bin filename in
  Marshal.to_channel fout content [];
  close_out fout;
  if !vdebug then P.printf "write_file_bin: '%s'\n%!" filename

let read_file_bin (filename:string) =
  let fin = open_in_bin filename in
  let content = Marshal.from_channel fin in
  close_in fin;
  if !vdebug then P.printf "read_file: '%s'\n%!" filename;
  content



let exec_cmd cmd = 
  if !vdebug then P.printf "$ %s\n%!" cmd ;
  match Unix.system cmd with
  |Unix.WEXITED(0) -> ()
  |_ -> failwith (P.sprintf "cmd failed '%s'" cmd)


(*commands*)
(*let gcc_cmd = P.sprintf "gcc %s -o %s >& /dev/null"*)
let gcc_cmd = P.sprintf "gcc %s -o %s > /dev/null 2>&1"

(*gcc filename.c;  return "filename.exe" if success else None*)
let compile (src:string): string = 
  let exe = src ^ ".exe" in 
  (try Unix.unlink exe with _ -> () ) ; 
  let cmd = gcc_cmd src exe in
  exec_cmd cmd ;
  exe
