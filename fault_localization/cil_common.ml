

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
