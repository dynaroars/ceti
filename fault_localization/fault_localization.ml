(*Instrument C program to output visited statements*)

open Cil
open Cil_common
module E = Errormsg


let ht = Hashtbl.create 4096
let ctr = ref 1
let get_next_ct counter = let ct = !counter in incr counter;  ct

let can_modify (sk:stmtkind) : bool= 
(* List of stmts that can be modified 
   Todo: should be only assignment
*)

  match sk with 
  |Instr _ |Return _ |If _ |Loop _ -> true
  |_ -> false
  

class numVisitor = object
  (*Walks over AST and builds a hashtable that maps ints to stmts *)
  inherit nopCilVisitor
  method vblock b = 
    let action (b: block) :block= 
      let change_sid (s: stmt) :unit = 
	if can_modify s.skind then (
	  let ct = get_next_ct ctr in
	  s.sid <- ct;
	  Hashtbl.add ht ct s.skind
	)
	else s.sid <- 0;
      in 
      List.iter change_sid b.bstmts; 
      b
    in 
    ChangeDoChildrenPost(b, action)
end


(*walks over AST and preceeds each stmt with a printf 
  that writes out its sid*)
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


let instrument (filename: string)  :unit = 
  let ast = Frontc.parse filename () in 
  visitCilFileSameGlobals (new numVisitor) ast;
  write_file (filename ^ ".ast") ast;
  
  visitCilFileSameGlobals (new instrumentVisitor) ast;
  
    (*add to global
      _coverage_fout = fopen("gcd.c.path", "ab");
    *)
  let new_global = GVarDecl(stderr_va, !currentLoc) in
  ast.globals <- new_global :: ast.globals;
  let fd = getGlobInit ast in 
  let lhs = (Var(stderr_va),NoOffset) in 
  let str_exp1 = Const(CStr(filename ^ ".path" )) in 
  let str_exp2 = Const(CStr("ab")) in 
  let instr = Call((Some(lhs)), fopen, [str_exp1;str_exp2], !currentLoc) in
  let new_s = Cil.mkStmt (Instr[instr]) in 
  fd.sbody.bstmts <- new_s :: fd.sbody.bstmts;
  write_src (filename ^ ".instr.c") ast;
  
  let ctr' = !ctr-1 in
  write_file (filename ^ ".ht")  (ctr', ht)
    
    
let analyze_path (filename:string): int * (int,int) Hashtbl.t= 
  E.log "analyzing_path: %s\n" filename;
  let tc_ctr = ref 0 in
  let ht_stat = Hashtbl.create 1024 in 
  let mem = Hashtbl.create 1024 in 

  (try
    let fin = open_in filename in
    while true do 
      let line = input_line fin in
      let sid = int_of_string line in

      if sid = 0 then (
	incr tc_ctr;
	Hashtbl.clear mem;
      )
      else (
	let sid_tc = (sid, !tc_ctr) in
	if not (Hashtbl.mem mem sid_tc) then (
	  Hashtbl.add mem sid_tc ();

	  let num_occur = 
	    if not (Hashtbl.mem ht_stat sid) then 1
	    else (Hashtbl.find ht_stat sid) + 1
	  in Hashtbl.replace ht_stat sid num_occur;
	  
	)
      );
    done
  with _ -> ()
  );

  !tc_ctr, ht_stat
    

let tarantula_fault_loc (n_g:int) ht_g (n_b: int) ht_b :(int*float) list=
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

  let rs = Hashtbl.fold (fun sid _ rs->
    let get_n_occur sid (ht: (int,int) Hashtbl.t) : float=
      if Hashtbl.mem ht sid then float_of_int(Hashtbl.find ht sid) else 0. 
    in

    let freq_g = (get_n_occur sid ht_g) /. n_g' in
    let freq_b = (get_n_occur sid ht_b) /. n_b' in
    let score = freq_b /. (freq_g +. freq_b)  in
    (sid,score)::rs

  ) ht_sids [] in 

  let rs = List.sort (fun (_,score1) (_,score2) -> compare score2 score1 )rs in
  E.log "Tarantula statement scores\n";
  List.iter(fun (sid,score) -> E.log "%d -> %g\n" sid score) rs;
  rs


class sidVisitor (sid: int) = object
  (*Walks over AST and builds a hashtable that maps ints to stmts *)
  inherit nopCilVisitor
  method vstmt s = 
    let action (s: stmt): stmt= 
      (*E.log "test sid %d:\n%a\n" sid d_stmt s;*)
      if s.sid = sid then (
	E.log "sid %d:\n%a\n" sid d_stmt s
      );
      s
    in
    ChangeDoChildrenPost(s, action)
end


let fault_loc (filename: string) :unit = 
  let path_g = filename ^ ".gpath" in
  let path_b = filename ^ ".bpath" in
  
  assert (Sys.file_exists path_g);
  assert (Sys.file_exists path_b);
  
  let n_g, ht_g = analyze_path path_g in
  let n_b, ht_b = analyze_path path_b in 
  let sid_score_l = tarantula_fault_loc n_g ht_g n_b ht_b in

  let filename_ast = filename ^ ".ast" in
  assert (Sys.file_exists filename_ast);
  let ast = read_file  filename_ast in 
  
  List.iter(fun (sid,score) -> 
    E.log "score %g\n" score;
    visitCilFileSameGlobals (new sidVisitor sid) ast
  )sid_score_l;
  ()
  
  

  
let main (): unit = 

  let filename = ref "" in
  let do_instrument = ref false in

  let argDescr = [
    "--instrument", Arg.Set do_instrument, " instrument C file";
  ] in

  let handleArg s =
    if !filename = "" then filename := s
    else raise (Arg.Bad "unexpected multiple input files")
  in

  Arg.parse (Arg.align argDescr) handleArg "fault_localizer <filename>"  ;

  initCIL();

  if !do_instrument then instrument !filename 
  else fault_loc !filename; 
  ()



let () = main ()
