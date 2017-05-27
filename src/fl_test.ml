open Cil
open Vu_common
(*open Ceti_common*)
open Fl
module E = Errormsg
module H = Hashtbl
module P = Printf

let () = begin
  E.colorFlag := true;

  let filename = ref "" in
  let inputs   = ref "" in
  let outputs  = ref "" in 

  let arg_descrs = [
    "--debug", Arg.Set vdebug, 
    P.sprintf " shows debug info (default %b)" !vdebug;

    "--fl_alg", Arg.Set_int fl_alg,
    P.sprintf 
      " use fault loc algorithm: 1 Ochia, 2 Tarantula (default %d)" 
      !fl_alg;

    "--top_n_sids", Arg.Set_int top_n_sids,
    P.sprintf " consider this # of suspicious stmts (default %d)" 
      !top_n_sids;

    "--min_sscore", Arg.Set_float min_sscore,
    P.sprintf " fix suspicious stmts with at least this score (default %g)" 
      !min_sscore;

  ] in 
  let handle_arg s =
    if !filename = "" then (
      chk_exist s ~msg:"require filename"; filename := s
    )
    else if !inputs = "" then inputs := s
    else if !outputs = "" then outputs := s
    else raise (Arg.Bad "too many input args")
  in
  let usage = P.sprintf "usage: tf src inputs outputs [options]\n" in

  Arg.parse (Arg.align arg_descrs) handle_arg usage;
  initCIL();
  Cil.lineDirectiveStyle:= None;
  Cprint.printLn:=false; (*don't print line #*)

  (* for Cil to retain &&, ||, ?: instead of transforming them to If stmts *)
  Cil.useLogicalOperators := true; 

  chk_exist !inputs  ~msg:"require inputs file";
  chk_exist !outputs ~msg:"require outputs file";

  (*create a temp dir to process files*)
  let tdir = mkdir_tmp "fault_loc" "" in
  let fn' = P.sprintf "%s/%s" tdir (Filename.basename !filename) in 
  exec_cmd (P.sprintf "cp %s %s" !filename fn');
  
  let filename,inputs,outputs = fn', !inputs, !outputs in
  at_exit (fun () ->  E.log "Note: temp files created in dir '%s'\n" tdir);

  let tcObj = (new uTest) filename in
  tcObj#get_tcs inputs outputs;
  
  let ast = Frontc.parse filename () in 

  visitCilFileSameGlobals (new emptyVisitor) ast;
  visitCilFileSameGlobals (new everyVisitor) ast;
  visitCilFileSameGlobals (new breakCondVisitor :> cilVisitor) ast;
  Cfg.computeFileCFG ast;

  let stmt_ht:(sid_t,stmt*fundec) H.t = H.create 1024 in 
  visitCilFileSameGlobals ((new storeHTVisitor) stmt_ht :> cilVisitor) ast;
  write_src (ast.fileName ^ ".preproc.c") ast;

  let cfg_contents = ref "" in
  ignore(visitCilFileSameGlobals (new printCFGVisitor cfg_contents) ast);
  (*E.log "%s" !cfg_contents;*)
  write_file_str (ast.fileName ^ ".cfg") !cfg_contents;

  let flVis = (new faultloc) ast tcObj#mygoods tcObj#mybads stmt_ht in
  let ssids:sidscore_t list = flVis#get_susp_sids !fl_alg in

  let idx = ref 0 in 
  let ssids = L.filter (fun (sid,score) ->
    let s,f = H.find stmt_ht sid in
    if score >= !min_sscore && (can_modify s.skind) then(
      E.log "%d. sid %d in fun '%s' (score %g)\n%a\n"
    	!idx sid f.svar.vname score dn_stmt s;
      incr idx;
      true
    ) else false
  ) ssids in
  
  ealert "FL: found %d ssids with sscores >= %g" 
    (L.length ssids) !min_sscore;

  if L.length ssids = 0 then (ealert "No suspicious stmts !")
  else(
    let ssids = take !top_n_sids ssids in (*consider only n top susp stmts*)
    L.iter (fun (sid,score) -> 
       let s,fd = H.find stmt_ht sid in  
       P.printf "sid %d, score %g: %s (fun: %s)\n%!"  
   	sid score (string_of_stmt s) fd.svar.vname 
    ) ssids
  )

end
