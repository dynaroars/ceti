open Cil
open Vu_common
open Ceti_common
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
  visitCilFileSameGlobals (new everyVisitor) ast;
  visitCilFileSameGlobals (new breakCondVisitor :> cilVisitor) ast;

  let stmt_ht:(sid_t,stmt*fundec) H.t = H.create 1024 in 
  visitCilFileSameGlobals ((new numVisitor) stmt_ht:> cilVisitor) ast;
  write_src (ast.fileName ^ ".preproc.c") ast;

  let fl_sids:sid_t list = 
    let flVis = (new faultloc) ast tcObj#mygoods tcObj#mybads stmt_ht in
    let sids' = flVis#fl !fl_alg !min_sscore in
    take !top_n_sids sids'   (*consider only n top susp stmts*)
  in

  if L.length fl_sids = 0 then (ealert "No suspicious stmts !"; exit 0)
  else(
    L.iter (fun sid -> 
      let s,fd = H.find stmt_ht sid in 
      P.printf "sid %d: %s (fun: %s)\n%!" 
	sid (string_of_stmt s) fd.svar.vname
    ) fl_sids
  );
end
