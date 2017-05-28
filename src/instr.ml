(*ocamlfind ocamlopt -package str,batteries,cil  cil_common.cmx -linkpkg -thread tf.ml*)
(*Takes in a preprocess file , e.g., cil.i 
for i in {1..41}; do cilly bug$i.c --save-temps --noPrintLn --useLogicalOperators; done
 *)

(*open Ceti_common*)
open Cil
module E = Errormsg
module L = List
module H = Hashtbl 
module P = Printf
module FL = Fl

module CC = Cil_common
module VC = Vu_common
module ST = Settings
module CM = Common
	      
(*filename formats*)
let transform_s = P.sprintf "%s.s%s.%s.ceti.c" (*f.c.s5.z3_c2.ceti.c*)

(* specific options for this program *)
let tpl = ref 0
let idxs = ref []
let xinfo = ref "" (*helpful info for debugging*)

(******************* Transforming File *******************)

(*add uk's to function args, e.g., fun(int x, int uk0, int uk1);*)
class funInstrVisitor (uks:varinfo list) = object
  inherit nopCilVisitor

  val ht = H.create 1024 
  method ht = ht

  method vfunc fd = 
    if fd.svar.vname <> "main" then (
      setFormals fd (fd.sformals@uks) ;
      H.add ht fd.svar.vname () 
    );
    DoChildren
end

(*insert uk's as input to all function calls
  e.g., fun(x); -> fun(x,uk0,uk1); *)
class instrCallVisitor (uks:varinfo list) (funs_ht:(string,unit) H.t)= object
  inherit nopCilVisitor

  method vinst (i:instr) =
    match i with 
    | Call(lvopt,(Lval(Var(vi),NoOffset)), args,loc) 
	 when H.mem funs_ht vi.vname ->
       let uks' = L.map CC.exp_of_vi uks in 
       let i' = Call(lvopt,(Lval(Var(vi),NoOffset)), args@uks',loc) in
       ChangeTo([i'])

    |_ -> SkipChildren
end

(*make calls to mainQ on test inp/oupt:
  mainQ_typ temp;
  temp = mainQ(inp0,inp1,..);
  temp == outp
 *)
let mk_main (main_fd:fundec) (mainQ_fd:fundec) (tcs:FL.testcase_t list) 
	    (uks:varinfo list) (instrs1:instr list) :stmt list= 
  
  let rs = L.map (fun ((inps:FL.inp_t), outp) -> 
		  let mainQ_typ:typ = match mainQ_fd.svar.vtype with 
		    |TFun(t,_,_,_) -> t
		    |_ -> E.s(E.error "%s is not fun typ %a\n" 
				      mainQ_fd.svar.vname d_type mainQ_fd.svar.vtype)
		  in
		  
		  (*mainQ_typ temp;*)
		  let temp:lval = var(makeTempVar main_fd mainQ_typ) in 
		  
		  (*tmp = mainQ(inp, uks);*)
		  let args_typs = L.map (fun vi -> vi.vtype) mainQ_fd.sformals in
		  assert (L.length args_typs = L.length inps);

		  let args = L.map2 (fun t x -> CC.const_exp_of_string t x) args_typs inps in 
		  let i:instr = CC.mk_call ~ftype:mainQ_typ ~av:(Some temp) "mainQ" args in
		  
		  let e:exp = BinOp(Eq, 
				    Lval temp, CC.const_exp_of_string mainQ_typ outp, 
				    CC.boolTyp) in 
		  i,e
		 ) tcs in

  let instrs2, exps = L.split rs in 

  (*creates reachability "goal" stmt 
    if(e_1,..,e_n){printf("GOAL: uk0 %d, uk1 %d ..\n",uk0,uk1);klee_assert(0);}
   *)
  let s = L.map (
	      fun vi -> vi.vname ^ (if vi.vtype = intType then " %d" else " %g")
	    ) uks in
  let s = "GOAL: " ^ (String.concat ", " s) ^ "\n" in 
  let print_goal:instr = CC.mk_call "printf" 
				    (Const(CStr(s))::(L.map CC.exp_of_vi uks)) in 
  
  (*klee_assert(0);*)
  let klee_assert_zero:instr = CC.mk_call "klee_assert" [zero] in
  (*let klee_assert_zero:instr = CC.mk_call "__VERIFIER_error" [] in *)
  
  
  let and_exps = CM.apply_binop LAnd exps in
  let reach_stmt = mkStmt (Instr([print_goal; klee_assert_zero])) in
  reach_stmt.labels <- [Label("ERROR",!currentLoc,false)];
  let if_skind = If(and_exps, 
		    mkBlock [reach_stmt], 
		    mkBlock [], 
		    !currentLoc) 
  in
  
  let instrs_skind:stmtkind = Instr(instrs1@instrs2) in
  [mkStmt instrs_skind; mkStmt if_skind]

(* modify statements *)
class modStmtVisitor 
	(sids:int list) 
	(mk_instr:instr -> varinfo list ref -> instr list ref -> instr) = 
object (self)

  inherit nopCilVisitor 

  val uks   :varinfo list ref = ref []
  val instrs:instr list ref = ref []
  val mutable status = ""

  method uks    = !uks
  method instrs = !instrs
  method status = status

  method vstmt (s:stmt) = 
    let action (s:stmt): stmt = 
      (match s.skind with 
       |Instr ins when L.mem s.sid sids ->
	 assert (L.length ins = 1);

	 (*CC.ealert "debug: stmt %d\n%a\n" sid dn_stmt s;*)

	 let old_i = L.hd ins in 
	 let new_i = mk_instr old_i uks instrs in	
	 s.skind <- Instr[new_i];

	 status <- (P.sprintf "%s ## %s"  (*the symbol is used when parsing*)
			      (CC.string_of_instr old_i) (CC.string_of_instr new_i));

	 if !VC.vdebug then CC.ealert "%s" status

       |_ -> ()
      ); s in
    ChangeDoChildrenPost(s, action)  
end
  


(*runs in parallel*)
let transform 
      (filename:string) 
      (sids:CC.sid_t list) 
      (tpl_id:int) 
      (xinfo:string) 
      (idxs:int list) = 

  let (ast:file),(mainQ_fd:fundec),(tcs:FL.testcase_t list) =
    VC.read_file_bin (ST.ginfo_s filename) in

  let main_fd = CM.find_fun ast "main" in 
  let sid = L.hd sids in (*FIXME*)
  let sids_s = VC.string_of_ints ~delim:"_" sids in 

  (*modify stmt*)  
  let cl = L.find (fun cl -> cl#cid = tpl_id ) CM.tpl_classes in 
  let mk_instr:(instr-> varinfo list ref -> instr list ref -> instr) = 
    cl#mk_instr ast main_fd sid tpl_id idxs xinfo in
  
  let visitor = (new modStmtVisitor) sids (fun i -> mk_instr i) in
  visitCilFileSameGlobals (visitor:> cilVisitor) ast;
  let stat, uks, instrs = visitor#status, visitor#uks, visitor#instrs in 
  if stat = "" then E.s(E.error "stmts [%s] not modified" sids_s);
  
  (*modify main*)
  let main_stmts = mk_main main_fd mainQ_fd tcs uks instrs in
  main_fd.sbody.bstmts <- main_stmts;

  (*add uk's to fun decls and fun calls*)
  let fiv = (new funInstrVisitor) uks in
  visitCilFileSameGlobals (fiv :> cilVisitor) ast;
  visitCilFileSameGlobals ((new instrCallVisitor) uks fiv#ht) ast;

  (*add include "klee/klee.h" to file*)
  ast.globals <- (GText "#include \"klee/klee.h\"") :: ast.globals;
  (* ast.globals <- (GText "extern void __VERIFIER_error();") :: ast.globals; *)
  (* ast.globals <- (GText "extern int __VERIFIER_nondet_int();") :: ast.globals; *)
  (* ast.globals <- (GText "extern void __VERIFIER_assume();") :: ast.globals; *)
  
  let fn = transform_s ast.fileName sids_s xinfo in


  (*the symbol is useful when parsing the result, don't mess up this format*)
  E.log "Transform success: ## '%s' ##  %s\n" fn stat;
  CC.write_src fn ast


(********************** INSTRUMENTATION **********************)

let () = begin
    (* e.g., ./instr --sid 1 --tpl 1 --idxs "3 7 8" --xinfo z2_c5 *)
    E.colorFlag := true;

    let filename = ref "" in
    let inputs   = ref "" in
    let outputs  = ref "" in 
    let version = P.sprintf "%s (%s) %f (CIL version %s)" 
			    ST.progname ST.progname_long ST.progversion cilVersion 
    in 

    let arg_descrs = [
      "--debug", Arg.Set VC.vdebug, 
      P.sprintf " shows debug info (default %b)" !VC.vdebug;
      
      "--sids", Arg.String (fun s-> 
			    let sids' =  L.map int_of_string (VC.str_split s) in
			    if L.exists (fun i -> i < 0) sids' then (
			      raise(Arg.Bad (
					P.sprintf 
					  "arg --sids must contain non-neg ints, [%s]" 
					  (VC.string_of_ints sids'))));
			    ST.sids := sids'), 
      " e.g., --sids \"3 7 8\"";
      
      "--tpl", Arg.Int (fun i -> 
			if i < 0 then raise (Arg.Bad "arg --tpl must be > 0");
			tpl:=i), 
      " e.g., --tpl 3";
      
      "--xinfo", Arg.Set_string xinfo, " e.g., --xinfo z2_c5";
      "--idxs", Arg.String (
		    fun s -> 
		    let idxs' =  L.map int_of_string (VC.str_split s) in
		    if L.exists (fun i -> i < 0) idxs' then (
		      raise(Arg.Bad (
				P.sprintf 
				  "arg --idxs must contain non-neg ints, [%s]" 
				  (VC.string_of_ints idxs'))));
		    idxs := idxs'), 
      " e.g., --idxs \"3 7 8\"";
      
    ] in
    
    let handle_arg s =
      if !filename = "" then (
	VC.chk_exist s ~msg:"require filename"; filename := s
      )
      else if !inputs = "" then inputs := s
      else if !outputs = "" then outputs := s
      else raise (Arg.Bad "too many input args")
    in
    
    let usage = P.sprintf "%s\nusage: ceti src in_file out_file [options]\n" version in

    Arg.parse (Arg.align arg_descrs) handle_arg usage;
    
    initCIL();
    Cil.lineDirectiveStyle := None;
    Cprint.printLn := false; (*don't print line #*)

    (* for Cil to retain &&, ||, ?: instead of transforming them to If stmts *)
    Cil.useLogicalOperators := true; 

    transform !filename !ST.sids !tpl !xinfo !idxs

  end
