open Cil
(*open Cil_common*)
module E = Errormsg
let debug = ref false

(*common*)
module W = Why3
module WT = W.Term
module WTH = W.Theory 
module WN = W.Number
module WE = W.Env
module WC = W.Whyconf
module WD = W.Decl
module WP = W.Pretty

type ops = {
  lt_op     : WT.lsymbol;
  gt_op     : WT.lsymbol;
  lte_op    : WT.lsymbol;
  gte_op    : WT.lsymbol;

  iplus_op  : WT.lsymbol;
  iminus_op : WT.lsymbol;
  itimes_op : WT.lsymbol;

  idiv_op   : WT.lsymbol;
  imod_op   : WT.lsymbol;

  get_op    : WT.lsymbol;
  set_op    : WT.lsymbol;
}


type wctxt = {
  mutable env    : WE.env;
  mutable task   : W.Task.task;
  mutable prover : WC.config_prover;
  mutable driver : W.Driver.driver;
 
  mutable ops    : ops;
  mutable memory : WT.vsymbol;
  mutable vars: (string, WT.vsymbol) Hashtbl.t ;
}


let initOps (it: WTH.theory) (dt: WTH.theory) (mt: WTH.theory): ops = {
  (*integer theory*)
  lt_op    = WTH.ns_find_ls it.WTH.th_export ["infix <"];
  gt_op    = WTH.ns_find_ls it.WTH.th_export ["infix >"];
  lte_op   = WTH.ns_find_ls it.WTH.th_export ["infix <="];
  gte_op   = WTH.ns_find_ls it.WTH.th_export ["infix >="];

  iplus_op = WTH.ns_find_ls it.WTH.th_export ["infix +"];
  iminus_op= WTH.ns_find_ls it.WTH.th_export ["infix -"];
  itimes_op = WTH.ns_find_ls it.WTH.th_export ["infix *"];

  (*division theory*)
  idiv_op  = WTH.ns_find_ls dt.WTH.th_export ["div"];
  imod_op  = WTH.ns_find_ls dt.WTH.th_export ["mod"];

  (*array theory*)
  get_op  = WTH.ns_find_ls mt.WTH.th_export ["get"];
  set_op  = WTH.ns_find_ls mt.WTH.th_export ["set"];
}


let initWhyCtxt (p: string) (pv: string): wctxt = 
  let config = WC.read_config None in
  let main = WC.get_main config in
  WC.load_plugins main;
  let provers = WC.get_provers config in
  WC.Mprover.iter (
    fun  k a ->
      E.warn "%s %s (%s)" k.WC.prover_name k.WC.prover_version k.WC.prover_altern
  )provers;

  let prover_spec = {WC.prover_name=p; 
		     WC.prover_version=pv; 
		     WC.prover_altern=""} in
  let prover = 
    try WC.Mprover.find prover_spec provers
    with Not_found -> E.s(E.error "Prover %s not found" p) in

  let env = WE.create_env (WC.loadpath main) in
  let driver: W.Driver.driver = 
    try W.Driver.load_driver env prover.WC.driver []
    with _ -> E.s (E.error "Failed to load driver for %s" p) in

  let int_theory = WE.find_theory env ["int"] "Int" in
  let div_theory = WE.find_theory env ["int"] "ComputerDivision" in
  let arr_theory = WE.find_theory env ["map"] "Map" in 
  let task = List.fold_left W.Task.use_export None 
    [int_theory; div_theory; arr_theory] in
  let arr_ts = WTH.ns_find_ts arr_theory.WTH.th_export ["map"] in 
  let int_arr_t = W.Ty.ty_app arr_ts [W.Ty.ty_int; W.Ty.ty_int] in

  {env=env; task = task; prover = prover; driver = driver;
   ops = initOps int_theory div_theory arr_theory;
   memory = WT.create_vsymbol (W.Ident.id_fresh "M") int_arr_t;
   vars = Hashtbl.create 64}
    
    
let invAttrStr = "invariant" 
and postAttrStr = "post"
and preAttrStr = "pre"


let make_symbol(s: string): WT.vsymbol = 
  WT.create_vsymbol (W.Ident.id_fresh s) W.Ty.ty_int

let freshvar_of_ap(ap: attrparam): string * WT.vsymbol =
  match ap with 
  |ACons(n, []) -> n, make_symbol n
  |_ -> E.s(E.error "Names only")

let oldvar_of_ap wc (ap: attrparam): WT.vsymbol = 
  match ap with
  |ACons(n, []) -> Hashtbl.find wc.vars n
  |_ -> E.s(E.error "Names only")


let term_of_int(i: int) : WT.term = 
  WT.t_const (WN.ConstInt (WN.int_const_dec (string_of_int i)))

let term_of_i64(i: int64): WT.term = 
  WT.t_const (WN.ConstInt (WN.int_const_dec (Int64.to_string i)))


let rec term_of_attrparam wc (ap: attrparam): WT.term = 
  match ap with
  |AInt i                 -> term_of_int i
  |ACons(n,[])            -> WT.t_var (Hashtbl.find wc.vars n)
  |ACons("forall",apl)    -> term_of_forall wc apl
  |ACons("implies",[h;c]) -> term_of_implies wc h c
  |AUnOp(uo, ap)          -> term_of_apuop wc uo ap
  |ABinOp(bo, ap1, ap2)   -> term_of_apbop wc bo ap1 ap2
  |AStar ap               -> term_of_star wc ap
  |AIndex(base, index)    -> term_of_index wc base index    

  |AStr _ -> E.s(E.unimp "AStr -> Term")
  |ASizeOf _
  |ASizeOfE _
  |ASizeOfS _
  |AAlignOf _
  |AAlignOfE _
  |AAlignOfS _  -> E.s(E.unimp "A{Size,Align}Of* -> Term")
  |ADot(ap, s) -> E.s(E.unimp "ADot -> Term")
  |AAddrOf ap -> E.s(E.unimp "AAddrOf -> Term")
  |AQuestion(ap1, ap2, ap3) -> E.s(E.unimp "AQuestion -> Term")

  |_ -> E.s(E.error "Attrparam is not a term: %a" d_attrparam ap)


and term_of_forall wc (apl: attrparam list): WT.term = 
  let fat = List.hd (List.rev apl)
  and vl = List.map freshvar_of_ap (List.tl (List.rev apl)) 
  and oldm = Hashtbl.copy wc.vars 
  in
  List.iter (fun (n,v) -> Hashtbl.add wc.vars n v) vl;
  let t = term_of_attrparam wc fat in

  wc.vars <- oldm;
  WT.t_forall_close (List.map snd vl) [] t

and term_of_implies wc (h: attrparam) (c: attrparam): WT.term =
  WT.t_implies (term_of_attrparam wc h) (term_of_attrparam wc c)
  
and term_of_apuop wc (u: unop) (ap: attrparam): WT.term = 
  let te = term_of_attrparam wc ap in 
  match u with 
  |Neg -> WT.t_app_infer wc.ops.iminus_op [(term_of_int 0); te]
  |LNot -> WT.t_not te 
  |BNot -> E.s(E.unimp "Attribute BNot: ~%a\n" d_attrparam ap)

and term_of_apbop
    wc (b: binop) (ap1: attrparam) (ap2: attrparam): WT.term =
  let te1 = term_of_attrparam wc ap1 
  and te2 = term_of_attrparam wc ap2 in

  match b with 
  |PlusA  |PlusPI  |IndexPI -> WT.t_app_infer wc.ops.iplus_op [te1; te2]
  |MinusA |MinusPI |MinusPP -> WT.t_app_infer wc.ops.iminus_op [te1; te2]
  |Mult -> WT.t_app_infer wc.ops.itimes_op [te1; te2]
  |Div  -> WT.t_app_infer wc.ops.idiv_op   [te1; te2]
  |Mod  -> WT.t_app_infer wc.ops.imod_op   [te1; te2]
  |Lt   -> WT.t_app_infer wc.ops.lt_op  [te1; te2]
  |Gt   -> WT.t_app_infer wc.ops.gt_op  [te1; te2]
  |Le   -> WT.t_app_infer wc.ops.lte_op [te1; te2]
  |Ge   -> WT.t_app_infer wc.ops.gte_op [te1; te2]
  |Eq   -> WT.t_equ te1 te2
  |Ne   -> WT.t_neq te1 te2
  |LAnd -> WT.t_and te1 te2
  |LOr  -> WT.t_or  te1 te2
  |_ -> E.s (E.error "term_of_bop failed: %a %a %a\n"
               d_attrparam ap1 d_binop b d_attrparam ap2)

and term_of_star wc (a: attrparam): WT.term = 
  WT.t_app_infer wc.ops.get_op [WT.t_var wc.memory; term_of_attrparam wc a]

and term_of_index wc (base: attrparam) (index: attrparam): WT.term = 
  let addr = WT.t_app_infer wc.ops.iplus_op 
    [term_of_attrparam wc base; term_of_attrparam wc index]
  and mt = WT.t_var wc.memory in
  WT.t_app_infer wc.ops.get_op [mt; addr]
     

let rec term_of_exp  wc (e: exp): WT.term =
  match e with
  |Const(CInt64(i,_,_)) -> term_of_i64 i
  |Lval(Var vi, NoOffset) -> WT.t_var (Hashtbl.find wc.vars vi.vname)
  |Lval(Mem e, NoOffset) -> 
    WT.t_app_infer wc.ops.get_op [WT.t_var wc.memory; term_of_exp wc e]
  | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ ->
    term_of_exp wc (constFold true e)
  |UnOp(uo, e, typ) -> term_of_uop wc uo e
  |BinOp(bo, e1, e2, typ) -> term_of_bop wc bo e1 e2
  |CastE(t, e) -> term_of_exp wc e
  | AddrOf _ | StartOf _ |_ -> E.s(E.error "term_of_exp failed: %a" d_exp e)
  
and term_of_uop wc(u: unop)(e: exp): WT.term = 
  let te = term_of_exp wc e in 
  match u with 
  |Neg -> WT.t_app_infer wc.ops.iminus_op [(term_of_int 0); te]
  |LNot -> WT.t_not te 
  |BNot -> E.s (E.error "term_of_uop failed: ~%a\n" d_exp e)

and term_of_bop wc(b: binop)(e1: exp)(e2: exp): WT.term = 

  let te1 = term_of_exp wc e1 in
  let te2 = term_of_exp wc e2 in
  match b with
  | PlusA  | PlusPI  | IndexPI -> WT.t_app_infer wc.ops.iplus_op  [te1; te2]
  | MinusA | MinusPI | MinusPP -> WT.t_app_infer wc.ops.iminus_op [te1; te2]
  | Mult -> WT.t_app_infer wc.ops.itimes_op [te1; te2]
  | Div  -> WT.t_app_infer wc.ops.idiv_op   [te1; te2]
  | Mod  -> WT.t_app_infer wc.ops.imod_op   [te1; te2]
  | Lt   -> WT.t_app_infer wc.ops.lt_op  [te1; te2]
  | Gt   -> WT.t_app_infer wc.ops.gt_op  [te1; te2]
  | Le   -> WT.t_app_infer wc.ops.lte_op [te1; te2]
  | Ge   -> WT.t_app_infer wc.ops.gte_op [te1; te2]
  | Eq   -> WT.t_equ te1 te2
  | Ne   -> WT.t_neq te1 te2
  | LAnd -> WT.t_and te1 te2
  | LOr  -> WT.t_or  te1 te2
  | _ -> E.s (E.error "term_of_bop failed: %a %a %a\n"
              d_exp e1 d_binop b d_exp e2)


let guard_block_of_loop (b:block): exp option* stmt list= 
  let rec skipEmpty = function 
    |[]-> []
    |{skind = Instr []; labels = []} :: rest -> skipEmpty rest
    |x -> x
  in
  let (guard:exp option),(body:stmt list) = 
    match skipEmpty b.bstmts with
    (*Match the first stmt after skipping all empty stmts*)
    |{skind = If(e,tb,fb,_); labels =[]}::rest -> 
      begin      
	match skipEmpty tb.bstmts, skipEmpty fb.bstmts with
	|[], {skind = Break _; labels = []}:: _ -> Some(e), rest
	|{skind = Break _; labels = []}:: _, [] -> Some(UnOp(LNot, e, intType)), rest
	|_ -> None,rest
      end
    |_ -> None,b.bstmts
  in
  guard,body


(*Generate VC's*)

let rec term_of_stmt wc s q: WT.term =
  match s.skind with
  |Instr il -> List.fold_right (term_of_instr wc) il q
  |If(c,tb,fb,_) -> term_of_if wc c tb fb q
  |Loop(b,_,_,_) -> term_of_loop wc b q
  |Block b -> term_of_block wc b q
  |Return(_,_) -> q
  |_ -> E.s(E.error "No support for try-finally, or try-except")

and term_of_if wc c tb fb q: WT.term = 
  let tc = term_of_exp wc c in
  Format.printf "@[tc: @ %a@]@." WP.print_term tc;
  let ttb = term_of_block wc tb q in
  let tfb = term_of_block wc fb q in 
  WT.t_if tc ttb tfb

and term_of_loop wc b q: WT.term = 
  let guard,(body:stmt list) = guard_block_of_loop b in

  let body_block = 
    let s = (List.hd body) in 
    match s.skind with
    |Block b -> b
    |_ -> E.s(E.bug "Expected block (inv)")
  in

  let li, lvl = 
    match filterAttributes invAttrStr body_block.battrs with
    |[Attr(_,li::rst)]-> term_of_attrparam wc li,List.map (oldvar_of_ap wc) rst
    |_ -> E.s(E.error "malformed inv attrib: %a" d_attrlist body_block.battrs)
  in

  let tb = term_of_block wc (mkBlock (body_block.bstmts @ (List.tl body))) li in 
  Format.printf "@[loop: tb is\n@ %a@]@." W.Pretty.print_term tb;

  let lvl' = wc.memory::lvl in
  List.iter ( fun v ->  Format.printf "@[@ %a@]@." WP.print_vs v;) lvl;

  let t = match guard with
    |Some(e) -> WT.t_if (term_of_exp wc e) tb q
    |None -> tb
  in
  let t' = WT.t_forall_close lvl' []  (WT.t_implies li t) in
  WT.t_and li t'


and term_of_instr wc i q: WT.term =
  match i with
  |Set((Var vi, _), e, _)  ->
    let vt:WT.vsymbol = Hashtbl.find wc.vars vi.vname in
    WT.t_let_close vt (term_of_exp wc e) q

  |Set((Mem me, _), e, _) ->
    let ume = WT.t_app_infer wc.ops.set_op 
      [WT.t_var wc.memory; term_of_exp wc me; term_of_exp wc e] in
    WT.t_let_close wc.memory ume q

  | _ -> E.s (E.error "term_of_inst: We can only handle assignment")

and term_of_block wc b q: WT.term =
  List.fold_right (term_of_stmt wc) b.bstmts q


let validateWhyCtxt wc (toprove: WT.term): unit = 
  Format.printf "@[validating: @ %a@]@." W.Pretty.print_term toprove;
  let goal = WD.create_prsymbol (W.Ident.id_fresh "goal") in
  let task = W.Task.add_prop_decl wc.task WD.Pgoal goal toprove in
  let res = 
    let cmd = (W.Driver.prove_task 
		 ~command:wc.prover.WC.command 
		 ~timelimit:120 wc.driver task ()) in
    W.Call_provers.wait_on_call cmd ()
  in
  Format.printf "@[Prover answers:@ %a@]@.@[%s@]@."
    W.Call_provers.print_prover_result res res.W.Call_provers.pr_output;
  ()


let vcgen wc (fd: fundec) (precond: WT.term option) (postcond: WT.term): WT.term = 
  let tb:WT.term = term_of_block wc fd.sbody postcond in

  let vc:WT.term = 
    match precond with
    |None -> tb
    |Some precond' -> WT.t_implies precond' tb
  in

  let vl =   (*vsymbols of function*)
    let sl  = (List.map (fun vi -> vi.vname) fd.sformals) in
    let vl:WT.vsymbol list  = List.map (fun s -> Hashtbl.find wc.vars s) sl in
    List.append [wc.memory] vl
  in

  WT.t_forall_close vl [] vc



let rec wp_of_stmt wc s q l: (WT.term * WT.term list) = 
  match s.skind with
  |Instr il -> 
    List.fold_right (fun i (q',l') -> wp_of_instr wc i q' l') il (q,l)
  |If(c,tb,fb,_) -> wp_of_if wc c tb fb q l
  |Loop(b,_,_,_) -> wp_of_loop wc b q l
  |Block b -> wp_of_block wc b q l
  |Return(_,_) -> q,l
  |_ -> E.s(E.error "No support for try-finally, or try-except")


and wp_of_block wc b q l: (WT.term * WT.term list) = 
  List.fold_right (fun s (q',l') -> wp_of_stmt wc s q' l') b.bstmts (q,l)

and wp_of_instr wc i q l: (WT.term * WT.term list) = 
  match i with
  |Set((Var vi, _), e, _)  ->
    let vt:WT.vsymbol = Hashtbl.find wc.vars vi.vname in
    (WT.t_let_close vt (term_of_exp wc e) q), l

  |Set((Mem me, _), e, _) ->
    let ume = WT.t_app_infer wc.ops.set_op 
      [WT.t_var wc.memory; term_of_exp wc me; term_of_exp wc e] in
    (WT.t_let_close wc.memory ume q), l

  | _ -> E.s (E.error "term_of_inst: We can only handle assignment")


and wp_of_if wc c tb fb q l: (WT.term * WT.term list) = 
  let q1,l1 = wp_of_block wc tb q l in 
  let q2,l2 = wp_of_block wc fb q l in 
  let t = term_of_exp wc c in
  WT.t_if t q1 q2, l1@l2
    

and wp_of_loop wc b q l: (WT.term * WT.term list) = 
  let guard,(body:stmt list) = guard_block_of_loop b in

  let body_block = 
    let s = (List.hd body) in 
    match s.skind with
    |Block b -> b
    |_ -> E.s(E.bug "Expected block (inv)")
  in

  let li, lvl = 
    match filterAttributes invAttrStr body_block.battrs with
    |[Attr(_,li::rst)]-> term_of_attrparam wc li,List.map (oldvar_of_ap wc) rst
    |_ -> E.s(E.error "malformed inv attrib: %a" d_attrlist body_block.battrs)
  in
  let lvl' = wc.memory::lvl in  

  let b = mkBlock (body_block.bstmts @ (List.tl body)) in
  let q',l' = wp_of_block wc b li l in 

  let l'':WT.term list = 
    let mkNeg e = UnOp(LNot,e,intType) in
    match guard with
    |Some(e) -> 

      let l1 = WT.t_implies li (WT.t_implies (term_of_exp wc e) q') in
      let l2 = WT.t_implies li (WT.t_implies (term_of_exp wc (mkNeg e)) q) in
      [l1;l2]

    |None -> [WT.t_implies li q']
      
  in

  let l''':WT.term list = List.map (WT.t_forall_close lvl' []) l'' in
  li,l'@l'''


let vcgen' wc (fd: fundec) (p: WT.term option) (q: WT.term): WT.term list =
    
  let q',l = wp_of_block wc fd.sbody q [] in
  let vcl = 
    match p with
    |None -> q'::l (*T->q' = q'*)
    |Some p' -> [WT.t_implies p' q']@l
  in

  let vl =   (*vsymbols of function*)
    let sl  = (List.map (fun vi -> vi.vname) fd.sformals) in
    let vl:WT.vsymbol list  = List.map (fun s -> Hashtbl.find wc.vars s) sl in
    List.append [wc.memory] vl
  in

  List.map (WT.t_forall_close vl []) vcl 
      

let processFun  wc (fd: fundec) (loc: location): unit = 
  E.log "processing fun %s\n" fd.svar.vname ;

  List.iter (fun vi ->     
    Hashtbl.add wc.vars vi.vname (make_symbol vi.vname)) 
    (fd.slocals @ fd.sformals);
  
  Hashtbl.iter (
    fun k v ->  
      Format.printf "@[%s -> @ %a@]@." k WP.print_vs v;
  ) wc.vars;
    

  (*extract condition from function to term*)
  let cond_of_fun wc (attr_name: string) (fd: fundec): WT.term option =
    match filterAttributes attr_name (typeAttrs fd.svar.vtype) with
    |[Attr(_,[ap])] -> 
      let t = term_of_attrparam wc ap in
      Some(t)
    |_ -> None
  in
  
  match cond_of_fun wc postAttrStr fd with
  |None -> ()
  |Some postcond -> 
    let precond = cond_of_fun wc preAttrStr fd in 
    let vcl = vcgen' wc fd precond postcond in
    E.log "Generate %d vc's\n" (List.length vcl);
    List.iter (validateWhyCtxt wc) vcl;

    E.log "Old result\n" ;
    let vc = vcgen wc fd precond postcond in 
    validateWhyCtxt wc vc;

      



class attrEraserVisitor = object(self)
  inherit nopCilVisitor
  method vattr (a: attribute) = 
    match a with 
    |Attr(s,_) when List.mem s [invAttrStr; postAttrStr; preAttrStr] 
	-> ChangeTo []
    |_ -> DoChildren
end


let main () : unit =
  let filename = ref "" in
  let storeFilename s =
    if !filename = "" then filename := s
    else raise (Arg.Bad "unexpected multiple input files")
  in
  Arg.parse [] storeFilename "vcgen <filename>";

  initCIL ();
  let source = Frontc.parse !filename () in
  let wc = initWhyCtxt "Alt-Ergo" "0.95.2" in
  (*let wc = initWhyCtxt "Yices" "1.0.34" in*)
  (*let wc = initWhyCtxt "Z3" "4.3.2" in*)

  iterGlobals source (
    function g -> 
      match g with 
      |GFun(f, loc) -> processFun wc f loc (*only functions*)
      |_ -> ()
  );

  visitCilFile (new attrEraserVisitor) source (*erase attrs*)
  (*write_src "vu_tmp.c" source*)
    
let () = main ()
