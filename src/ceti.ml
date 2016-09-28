(*ocamlfind ocamlopt -package str,batteries,cil  cil_common.cmx -linkpkg -thread tf.ml*)
(*Takes in a preprocess file , e.g., cil.i 
for i in {1..41}; do cilly bug$i.c --save-temps --noPrintLn --useLogicalOperators; done
 *)

(*open Ceti_common*)
open Cil
module E = Errormsg
module L = List
module A = Array
module H = Hashtbl 
module P = Printf
module FL = Fl

module CC = Cil_common
module VC = Vu_common

(* let forceOption (ao : 'a option) : 'a = *)
(*   match ao with  | Some a -> a | None -> raise(Failure "forceOption") *)

(*filename formats*)
let ginfo_s = P.sprintf "%s.info" (*f.c.info*)
let arr_s = P.sprintf "%s.s%d.t%d.arr" (*f.c.s1.t3.arr*)
let transform_s = P.sprintf "%s.s%s.%s.ceti.c" (*f.c.s5.z3_c2.ceti.c*)

type spy_t = CC.sid_t list*int*int*int list (*sid,cid,level,idxs*)

let string_of_spys ((sids,cid,level,idxs):spy_t): string = 
  let sid' = (String.concat " " (L.map string_of_int sids)) in
  let idxs' = (String.concat " " (L.map string_of_int idxs)) in
  P.sprintf "(%s, %d, %d, %s)" sid' cid level idxs'

let group_sids (sids:CC.sid_t list) (l:spy_t list): spy_t list = 

  let l0,l1 = L.partition (fun (sids',_,_,_) -> 
			   assert (L.length sids' = 1);
			   L.mem (L.hd sids') sids) l 
  in

  let l1 = L.map (fun (sids,t,l,i) -> (sids,t,l,i)) l1 in
  if L.length l0 = 0 then
    l1
  else
    let _,t,l,i = L.hd l0 in
    let sids':CC.sid_t list list = L.map (fun (s,_,_,_) -> s) l0 in 
    [(L.flatten sids',t,l,i)]@l1

(* specific options for this program *)

let progname:string = "CETI"
let progname_long:string = "Correcting Errors using Test Inputs"
let progversion:float = 0.1
let mainfunname:string = "mainQ"
let synvarname:string = "ceti_q"

let dlog s = if !VC.vdebug then E.log "%s" s else ()
let dalert s = if !VC.vdebug then CC.ealert "%s" s else ()

let fl_sids = ref [] (*manually provide fault loc info*)

let no_global_vars = ref false
let no_parallel = ref false
let no_bugfix = ref false
let no_stop = ref false

let only_transform = ref false
let only_synthesis = ref false
let sids = ref [] (*only do transformation on vs_idxs*)
let tpl = ref 0
let idxs = ref []
let xinfo = ref "" (*helpful info for debugging*)

let only_spy = ref false
let only_peek = ref false (*for debugging only, peeking at specific stmt*)

let python_script = "kl.py" (*name of the python script, must be in same dir*)

let uk_iconst_min:exp = integer (-100000)
let uk_iconst_max:exp = integer 100000
let uk_fconst_min:exp = Const(CReal(-100000.,FFloat,None))
let uk_fconst_max:exp = Const(CReal(100000.,FFloat,None))
let uk_dconst_min:exp = Const(CReal(-100000.,FDouble,None))
let uk_dconst_max:exp = Const(CReal(100000.,FDouble,None))

(* coeffs, e.g., c1*v1 + ... + cnvn*)
let uk_imin:exp = mone (* -1 *) 
let uk_imax:exp =  one

let tpl_ids:int list ref = ref [] (*apply only these specific template ids*)
let tpl_level:int ref = ref 4 (*apply only templates with <= levels*)
let extra_vars:varinfo list ref = ref []

(*
  Supported arithmetic type.  
  Note Cil's isArithmeticType consists of other non-supported (yet) types
 *)
let isMArithType = function
  |TInt _ -> true
  |TFloat(FFloat,_) -> true
  |TFloat(FDouble,_) -> true

  | _ -> false
(******************* Helper Functions *******************)

let find_fun (ast:file) (funname:string) : fundec = 
  let fd = ref None in
  iterGlobals ast (function 
		    |GFun(f,_) when f.svar.vname = funname -> fd := Some f
		    |_ -> ()
		  );
  match !fd with
  |Some f -> f
  |None -> E.s(E.error "fun '%s' not in '%s'!" funname ast.fileName)


(*apply binary op to a list of exps, e.g, + [v1,..,vn] =>  v1 + .. + vn*)
let apply_binop (op:binop) (exps:exp list): exp = 
  assert (L.length exps > 0);
  let e0 = L.hd exps in 
  let ty = typeOf e0 in
  L.fold_left (fun e e' -> BinOp(op,e,e',ty)) e0 (L.tl exps)

(*
  apply a list of ops, e.g., 
  apply_bops x y + * [v1;v2] [<; =; >] gives
  (v1 * (e1 < e2)) + (v2* (e1 = e2)) + (v3 * (e1 > e2))
 *)
let apply_bops 
      ?(o1:binop=PlusA) ?(o2:binop=Mult) 
      (e1:exp) (e2:exp) 
      (uks:exp list) (ops:binop list) :exp =

  assert (L.length uks > 0);
  assert (L.length uks = L.length ops);
  let ty = typeOf e1 in
  (*E.log "ty of %s is %s\n" (string_of_exp e1) (string_of_typ ty);*)
  assert (L.for_all (fun x -> 
		     (*E.log "ty of %s is %s" (string_of_exp x) (string_of_typ (typeOf x));*)
		     typeOf x = ty) (e2::uks));

  let uk0, uks = L.hd uks, L.tl uks in
  let op0, ops = L.hd ops, L.tl ops in 

  let a = BinOp(o2,uk0,BinOp(op0,e1,e2,ty),ty) in
  let tE = typeOf a in
  L.fold_left2 (fun a op uk ->
		BinOp(o1,a,BinOp(o2, uk, BinOp (op,e1,e2,ty), ty),tE)
	       ) a ops uks


(******************* Helper Visistors *******************)
(*Find variables of type bool, so that we don't do int var*/+ bool var 
  during instrumentation 
  TODO:  I am still confused if I should use DoChildren or SkipChildren
 *)

class findBoolVars (bvs:varinfo list ref) = object
  inherit nopCilVisitor

  method vstmt (s:stmt) = 
    match s.skind with 
    |If(Lval(Var vi,_),_,_,_) -> bvs := vi::!bvs; DoChildren  
    |_->DoChildren

end

let find_boolvs fd = 
  let bvs:varinfo list ref = ref [] in
  ignore (visitCilFunction ((new findBoolVars) bvs) fd);
  L.rev !bvs

(*Find statements of the form 
  ceti_q = dummyVal; 
 *)
class findSynStmts (sids:CC.sid_t list ref) = object
  inherit nopCilVisitor
  method vstmt (s:stmt) = 
    match s.skind with 
    |Instr[Set((Var vi,_),Const _,_)] when VC.in_str synvarname vi.vname ->
      sids := s.sid::!sids; 
      DoChildren  
    |_->DoChildren
end

let find_synstmts ast = 
  let sids:CC.sid_t list ref = ref [] in
  ignore (visitCilFileSameGlobals ((new findSynStmts) sids) ast);
  L.rev !sids


(******************* For debugging a Cil construct *******************)

let rec peek_exp e: string = 
  match e with 
  |Const _ -> "Cconst"
  |Lval lv -> CC.string_of_lv lv
  |SizeOf _ -> "SizeOf"
  |SizeOfE _ -> "SizeOfE"
  |SizeOfStr _ -> "SizeOfStr"    
  |AlignOf _ -> "AlignOf"
  |AlignOfE _ -> "AlignOfE"
  |UnOp (uop,e',_) -> P.sprintf "%s (%s)" (CC.string_of_unop uop) (peek_exp e)
  |BinOp (bop,e1,e2,_) -> 
    P.sprintf "%s %s %s" (peek_exp e1) (CC.string_of_binop bop) (peek_exp e2)
  |Question _ -> "Question"
  |CastE _ -> "CastE"
  |AddrOf _-> "AddrOf"
  |AddrOfLabel _-> "AddrOfLabel"
  |StartOf _ -> "StartOf"
		  
and peek_instr ins: string = 
  match ins with 
  |Set(lv,e,_) -> P.sprintf "%s = %s" (CC.string_of_lv lv) (peek_exp e)
  |Call _ -> "Call"
  |_ -> "(unimp instr: "  ^ CC.string_of_instr ins ^ ")"
						       
class peekVisitor sids = object(self)
  inherit nopCilVisitor
  method vstmt s = 
    if L.mem s.sid sids then (
      CC.ealert "Peek: sid %d\n%a" s.sid dn_stmt s;
      match s.skind with 
      |Instr ins -> 
	let rs = L.map peek_instr ins in 
	E.log "%s\n" (String.concat "\n" rs);
      |_ -> E.unimp "stmt : %a" dn_stmt s
    );
    DoChildren
end

			   
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

(* make unknown variables and their assumptions*)
let mk_uk 
      (uid:int) (uty:typ)
      (min_v:exp) (max_v:exp)
      (main_fd:fundec) 
      (vs:varinfo list ref)
      (instrs:instr list ref) 
    :varinfo =
  
  let vname = ("uk_" ^ string_of_int uid) in 
  
  (*declare uks*)
  let vi:varinfo = makeLocalVar main_fd vname uty in
  let lv:lval = var vi in 
  
  (*klee_make_symbolic(&uk,sizeof(uk),"uk") *)
  (* let mk_sym_instr:instr = *)
  (*   CC.mk_call "klee_make_symbolic"  *)
  (* 	       [mkAddrOf(lv); SizeOfE(Lval lv); Const (CStr vname)] in *)

  let mk_sym_instr:instr =
    CC.mk_call ~av:(Some lv) "__VERIFIER_nondet_int" [] in
  
  (* "klee_assume" *)
  let klee_assert_lb:instr = CC.mk_call "__VERIFIER_assume"
					[BinOp(Le,min_v,Lval lv, CC.boolTyp)] in 
  
  let klee_assert_ub:instr = CC.mk_call "__VERIFIER_assume"
					[BinOp(Le,Lval lv, max_v, CC.boolTyp)] in 
  
  vs := !vs@[vi];
  instrs := !instrs@[mk_sym_instr;  klee_assert_lb; klee_assert_ub];

  vi 

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
  (*let klee_assert_zero:instr = CC.mk_call "klee_assert" [zero] in *)
  let klee_assert_zero:instr = CC.mk_call "__VERIFIER_error" [] in 
  
  
  let and_exps = apply_binop LAnd exps in
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
  

class virtual bugfixTemplate (cname:string) (cid:int) (level:int) = object

	  val cname = cname
	  val cid = cid
	  val level = level

	  method cname : string = cname
	  method cid   : int = cid
	  method level : int = level

	  method virtual spy_stmt : string -> CC.sid_t -> fundec -> (instr -> spy_t option)
	  method virtual mk_instr : file -> fundec -> int -> int -> int list -> string -> 
				    (instr -> varinfo list ref -> instr list ref -> instr)
	end 


(*Const Template:
  replace all consts found in an exp to a parameter*)

class bugfixTemplate_CONSTS cname cid level = object(self)
						      
  inherit bugfixTemplate cname cid level as super

  (*returns n, the number of consts found in exp
    This produces 1 template stmt with n params
   *)
  method spy_stmt (filename_unused:string) (sid:CC.sid_t) (fd:fundec)
	 : (instr -> spy_t option) = function
    |Set(_,e,_) ->
      let rec find_consts ctr e: int = match e with
	|Const(CInt64 _) -> succ ctr
	|Const(CReal _) -> succ ctr
	|Lval _ -> ctr
	|CastE (_,e1) -> find_consts ctr e1
	|UnOp(_,e1,_) -> find_consts ctr e1
	|BinOp (_,e1,e2,_) -> find_consts ctr e1 + find_consts ctr e2

	| _ -> 
	   CC.ealert "%s: don't know how to deal with exp '%a' (sid %d)" 
		     super#cname dn_exp e sid;
    	   ctr
      in
      let n_consts:int = find_consts 0 e in
      
      if !VC.vdebug then E.log "%s: found %d consts\n" super#cname n_consts;

      if n_consts > 0 then Some([sid],super#cid,super#level,[n_consts])
      else None
	     
    |_ -> None


  (*idxs e.g., [3] means 3 consts found in the susp stmt*)
  method mk_instr (ast:file) (main_fd:fundec) (sid_unused:int)  
		  (tpl_id_unused:int) (idxs:int list) (xinfo:string) 
	 : (instr -> varinfo list ref -> instr list ref -> instr) = 

    assert (L.length idxs = 1);
    let n_consts = L.hd idxs in
    E.log "** %s: xinfo %s, consts %d\n" super#cname xinfo n_consts;

    fun a_i uks instrs -> (
      let mk_exp (e:exp): exp = 
	let new_uk uid uty min_v max_v= 
	  mk_uk uid uty min_v max_v main_fd uks instrs 
	in
	let ctr = ref (L.length !uks) in
	
	let rec find_consts e = match e with
	  |Const(CInt64 _) -> 
	    let vi = new_uk !ctr (typeOf e) uk_iconst_min uk_iconst_max 
	    in incr ctr; CC.exp_of_vi vi
	  |Const(CReal (_,FFloat,_)) -> 
	    let vi = new_uk !ctr (typeOf e) uk_fconst_min uk_fconst_max 
	    in incr ctr; CC.exp_of_vi vi
	  |Const(CReal (_,FDouble,_)) -> 
	    let vi = new_uk !ctr (typeOf e) uk_dconst_min uk_dconst_max 
	    in incr ctr; CC.exp_of_vi vi

	  |Lval _ -> e
	  |CastE (ty,e1) -> CastE (ty,find_consts e1)
	  |UnOp (uop,e1,ty) -> UnOp(uop,find_consts e1,ty)
	  |BinOp (bop,e1,e2,ty) -> BinOp(bop,find_consts e1, find_consts e2, ty)

	  | _ -> 
	     CC.ealert "%s: don't know how to deal with exp '%a'" 
		       super#cname dn_exp e;
	     e
	in
	let r_exp = find_consts e in

	r_exp
      in
      
      match a_i with
      |Set(v,e,l) -> Set(v, mk_exp e, l)
      |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)
    )
end

let logic_bops = [|LAnd; LOr|] 
let comp_bops =  [|Lt; Gt; Le; Ge; Eq; Ne|]
let arith_bops = [|PlusA; MinusA|]

(*Template for creating parameterized ops*)
class bugfixTemplate_OPS_PR cname cid level = object(self)
  inherit bugfixTemplate cname cid level as super 
  val ops_ht:(binop, binop list) H.t = H.create 128

  initializer
  let ops_ls = [A.to_list logic_bops; A.to_list comp_bops; A.to_list arith_bops] in
      L.iter(fun bl -> L.iter (fun b -> H.add ops_ht b bl) bl) ops_ls;

      if !VC.vdebug then 
	E.log "%s: create bops ht (len %d)\n" super#cname (H.length ops_ht)
							  
  (*returns n, the number of supported ops in an expression
    This produces n template stmts
   *)
  method spy_stmt (filename_unused:string) (sid:CC.sid_t) (fd:fundec)
	 : (instr -> spy_t option) = function
    |Set(_,e,_) ->
      let rec find_ops ctr e: int = match e with
	|Const _ -> ctr
	|Lval _ -> ctr
	|UnOp(_,e1,_) -> find_ops ctr e1
	|CastE(_,e1) -> find_ops ctr e1
	|BinOp (bop,e1,e2,_) -> 
	  (if H.mem ops_ht bop then 1 else 0) + 
	    find_ops ctr e1 + find_ops ctr e2 

	| _ -> 
	   CC.ealert "%s: don't know how to deal with exp '%a' (sid %d)" 
		     super#cname dn_exp e sid;
    	   ctr
      in
      let n_ops:int = find_ops 0 e in
      
      if !VC.vdebug then E.log "%s: found %d ops\n" super#cname n_ops;

      if n_ops > 0 then Some([sid],super#cid,super#level,[n_ops])
      else None
	     
    |_ -> None

  (*idxs e.g., [3] means do the 3rd ops found in the susp stmt*)
  method mk_instr (ast:file) (main_fd:fundec) (sid:int)  
		  (tpl_id_unused:int) (idxs:int list) (xinfo:string) 
	 :(instr -> varinfo list ref -> instr list ref -> instr) = 

    assert (L.length idxs = 1);
    let nth_op:int = L.hd idxs in
    assert (nth_op > 0);
    E.log "** %s: xinfo %s, nth_op %d\n" super#cname xinfo nth_op;

    fun a_i uks instrs -> (
      let mk_exp (e:exp): exp = 
	let new_uk uid = mk_uk uid intType zero one main_fd uks instrs in

	let ctr = ref 0 in
	let rec find_ops e = match e with
	  |Const _ -> e
	  |Lval _ -> e
	  |CastE(ty,e1) -> CastE(ty,find_ops e1)
	  |UnOp (uop,e1,ty) -> UnOp(uop,find_ops e1,ty)
	  |BinOp (bop,e1,e2,ty) -> 
	    if H.mem ops_ht bop then (
	      incr ctr;
	      if !ctr = nth_op then (
		let bops = L.filter (fun op -> op <> bop) (H.find ops_ht bop) in
		assert (L.length bops > 0);
		if L.length bops = 1 then
		  BinOp(L.hd bops, e1,e2,ty)
		else(
		  let uks = L.map new_uk (VC.range (L.length bops)) in 
		  let uks = L.map CC.exp_of_vi uks in 
		  
		  let xor_exp = apply_binop BXor uks in		  
		  (*let klee_assert_xor:instr = CC.mk_call "klee_assume" [xor_exp] in*)
		  let klee_assert_xor:instr = CC.mk_call "__VERIFIER_assume" [xor_exp] in
		  instrs := !instrs@[klee_assert_xor];
		  
		  apply_bops e1 e2 uks bops
		)
	      )
	      else
		BinOp(bop,find_ops e1, find_ops e2,ty)
	    )
	    else
	      BinOp(bop,find_ops e1, find_ops e2,ty)

	  | _ -> 
	     CC.ealert "%s: don't know how to deal with exp '%a'" 
		       super#cname dn_exp e;
	     e
	in
	let r_exp = find_ops e in	
	r_exp
      in

      
      match a_i with
      |Set(v,e,l) -> Set(v, mk_exp e, l)
      |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)
    )

end


(*Brute force way to generate template stmts (no params)*)
class bugfixTemplate_OPS_BF cname cid level = object(self)
  inherit bugfixTemplate cname cid level as super

  (*sid cid level idxs, where, e.g., idxs = [3, 5, 7] means, 
    replace the first op with classOf(op)[3],
    the second op with classOf(op)[5],
    the third op with classOf(op)[7]*)

  val ops_ht:(binop, binop array) H.t = H.create 128
  initializer
  let ops = 
    match super#cname with 
    |"OPS_LOGIC_B" -> logic_bops
    |"OPS_COMP_B" -> comp_bops
    |_ -> E.s(E.error "incorrect ops name: %s" super#cname)
      in

      (*  H = {
      LAnd: logic_bops,  
      LOr: logic_bops,
      Lt: comp_bops,
      Gt: comp_bops, ..
      }  *)
      A.iter (fun b -> H.add ops_ht b ops) ops;

      (* L.iter(fun bl -> A.iter (fun b -> H.add ops_ht b bl) bl) *)
      (*     [(\*TODO: TOO LONG,  should consider only 1 group at a time .. *\) *)
      (* 	[|LAnd; LOr|]; *)
      (* 	[|Lt; Gt; Le; Ge; Eq; Ne|] *)
      (*     ]; *)
      if !VC.vdebug then 
	E.log "%s: create bops ht (len %d)\n" super#cname (H.length ops_ht)

  (*if e has n ops supported by this class then returns a list of n ints 
    representing the number of compatible ops of each of the n ops,
    e.g., [7 3] means op1 in e has 7 compat ops, op2 has 3 compat ops.

    This (brute force) produces cartesian_product(list) template stmts,
    but each has 0 params.
   *)
  method spy_stmt (filename_unused:string) (sid:CC.sid_t) (fd:fundec) 
	 : (instr -> spy_t option) = function

    |Set(_,e,_) ->
      let rec find_ops l e: binop list = match e with
	|Const _ -> l
	|Lval  _ -> l
	|UnOp(_,e1,_) -> find_ops l e1
	|BinOp (bop,e1,e2,_) ->  
	  let e1_ops = find_ops l e1 in
	  let e2_ops = find_ops l e2 in
	  let e_ops = e1_ops@e2_ops in

	  (*append op if it belongs to this class*)
	  if H.mem ops_ht bop then bop::e_ops else e_ops

	|_ ->
	  CC.ealert "%s: don't know how to deal with exp '%a' (sid %d)" 
		    super#cname dn_exp e sid;
	  l
      in
      let ops = find_ops [] e in
      (*e.g.,  
      (x && y) || z -> [2; 2],
      (x&&y) < z -> [2; 5]
       *)
      let ops_lens = L.map (fun op -> A.length (H.find ops_ht op)) ops in 
      let len = L.length ops in 

      if !VC.vdebug then E.log "%s: found %d ops [%s]\n" 
			       super#cname len (VC.string_of_list (L.map CC.string_of_binop ops));

      if len > 0 then Some([sid],super#cid,super#level,ops_lens)
      else None
	     
    |_ -> None

  method mk_instr (ast:file) (main_fd:fundec) (sid:int) 
		  (tpl_id_unused:int) (idxs:int list) (xinfo:string) 
	 :(instr -> varinfo list ref -> instr list ref -> instr) = 

    assert (L.length idxs > 0);
    assert (L.for_all (fun idx -> idx >= 0) idxs);

    E.log "**%s: xinfo %s, idxs %d [%s]\n" super#cname xinfo 
						       (L.length idxs) (VC.string_of_ints idxs);

    fun a_i uks instrs -> (
      let mk_exp (e:exp): exp = 
	let idxs = A.of_list idxs in
	let ctr = ref 0 in
	
	let rec find_ops e = match e with
	  |Const _ -> e
	  |Lval _ -> e
	  |UnOp(uop,e1,ty) -> UnOp(uop,find_ops e1,ty)
	  |BinOp (bop,e1,e2,ty) -> 

	    let bop' = 
	      if H.mem ops_ht bop then
		let arr:binop array = H.find ops_ht bop in
		let bop'' = arr.(idxs.(!ctr)) in
		incr ctr;
		bop''
	      else
		bop
	    in

	    let e1' = find_ops e1 in
	    let e2' = find_ops e2 in
	    BinOp(bop', e1', e2', ty)
		 
	  | _ -> CC.ealert "%s: don't know how to deal with exp '%a'" 
			   super#cname dn_exp e;
		 e
	in
	let r_exp = find_ops e in 
	assert (!ctr = A.length idxs); (*make sure that all idxs are used*)
	r_exp   
      in
      
      match a_i with
      |Set(v,e,l) -> Set(v,mk_exp e,l)
      |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)
    )

end

(*
  change 
  typ x = ..;
  to 
  typ x = uk0 + uk1*v1 + uk2*v2 ; 
  where v0 have the same type as x, i.e., typ
  and other vi has type int, i.e., uk_i = {-1,0,1}
 *)

class bugfixTemplate_VS cname cid level = object(self)
  inherit bugfixTemplate cname cid level as super

  method spy_stmt (filename:string) (sid:CC.sid_t) (fd:fundec) 
	 : (instr -> spy_t option) = function

    |Set _ ->
      let bvs = find_boolvs fd in (*Find vars in sfd have type bool*)

      (*obtain usuable variables from fd*)
      let vs' = fd.sformals@fd.slocals in
      assert (L.for_all (fun vi -> not vi.vglob) vs');
      let vs' = !extra_vars@vs' in
      
      let vi_pred vi =
	isMArithType vi.vtype &&
	  L.for_all (fun bv -> vi <> bv) bvs &&
	    not (VC.in_str "__cil_tmp" vi.vname) &&
	      not (VC.in_str "tmp___" vi.vname)
      in
      let vs = L.filter vi_pred vs' in
      let n_vs = L.length vs in
      
      if !VC.vdebug then (
	E.log "%s: found %d/%d avail vars in fun %s [%s]\n"
    	      super#cname n_vs (L.length vs') fd.svar.vname 
			  (String.concat ", " (L.map (fun vi -> vi.vname) vs))
      );
      
      if n_vs > 0 then(
	VC.write_file_bin (arr_s filename sid super#cid) (A.of_list vs);
	Some([sid],super#cid,super#level,[n_vs])
      ) else None

    |_ -> None

  method mk_instr (ast:file) (main_fd:fundec) (sid:int) 
		  (tpl_id:int) (idxs:int list) (xinfo:string) 
	 :(instr -> varinfo list ref -> instr list ref -> instr) =

    let vs:varinfo array = VC.read_file_bin (arr_s ast.fileName sid tpl_id) in
    let vs:varinfo list = L.map (fun idx ->  vs.(idx) ) idxs in
    let n_vs = L.length vs in 

    E.log "** xinfo %s, |vs|=%d, [%s]\n" xinfo n_vs
	  (VC.string_of_list (L.map (fun vi -> vi.vname) vs));

    fun a_i uks instrs -> (
      let mk_exp ty = 
	let new_uk uid uty min_v max_v = 
	  mk_uk uid uty min_v max_v main_fd uks instrs 
	in
	let n_uks = succ (L.length vs) in
	
	(* let ts = L.map2 (fun x y ->  *)
	(*   E.log "%d vname %s vtype %s\n" x y.varname *)
	(* ) (range n_uks) vs in *)
	
	(* E.log "get here\n"; *)

	let my_uks = L.map (fun uid -> 
			    (*uk0 is arbitrary const, other uks are more restricted consts*)
			    match uid with
			    |0 -> (
			      match ty with
			      |TInt _ -> new_uk uid ty uk_iconst_min uk_iconst_max 
			      |TFloat(FFloat,_) -> new_uk uid ty uk_fconst_min uk_fconst_max 
			      |TFloat(FDouble,_) -> new_uk uid ty uk_dconst_min uk_dconst_max 
			      |_ -> E.s(E.error "unexp type %a " dn_type ty)
			    )
			    |_ -> new_uk uid intType uk_imin uk_imax
			   )  (VC.range n_uks)
	in
	let my_uks = L.map CC.exp_of_vi my_uks in 
	let vs = L.map CC.exp_of_vi vs in 
	let uk0,uks' = (L.hd my_uks), (L.tl my_uks) in 

	let r_exp = L.fold_left2 (fun a x y -> 
				  assert (typeOf x = typeOf y);
				  BinOp(PlusA, a, BinOp(Mult, x, y, ty), ty))
				 uk0 uks' vs in
	
	r_exp
      in
      
      match a_i with 
      |Set(v,_,l)->Set(v,mk_exp (typeOfLval v),l)
      |_ -> E.s(E.error "unexp assignment instr %a" d_instr a_i)      
    )

end


let tpl_classes:bugfixTemplate list = 
  [((new bugfixTemplate_CONSTS) "CONSTS" 3 1:> bugfixTemplate); 
   ((new bugfixTemplate_OPS_PR) "OPS_PR" 7 2 :> bugfixTemplate); 
   (* ((new bugfixTemplate_OPS_BF) "OPS_LOGIC_B" 5 13 :> bugfixTemplate);  *)
   (* ((new bugfixTemplate_OPS_BF) "OPS_COMP_B" 6 13 :> bugfixTemplate);  *)
   ((new bugfixTemplate_VS)     "VS"     1 4 :> bugfixTemplate)]


let spy 
      (filename:string)
      (stmt_ht:(int,stmt*fundec) H.t)
      (sid:CC.sid_t)
    : spy_t list
  = 
  let s,fd = H.find stmt_ht sid in
  if !VC.vdebug then E.log "Spy stmt id %d in fun %s\n%a\n" 
			   sid fd.svar.vname dn_stmt s;
  
  match s.skind with 
  |Instr ins ->
    assert (L.length ins = 1);
    let spy_f p c = 
      if p then c#spy_stmt filename sid fd (L.hd ins) else None
    in
    let rs = 
      if L.length !tpl_ids > 0 then
	L.map (fun cl -> spy_f (L.mem cl#cid !tpl_ids) cl) tpl_classes 
      else
	L.map(fun cl -> spy_f (cl#level <= !tpl_level) cl) tpl_classes
    in 
    VC.list_of_some rs

  |_ -> CC.ealert "no info obtained on stmt %d\n%a" sid dn_stmt s; []


(*runs in parallel*)
let transform 
      (filename:string) 
      (sids:CC.sid_t list) 
      (tpl_id:int) 
      (xinfo:string) 
      (idxs:int list) = 

  let (ast:file),(mainQ_fd:fundec),(tcs:FL.testcase_t list) =
    VC.read_file_bin (ginfo_s filename) in

  let main_fd = find_fun ast "main" in 
  let sid = L.hd sids in (*FIXME*)
  let sids_s = VC.string_of_ints ~delim:"_" sids in 

  (*modify stmt*)  
  let cl = L.find (fun cl -> cl#cid = tpl_id ) tpl_classes in 
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
  (*ast.globals <- (GText "#include \"klee/klee.h\"") :: ast.globals;*)
  ast.globals <- (GText "extern void __VERIFIER_error();") :: ast.globals;
  ast.globals <- (GText "extern int __VERIFIER_nondet_int();") :: ast.globals;
  ast.globals <- (GText "extern void __VERIFIER_assume();") :: ast.globals;
  
  let fn = transform_s ast.fileName sids_s xinfo in


  (*the symbol is useful when parsing the result, don't mess up this format*)
  E.log "Transform success: ## '%s' ##  %s\n" fn stat;
  CC.write_src fn ast


(********************** PROTOTYPE **********************)

let () = begin
    E.colorFlag := true;

    let filename = ref "" in
    let inputs   = ref "" in
    let outputs  = ref "" in 
    let version = P.sprintf "%s (%s) %f (CIL version %s)" 
			    progname progname_long progversion cilVersion 
    in 

    let arg_descrs = [
      "--debug", Arg.Set VC.vdebug, 
      P.sprintf " shows debug info (default %b)" !VC.vdebug;
      
      "--no_parallel", Arg.Set no_parallel, 
      P.sprintf " don't use multiprocessing (default %b)" !no_parallel;
      
      "--no_bugfix", Arg.Set no_bugfix, 
      P.sprintf " don't do bugfix (default %b)" !no_bugfix;
      
      "--no_stop", Arg.Set no_stop, 
      P.sprintf " don't stop after finding a fix (default %b)" !no_stop;
      
      "--no_global_vars", Arg.Set no_global_vars,
      P.sprintf " don't consider global variables when modify stmts (default %b)" 
		!no_global_vars;

      "--fl_sids", Arg.String (fun s -> 
			       fl_sids := L.map int_of_string (VC.str_split s)),
      (P.sprintf "%s" 
		 " don't run fault loc, use the given suspicious stmts, " ^
	 "e.g., --fl_sids \"1 3 7\".");
      
      "--fl_alg", Arg.Set_int FL.fl_alg,
      P.sprintf
	" use fault loc algorithm: 1 Ochia, 2 Tarantula (default %d)" 
	!FL.fl_alg;
      
      "--top_n_sids", Arg.Set_int FL.top_n_sids,
      P.sprintf " consider this # of suspicious stmts (default %d)" 
		!FL.top_n_sids;
      
      "--min_sscore", Arg.Set_float FL.min_sscore,
      P.sprintf " fix suspicious stmts with at least this score (default %g)" 
		!FL.min_sscore;
      
      "--tpl_ids", Arg.String (
		       fun s -> tpl_ids :=
				  L.map int_of_string (VC.str_split s)
		     ),
      " only use these bugfix template ids, e.g., --tpl_ids \"1 3\"";
      
      "--tpl_level", Arg.Set_int tpl_level,
      P.sprintf " fix tpls up to and including this level (default %d)" 
		!tpl_level;
      
      "--only_spy", Arg.Set only_spy, 
      P.sprintf " only do spy (default %b)" 
		!only_spy;

      "--only_peek", Arg.Set only_peek, 
      P.sprintf " only do peek the stmt given in --sid (default %b)" 
		!only_peek;
      
      (* STAND ALONE PROGRAM *)
      (* transforming file*)
      "--only_transform", Arg.Set only_transform, 
      " stand alone prog to transform code, " ^ 
	"e.g., --only_transform --sid 1 --tpl 1 --idxs \"3 7 8\" --xinfo z2_c5";
      
      "--sids", Arg.String (fun s-> 
			    let sids' =  L.map int_of_string (VC.str_split s) in
			    if L.exists (fun i -> i < 0) sids' then (
			      raise(Arg.Bad (
					P.sprintf 
					  "arg --sids must contain non-neg ints, [%s]" 
					  (VC.string_of_ints sids'))));
			    sids := sids'), 
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


    (* Stand alone program for transformation *)
    if !only_transform then (
      transform !filename !sids !tpl !xinfo !idxs;
      exit 0
    );


    (*** some initialization, getting testcases etc***)
    (*
    Note: src (filename) must be preprocessed by cil by running 
    cilly src.c --save-temps; the result is called src.cil.c

    Also, must have certain format  
    void main(..) {
    printf(mainQ);...
    }
     *)
    
    VC.chk_exist !inputs  ~msg:"require inputs file";
    VC.chk_exist !outputs ~msg:"require outputs file";

    (*create a temp dir to process files*)
    let tdir = VC.mkdir_tmp ~temp_dir:"/var/tmp" progname "" in
    let fn' = P.sprintf "%s/%s" tdir (Filename.basename !filename) in 
    VC.exec_cmd (P.sprintf "cp %s %s" !filename fn');
    
    let filename,inputs,outputs = fn', !inputs, !outputs in
    at_exit (fun () ->  E.log "Note: temp files created in dir '%s'\n" tdir);

    let tcObj = (new FL.uTest) filename in
    tcObj#get_tcs inputs outputs;
    
    let ast = Frontc.parse filename () in 

    visitCilFileSameGlobals (new CC.everyVisitor) ast;
    visitCilFileSameGlobals (new FL.breakCondVisitor :> cilVisitor) ast;

    let stmt_ht:(CC.sid_t,stmt*fundec) H.t =
      CC.mk_stmt_ht ast CC.can_modify ~create_stmt_ids:true in
    CC.write_src (ast.fileName ^ ".preproc.c") ast;

    if !only_peek then (
      ignore (visitCilFileSameGlobals ((new peekVisitor) !sids) ast);
      exit 0);

    (* determine if file contains synthesis stmts*)
    let syn_sids = find_synstmts ast in 
    only_synthesis := L.length syn_sids > 0 ;

    let perform_s = ref "" in 
    let sids:CC.sid_t list ref = ref [] in 

    if !only_synthesis then (
      perform_s := "Synthesis";
      sids := syn_sids;
      tpl_ids := [3] (*CONST template*)
    )
    else ( 
      perform_s := "BugFix";
      (*** fault localization ***)

      let fl_sids:CC.sid_t list = 
	if L.length !fl_sids > 0 then !fl_sids 
	else (
	  let flVis = (new FL.faultloc) ast tcObj#mygoods tcObj#mybads stmt_ht in
	  let ssids = flVis#get_susp_sids !FL.fl_alg in

	  (*remove all susp stmts in main, which cannot have anything except call
	  to mainQ, everything in main will be deleted when instrumenting main*)

	  let idx = ref 0 in 
	  let ssids = L.filter (
			  fun (sid,score) -> 
			  let s,f = H.find stmt_ht sid in
			  if score >= !FL.min_sscore && f.svar.vname <> "main" then(
			    E.log "%d. sid %d in fun '%s' (score %g)\n%a\n"
				  !idx sid f.svar.vname score dn_stmt s;
			    incr idx;
			    true
			  ) else false
			) ssids in
	  CC.ealert "FL: found %d ssids with sscores >= %g" 
		    (L.length ssids) !FL.min_sscore;
	  
	  let ssids = VC.take !FL.top_n_sids ssids in (*consider only n top susp stmts*)
	  L.map fst ssids
	)
      in
      sids := fl_sids
    );

    CC.ealert "Perform ** %s **" !perform_s;

    let sids = !sids in
    if L.length sids = 0 then (CC.ealert "No suspicious stmts !"; exit 0);
    
    (*** transformation and bug fixing ***)
    (* find mainQ *)
    let mainQ_fd = find_fun ast mainfunname in
    
    if not !no_global_vars then (
      iterGlobals ast (function 
			|GVar (vi,_,_) -> extra_vars := vi::!extra_vars 
			|_ -> ());
      
      if !VC.vdebug then 
	E.log "Consider %d gloval vars [%s]\n" 
	      (L.length !extra_vars) 
	      (VC.string_of_list (L.map (fun vi -> vi.vname) !extra_vars));
    );

    (*spy on suspicious stmts*)
    if !VC.vdebug then E.log "Spy %d sids: [%s] with tpl_ids: [%s]\n" 
			     (L.length sids) (VC.string_of_ints sids) (VC.string_of_ints !tpl_ids);

    let rs = L.map (spy ast.fileName stmt_ht) sids in
    let rs' = L.filter (function |[] -> false |_ -> true) rs in
    let rs = L.flatten rs' in 
    CC.ealert "Spy: Got %d info from %d sids" (L.length rs) (L.length rs');
    if (L.length rs) = 0 then (CC.ealert "No spied info. Exit!"; exit 0);

    let rs = 
      if !only_synthesis then 
	group_sids sids rs (*synthesize multiple statements simultenously*)
      else
	rs
    in
    let rs = L.map string_of_spys rs in

    (*call Python script to do transformation*)
    let rs = String.concat "; " rs in
    let kr_opts = [
      if !VC.vdebug then "--debug" else "";
      if !no_parallel then "--no_parallel" else "";
      if !no_bugfix then  "--no_bugfix"  else "";
      if !no_stop then "--no_stop" else ""
    ] in
    let kr_opts = String.concat " " (L.filter (fun o -> o <> "") kr_opts) in

    let cmd = P.sprintf "python2.7 %s %s --do_tb \"%s\" %s"
			python_script ast.fileName rs kr_opts in

    if !only_spy then exit 0;

    (*write info to disk for parallelism use*)
    VC.write_file_bin (ginfo_s ast.fileName) (ast,mainQ_fd,tcObj#mytcs);
    VC.exec_cmd cmd
		

  end

(*IMPORTANT: main must be empty and only call mainQ
TODO: after getting everything working again:  no need to write vs arr to disk, can just reconstruct it from main_fd
*)
