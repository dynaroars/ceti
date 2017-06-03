open Cil
module E = Errormsg
module L = List
module A = Array
module H = Hashtbl 
module P = Printf

module CC = Cil_common
module VC = Vu_common
module ST = Settings

type spy_t = CC.sid_t list*int*int*int list (*sid,cid,level,idxs*)

let string_of_spys ((sids,cid,level,idxs):spy_t): string = 
  let sid' = (String.concat " " (L.map string_of_int sids)) in
  let idxs' = (String.concat " " (L.map string_of_int idxs)) in
  P.sprintf "(%s, %d, %d, %s)" sid' cid level idxs'


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

let findBoolvs fd = 
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
    |Instr[Set((Var vi,_),Const _,_)] when VC.in_str ST.synvarname vi.vname ->
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

(* make unknown variables and their assumptions*)
let mkUk
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
  
  (*klee_make_symbolic(&uk,sizeof(uk),"uk")*)
  let mkSymInstr:instr =
    CC.mkCall "klee_make_symbolic"
  	       [mkAddrOf(lv); SizeOfE(Lval lv); Const (CStr vname)]
  in
  
      (* let mk_sym_instr:instr = *)
  (*   CC.mkCall ~av:(Some lv) "__VERIFIER_nondet_int" [] in *)
  
  
  let klee_assert_lb:instr = CC.mkCall "klee_assume"
					[BinOp(Le,min_v,Lval lv, CC.boolTyp)] in 
  
  let klee_assert_ub:instr = CC.mkCall "klee_assume"
					[BinOp(Le,Lval lv, max_v, CC.boolTyp)] in 
  
  vs := !vs@[vi];
  instrs := !instrs@[mkSymInstr;  klee_assert_lb; klee_assert_ub];

  vi 



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
	  mkUk uid uty min_v max_v main_fd uks instrs 
	in
	let ctr = ref (L.length !uks) in
	
	let rec find_consts e = match e with
	  |Const(CInt64 _) -> 
	    let vi = new_uk !ctr (typeOf e) ST.uk_iconst_min ST.uk_iconst_max 
	    in incr ctr; CC.exp_of_vi vi
	  |Const(CReal (_,FFloat,_)) -> 
	    let vi = new_uk !ctr (typeOf e) ST.uk_fconst_min ST.uk_fconst_max 
	    in incr ctr; CC.exp_of_vi vi
	  |Const(CReal (_,FDouble,_)) -> 
	    let vi = new_uk !ctr (typeOf e) ST.uk_dconst_min ST.uk_dconst_max 
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
	let new_uk uid = mkUk uid intType zero one main_fd uks instrs in

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
		  let klee_assert_xor:instr = CC.mkCall "klee_assume" [xor_exp] in
		  (*let klee_assert_xor:instr = CC.mkCall "__VERIFIER_assume" [xor_exp] in*)
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
      let bvs = findBoolvs fd in (*Find vars in sfd have type bool*)

      (*obtain usuable variables from fd*)
      let vs' = fd.sformals@fd.slocals in
      assert (L.for_all (fun vi -> not vi.vglob) vs');
      let vs' = !ST.extra_vars@vs' in
      
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
	VC.write_file_bin (ST.arr_s filename sid super#cid) (A.of_list vs);
	Some([sid],super#cid,super#level,[n_vs])
      ) else None

    |_ -> None

  method mk_instr (ast:file) (main_fd:fundec) (sid:int) 
		  (tpl_id:int) (idxs:int list) (xinfo:string) 
	 :(instr -> varinfo list ref -> instr list ref -> instr) =

    let vs:varinfo array = VC.read_file_bin (ST.arr_s ast.fileName sid tpl_id) in
    let vs:varinfo list = L.map (fun idx ->  vs.(idx) ) idxs in
    let n_vs = L.length vs in 

    E.log "** xinfo %s, |vs|=%d, [%s]\n" xinfo n_vs
	  (VC.string_of_list (L.map (fun vi -> vi.vname) vs));

    fun a_i uks instrs -> (
      let mk_exp ty = 
	let new_uk uid uty min_v max_v = 
	  mkUk uid uty min_v max_v main_fd uks instrs 
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
			      |TInt _ -> new_uk uid ty ST.uk_iconst_min ST.uk_iconst_max 
			      |TFloat(FFloat,_) -> new_uk uid ty ST.uk_fconst_min ST.uk_fconst_max 
			      |TFloat(FDouble,_) -> new_uk uid ty ST.uk_dconst_min ST.uk_dconst_max 
			      |_ -> E.s(E.error "unexp type %a " dn_type ty)
			    )
			    |_ -> new_uk uid intType ST.uk_imin ST.uk_imax
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
      if L.length !ST.tpl_ids > 0 then
	L.map (fun cl -> spy_f (L.mem cl#cid !ST.tpl_ids) cl) tpl_classes 
      else
	L.map(fun cl -> spy_f (cl#level <= !ST.tpl_level) cl) tpl_classes
    in 
    VC.list_of_some rs

  |_ -> CC.ealert "no info obtained on stmt %d\n%a" sid dn_stmt s; []


