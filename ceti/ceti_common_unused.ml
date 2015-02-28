open Cil
open Cil_common
open Vu_common
module E = Errormsg
module H = Hashtbl



(* Walks over AST and builds a hashtable that maps int to stmt*fundec *)
class numVisitor ht = object(self)
  inherit nopCilVisitor

  val mutable mctr = 1
  val mutable cur_fd = None

  method vfunc f = cur_fd <- (Some f); DoChildren

  (*Stmts that can be tracked for fault loc and modified for bug fix *)
  method private can_modify : stmtkind -> bool = function 
  |Instr[Set(_)] -> true
  |_ -> false

  method vblock b = 
    let action (b: block) : block= 
      let change_sid (s: stmt) : unit = 
	if self#can_modify s.skind then (
	  s.sid <- mctr;
	  let fd = match cur_fd with 
	    | Some f -> f | None -> E.s(E.error "not in a function") in
	  H.add ht mctr (s, fd);
	  mctr <- succ mctr
	)
	else s.sid <- 0;  (*Anything not considered has sid 0 *)
      in 
      L.iter change_sid b.bstmts; 
      b
    in 
    ChangeDoChildrenPost(b, action)

end


(*Stmts that can be tracked for fault loc and modified for bug fix *)
let can_modify : stmtkind -> bool = function 
  |Instr[Set(_)] -> true
  |_ -> false


class storeHTVisitor ht = object(self)
  inherit nopCilVisitor

  val mutable cur_fd = None

  method vfunc f = cur_fd <- (Some f); DoChildren

  method vblock b = 
    let action (b: block) : block= 
      let change_sid (s: stmt) : unit = 
	let fd = match cur_fd with 
	  | Some f -> f | None -> E.s(E.error "not in a function") 
	in
	H.add ht s.sid (s, fd)
      in 
      L.iter change_sid b.bstmts; 
      b
    in 
    ChangeDoChildrenPost(b, action)

end



class printCFGVisitor cfg_contents = object(self)
  inherit nopCilVisitor
  method vstmt s =
    let neg_id_in_stmts stmts = L.mem (-1) (sids_of_stmts stmts) in
    
    (*E.log "\n*** sid %d *** \n%a\n" s.sid dn_stmt s;*)

    let preds = string_of_ints  ~delim:" " (sids_of_stmts s.preds) in
    (* let succs = string_of_ints ~delim:" " (sids_of_stmts s.succs) in *)
    (*E.log "preds: [%s]\nsuccs: [%s]\n*****\n" preds succs;*)

    if neg_id_in_stmts s.preds || neg_id_in_stmts s.succs then
      (E.s (E.error "Problem: -1 in list"));
    
    cfg_contents := !cfg_contents ^ (P.sprintf "%d %s\n" s.sid preds);
    DoChildren
end
