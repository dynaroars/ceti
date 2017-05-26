open Cil
module P = Printf
module CC = Cil_common
	      
let progname:string = "CETI"
let progname_long:string = "Correcting Errors using Test Inputs"
let progversion:float = 0.1
let mainfunname:string = "mainQ"
let synvarname:string = "ceti_q"

			  
let uk_iconst_min:exp = integer (-100000)
let uk_iconst_max:exp = integer 100000
let uk_fconst_min:exp = Const(CReal(-100000.,FFloat,None))
let uk_fconst_max:exp = Const(CReal(100000.,FFloat,None))
let uk_dconst_min:exp = Const(CReal(-100000.,FDouble,None))
let uk_dconst_max:exp = Const(CReal(100000.,FDouble,None))


(* coeffs, e.g., c1*v1 + ... + cnvn*)
let uk_imin:exp = mone (* -1 *) 
let uk_imax:exp =  one
			     

let arr_s = P.sprintf "%s.s%d.t%d.arr" (*f.c.s1.t3.arr*)
let extra_vars:varinfo list ref = ref []		     

let tpl_ids:int list ref = ref [] (*apply only these specific template ids*)
let tpl_level:int ref = ref 4 (*apply only templates with <= levels*)


let ginfo_s = P.sprintf "%s.info" (*f.c.info*)			    

let sids:CC.sid_t list ref = ref [] (*only do transformation on vs_idxs*)
