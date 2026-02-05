(* file: subst.sml *)
(* description: substutition *)
(* author: Takahito Aoto *)

signature SUBST = 
sig 
    type subst
    val apply: subst -> Term.term -> Term.term
    val dom: subst -> Var.key list
    val toString: subst -> string 
    val fromString: string -> subst
    val match: Term.term -> Term.term -> subst option
    val compose: subst -> subst -> subst
    val unify: Term.term * Term.term -> subst option
    val isUnif: Term.term * Term.term -> bool
end

structure Subst: SUBST =
struct 

local 
    structure L = List
    structure AL = AssocList
    structure T = Term
    structure S = Symbol
in

type subst = (Var.key * Term.term) list

fun apply sigma (T.Var x) = (case AL.find x sigma of
    	  	       	         SOME v => v
			       | NONE => T.Var x)
  | apply sigma (T.Fun (f,ts)) = T.Fun (f,(applyList sigma ts))
and applyList sigma [] = []
  | applyList sigma (t::ts) = (apply sigma t)::(applyList sigma ts)

fun dom [] = []
  | dom ((k,T.Var x)::sigma) = if k = x then dom sigma else k::(dom sigma)
  | dom ((k,T.Fun (f,ts))::sigma) = k::(dom sigma)

fun toString sigma = ListUtil.toStringCommaSpaceBrace (fn (v,t) => "?" ^ (Var.toString v) ^ " := " ^ (Term.toString t)) sigma

fun fromString str = 
    let val tps = T.readMultipleKeySepartedTermPairs ("{",",","}") ":=" str
	fun getVar s  = case T.root s of 
			    S.V x => x 
			  | S.F _ => raise Fail ("Syntax error: var expected " ^ (T.toString s))
    in L.map (fn (s,t) => (getVar s, t)) tps
    end

fun match pattern term =
    let fun main [] sigma = SOME sigma
    	  | main ((T.Var x, t0)::rest) sigma = (case AL.add (x, t0) sigma of
	    	 	    	       	       	    SOME v => main rest v
						  | NONE => NONE)
	  | main ((T.Fun (f,ts), T.Fun (g,us))::rest) sigma = if (Symbol.F f) = (Symbol.F g)
	    	 	 	       		      	      then main (ListUtil.union (ListPair.zip (ts,us),rest)) sigma
							      else NONE
	  | main ((T.Fun _, T.Var _)::_) _ = NONE
    in main [(pattern,term)] []
    end

fun compose [] rho = rho
  | compose ((x,t)::sigma) rho = valOf (AL.add (x,apply rho t) (compose sigma rho))

fun unify (term1,term2) =
    let fun main [] sigma = SOME sigma
	  | main ((T.Var x, t)::rest) sigma = (case (T.Var x) = t of
						  true => main rest sigma
						| false => case ListUtil.member x (T.vars t) of
							       true => NONE
							     | false => main (map (fn (t1,t2) => (apply [(x,t)] t1,apply [(x,t)] t2)) rest) (compose sigma [(x,t)]))
	  | main ((T.Fun (f,ts), T.Fun (g,us))::rest) sigma = (case Symbol.F f = Symbol.F g of
								  true => main (ListUtil.union (ListPair.zip (ts,us),rest)) sigma
								| false => NONE)
	  | main ((t, T.Var x)::rest) sigma = main ((T.Var x, t)::rest) sigma
    in main [(term1,term2)] []
    end

fun isUnif (s,t) = isSome (unify (s,t))
	
end (* of local *)

end
