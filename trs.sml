(* file: trs.sml *)
(* description: first-order term rewriting systems *)
(* author: Takahito Aoto *)

signature TRS = 
sig
    type rl = Term.term * Term.term
    type conds = (Term.term * Term.term) list
    type crl = rl * conds
    type trs = rl list
    type ctrs = crl list
    type reach = Term.term * Term.term

    val prRule: rl -> string
    val rdRule: string -> rl

    val prEq: Term.term * Term.term -> string

    val prRules: trs -> string
    val rdRules: string -> trs

    val prCRule: crl -> string
    val prCRules: ctrs -> string

    val vars: reach -> Var.key list
end

structure Trs: TRS =
struct

local
    structure LU = ListUtil
    structure SU = StringUtil
    structure T = Term
in

type rl = T.term * T.term
type conds = (T.term * T.term) list
type crl = rl * conds
type trs = rl list
type ctrs = crl list
type reach = T.term * T.term

fun prRule (l,r) = (Term.toString l) ^ " -> " ^ (Term.toString r)
fun rdRule str = T.readKeySeparatedTermPair "->" str

fun prEq (l,r) = (Term.toString l) ^ " = " ^ (Term.toString r)

fun prRules rs = ListUtil.toStringCommaLnSquare prRule rs
fun rdRules str = T.readMultipleKeySepartedTermPairs ("[",",","]") "->" str

fun prCRule (rule,conds) = if null conds
			   then prRule rule
			   else prRule rule ^ " <= " ^ String.concatWith ", " (List.map prEq conds)

fun prCRules ctrs = LU.toStringCommaLnSquare prCRule ctrs

fun vars (s,t) = LU.union (T.vars s, T.vars t)
	
end (* of local *)

end


