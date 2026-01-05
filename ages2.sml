signature AG2 =
sig
    val makeGeq: Ln.coef list -> Var.key list -> Ln.coef -> Ln.atom
    val toLnForm: Form.form list -> (Ln.atom list * Ln.atom) list
end

structure Ag2 : AG2 =
struct
local
    structure T = Term
    structure F = Form
    structure LU = ListUtil
in
fun makeGeq lefts vars right =
    let val terms = ListPair.zip (lefts, vars)
	fun getTerm (coef, var) = (coef, Ln.Var var)
    in Ln.Geq (Ln.Fun (List.map getTerm terms), Ln.Fun [(right, Ln.Var ("0", 0))])
    end

fun makeDomConstraints () = [makeGeq [[["$c_1", "k"]]] [("0", 0)] [["$b_1"]], makeGeq [[["$c_2", "k"]]] [("0", 0)] [["$b_2"]]]

fun getPolynomial (f, k) =
    let val vars = List.tabulate (k, fn x => ("x", x + 1))
	val conds = List.concatMap (fn x => [makeGeq [[["$c_1"]]] [x] [["$b_1"]], makeGeq [[["$c_2"]]] [x] [["$b_2"]]]) vars
	val term = Ln.makeTerm (T.Fun (f, List.map (fn x => T.Var x) vars))
    in (conds, term)
    end

fun closure forms =
    let fun main [] = []
	  | main (arity::rest) =
	    let val (conds, Ln.Fun polynomial) = getPolynomial arity
		val geq1 = Ln.Geq (Ln.Fun (List.map (fn (coef, t) => (Ln.expandCoef ([["$c_1"]], coef),t)) polynomial),Ln.Fun [([["$b_1"]], Ln.Var ("0",0))])
		val geq2 = Ln.Geq (Ln.Fun (List.map (fn (coef, t) => (Ln.expandCoef ([["$c_2"]], coef),t)) polynomial),Ln.Fun [([["$b_2"]], Ln.Var ("0",0))])
	    in if null conds then (conds, geq1)::(conds, geq2)::(main rest) else (conds, Ln.moveTerm geq1)::(conds, Ln.moveTerm geq2)::(main rest)
	    end 
    in main (F.getArsFun forms)
    end

fun toLnForm forms =
    let val cnf = List.concatMap (F.cnfList o F.cnf o F.toQF o F.skolem o F.nnf) forms
	fun toConstraints cl =
	    let fun abs (F.Pos p) = p
		  | abs (F.Neg p) = p
		fun moveTerms (eqs, eq) = (List.map Ln.moveTerm eqs, Ln.moveTerm eq)
		fun conv1 pos conds =
		    let val (conseq, ant) = valOf (List.getItem pos)
			val exAnt = LU.allCombinations (List.map (fn a => Ln.makeFormNeg (abs a)) ant)
		    in List.concatMap (fn ci => List.map (fn a => moveTerms (conds @ a, ci)) exAnt) (Ln.makeForm (abs conseq))
		    end
		fun conv2 neg conds =
		    let val (conseq, ant) = valOf (List.getItem neg)
			val ant' = List.concatMap (fn a => Ln.makeForm (abs a)) ant
			val (c1, c2) = (fn [x, y] => (x, y) | _ => raise Fail "Error: invalid list") (Ln.makeFormNeg (abs conseq))
		    in [moveTerms (conds @ c1::ant', c2)]
		    end
		fun conv3 (pos, neg) conds =
		    let val (conseq, ant) = valOf (List.getItem pos)
			val antNeg = List.concatMap (fn a => Ln.makeForm (abs a)) neg
			val exAnt = LU.allCombinations (List.map (fn a => Ln.makeFormNeg (abs a)) ant)
			val ant' = List.map (fn a => conds @ antNeg @ a) exAnt
		    in List.concatMap (fn ci => List.map (fn a => moveTerms (a, ci)) ant') (Ln.makeForm (abs conseq))
		    end
		val vars = List.concatMap F.varsAtom (List.map abs cl)
		val conds = List.concatMap (fn x => [makeGeq [[["$c_1"]]] [x] [["$b_1"]], makeGeq [[["$c_2"]]] [x] [["$b_2"]]]) vars
		val (pos, neg) = List.partition (fn (F.Pos _) => true | (F.Neg _) => false) cl
	    in if null neg then conv1 pos conds
	       else if null pos then conv2 neg conds
	       else conv3 (pos, neg) conds
	    end 
    in List.concatMap toConstraints cnf
    end
(*
fun applyFarkas (eqs, eq) i =
    let fun findCoef (Ln.Fun ts) var = (case List.find (fn (_, Ln.Var x) => var = x | _ => false) ts of
					 SOME (c, _) => SOME c
				       | NONE => SOME [["0"]])
	fun getMatrixVarFromEq
	val vars = LU.unions (List.map Ln.varsAtom eqs)
	val A = List.map ()
	val b =
	val c = [getmatrixVarFromEq eq vars]
	val beta = [(fn Ln.Eq (l,r) => Ln.getCoef r | Ln.Geq (l,r) => Ln.getCoef r) eq]
	val lambda = makeLambda i (length b)
    in
    end
*) 
end 
end
