signature INF =
sig
    val getSymbolsFun: Form.form list -> (Term.fun_key * int) list
    val getSymbolsPred: Form.form list -> Form.pred_key list
    val makeInjNotOntoEq: Term.fun_key * int -> Form.form list
    val makeInjNotOntoPred: Form.pred_key -> Term.fun_key * int -> Form.form list
    val makeOntoNotInj: Term.fun_key * int -> Form.form list
    val makeSerial: Form.pred_key -> Term.fun_key * int -> Form.form list
    val makeForward: (Form.pred_key * Form.pred_key) -> Term.fun_key * int -> Form.form list
    val makeConjecture: Form.form list -> string list

    val isRefl: Form.pred_key -> Form.form list -> bool
    val isNotRefl: Form.pred_key -> Form.form list -> bool
    val elimPred: Form.pred_key list -> Form.form list -> (Form.pred_key -> Form.form list -> bool) -> Form.pred_key list

    val makeInFile: string list -> string -> unit
    val runP9: unit -> string
    val checkInfProp: Form.form list-> IntInf.int -> bool
end

structure Inf :INF =
struct
local
    structure LU = ListUtil
    structure T = Term
    structure F = Form
in

fun getSymbolsFun forms = List.filter (fn (f, k) => k > 0) (F.getArsFun forms)
fun getSymbolsPred forms = List.mapPartial (fn (p, k) => if k = 2 andalso p <> "=" then SOME p else NONE) (F.getArsPred forms)

fun makeConsts args = List.tabulate (length (List.filter (fn x => x = 1) args), fn x => T.Fun ("$C" ^ Int.toString (x + 1), []))
				      
fun makeTerm var symbol args consts =
    let fun getArgs _ [] [] = []
	  | getArgs _ [] _ = raise Fail "Error: invalid args"
	  | getArgs var (arg::restArgs) [] = if arg = 1 then raise Fail "Error: invailid args" else (T.Var var)::(getArgs var restArgs [])
	  | getArgs var (arg::restArgs) (const::restConsts) = if arg = 1 then const::(getArgs var restArgs restConsts) else (T.Var var)::(getArgs var restArgs (const::restConsts))
    in T.Fun (symbol, getArgs var args consts)
    end

fun makeInjNotOntoEq (symbol, arity) =
    let fun makeForm x y var symbol args =
	    let val consts = makeConsts args
		val inj = F.Imp (F.Atom (F.Eq (makeTerm x symbol args consts, makeTerm y symbol args consts)), F.Atom (F.Eq (T.Var x, T.Var y)))
		val notOnto = F.Not (F.Atom (F.Eq (makeTerm x symbol args consts, T.Var var)))
	    in F.Exists (var, F.All (x, F.All (y, (F.And (inj, notOnto)))))
	    end 
    in List.map (fn args => makeForm ("x", 0) ("y", 0) ("$C", 0) symbol args) (tl (LU.combinations arity [1,0]))
    end

fun makeInjNotOntoPred pred (symbol, arity) =
    let fun makeForm x y var symbol args =
	    let val consts = makeConsts args
		val refl = F.Atom (F.Pred (pred,[T.Var x, T.Var x]))
		val inj = F.Imp (F.Atom (F.Pred (pred, [makeTerm x symbol args consts, makeTerm y symbol args consts])), F.Atom (F.Pred (pred, [T.Var x, T.Var y])))
		val leftNotOnto = F.Not (F.Atom (F.Pred (pred, [makeTerm x symbol args consts, T.Var var])))
		val rightNotOnto = F.Not (F.Atom (F.Pred (pred, [T.Var var, makeTerm x symbol args consts])))
		val quants = fn form => F.Exists (var, F.All (x, F.All (y, form)))
	    in [quants (F.And (refl, F.And (inj, leftNotOnto))), quants (F.And (refl, F.And (inj, rightNotOnto)))]
	    end 
    in List.concatMap (fn args => makeForm ("x", 0) ("y", 0) ("$C", 0) symbol args) (tl (LU.combinations arity [1,0]))
    end

fun makeOntoNotInj (symbol, arity) =
    let fun makeForm x y var symbol args =
	    let val consts = makeConsts args
		val notInj = F.And (F.Atom (F.Eq (makeTerm x symbol args consts, makeTerm y symbol args consts)), F.Not (F.Atom (F.Eq (T.Var x, T.Var y))))
		val onto = F.Atom (F.Eq (makeTerm var symbol args consts, T.Var x))
	    in F.All (x, F.Exists (var, F.All (y, F.And (notInj, onto))))
	    end 
    in List.map (fn args => makeForm ("x", 0) ("y", 0) ("$C", 0) symbol args) (tl (LU.combinations arity [1,0]))
    end

fun makeSerial pred (symbol, arity) =
    let fun makeForm x y z var symbol args =
	    let val consts = makeConsts args
		val notRefl = F.Not (F.Atom (F.Pred (pred, [T.Var x, T.Var x])))
		val trans = F.Imp (F.And (F.Atom (F.Pred (pred, [T.Var x, T.Var y])), F.Atom (F.Pred (pred, [T.Var y, T.Var z]))), F.Atom (F.Pred (pred, [T.Var x, T.Var z])))
 		val leftSerial = F.Atom (F.Pred (pred, [T.Var x, T.Var var]))
		val rightSerial = F.Atom (F.Pred (pred, [T.Var var, T.Var x]))
		val quants = fn form => F.All (x, F.Exists (var, F.All (y, F.All (z, form))))
	    in [quants (F.And (notRefl, F.And (trans, leftSerial))), quants (F.And (notRefl, F.And (trans, rightSerial)))]
	    end 
    in List.concatMap (fn args => makeForm ("x", 0) ("y", 0) ("z", 0) ("$C", 0) symbol args) (tl (LU.combinations arity [1,0]))
    end

fun makeForward (p, q) (symbol, arity) =
    let fun makeForm x y z var symbol args =
	    let val consts = makeConsts args
		val refl = F.Atom (F.Pred (q,[T.Var x, T.Var x]))
		val trans = F.Imp (F.And (F.Atom (F.Pred (p, [T.Var x, T.Var y])), F.Atom (F.Pred (q, [T.Var y, T.Var z]))), F.Atom (F.Pred (q, [T.Var x, T.Var z])))
		val leftForward = F.And (F.Atom (F.Pred (p, [T.Var x, T.Var var])), F.Not (F.Atom (F.Pred (q, [T.Var var, T.Var x]))))
		val rightForward = F.And (F.Atom (F.Pred (p, [T.Var var, T.Var x])), F.Not (F.Atom (F.Pred (q, [T.Var x, T.Var var]))))
		val quants = fn form => F.All (x, F.Exists (var, F.All (y, F.All (z, form))))
	    in [quants (F.And (refl, F.And (trans, leftForward))), quants (F.And (refl, F.And (trans, rightForward)))]
	    end 
    in List.concatMap (fn args => makeForm ("x", 0) ("y", 0) ("z", 0) ("$C", 0) symbol args) (tl (LU.combinations arity [1,0]))
    end 

fun toString form =
    let fun paren s = "(" ^ s ^ ")"
	fun aux (F.Atom atom) = F.toStringAtom atom
	  | aux (F.Not p) = "-" ^ paren (aux p)
	  | aux (F.And (p, q)) = paren (aux p ^ " & " ^ aux q)
	  | aux (F.Or (p, q)) = paren (aux p ^ " | " ^ aux q)
	  | aux (F.Imp (p, q)) = paren (aux p ^ " -> " ^ aux q)
	  | aux (F.Iff (p, q)) = paren (aux p ^ " <-> " ^ aux q)
	  | aux (F.All (x, p)) = "all " ^ Var.toString x ^ " " ^ paren (aux p)
	  | aux (F.Exists (x, p)) = "exists " ^ Var.toString x ^ " " ^ paren (aux p)
    in (aux o F.toVars o F.toNeq) form
    end

fun isRefl pred forms =
    let fun main (F.Atom (F.Pred (p, [s, t]))) = if p = pred andalso T.isVar s andalso T.isVar t andalso s = t
						      then true
						 else false
	  | main (F.All (x, p)) = main p
	  | main _ = false 
    in List.exists (fn form => main form) forms
    end

fun isNotRefl pred forms =
    let fun main (F.Not (F.Atom (F.Pred (p, [s, t])))) = if p = pred andalso T.isVar s andalso T.isVar t andalso s = t
						      then true
							 else false
	  | main (F.All (x, p)) = main p
	  | main _ = false 
    in List.exists (fn form => main form) forms
    end
	
fun elimPred preds forms fx = List.filter (fn pred => not (fx pred forms)) preds
	
fun makeConjecture forms =
    let val funs = getSymbolsFun forms
	val preds = getSymbolsPred forms
	val InjNotOntoPred = List.concatMap (fn f => List.concatMap (fn p => makeInjNotOntoPred p f) (elimPred preds forms isNotRefl)) funs
	val serial = List.concatMap (fn f => List.concatMap (fn p => makeSerial p f) (elimPred preds forms isRefl)) funs
	val forward = List.concatMap (fn f=> List.concatMap (fn (p, q) => makeForward (p, q) f) (List.mapPartial (fn [p, q] => if p = q then NONE else SOME (p, q) | _ => NONE) (LU.combinations 2 preds))) funs
	val InjNotOntoEq = List.concatMap makeInjNotOntoEq funs
	val ontoNotInj = List.concatMap makeOntoNotInj funs
    in List.map (fn conj => toString conj) (InjNotOntoPred @ serial @ forward @ InjNotOntoEq @ ontoNotInj)
    end

fun makeInFile assumptions conj =
    let val outStream = TextIO.openOut "inf.in"
	val _ = TextIO.output (outStream, "assign(max_seconds, 1).\n")
	val _ = TextIO.output (outStream, "formulas(assumptions).\n")
	fun loop [] = ()
	  | loop (line::rest) =
	    let val _ = TextIO.output (outStream, line ^ ".\n")
	    in loop rest
	    end
	val _ = loop assumptions
	val _ = TextIO.output (outStream, "end_of_list.\n\n")
	val _ = TextIO.output (outStream, "formulas(goals).\n")
	val _ = TextIO.output (outStream, conj ^ ".\n")
	val _ = TextIO.output (outStream, "end_of_list.\n")
	val _ = TextIO.closeOut outStream
    in ()
    end

fun runP9 () =
    let val command = "./prover9 -f inf.in > inf.out"
	val _ = OS.Process.system command
	val inStream = TextIO.openIn "inf.out"
	val result = TextIO.inputAll inStream
	val _ = TextIO.closeIn inStream  
    in result
    end

fun checkInfProp forms sec =
    let val conjList = makeConjecture forms
	val assumptions = List.map toString forms
	fun loopProving _ [] = false
	  | loopProving assumptions (conj::rest) =
	    let val _ = makeInFile assumptions conj
		val isInf = String.isSubstring "THEOREM PROVED" (runP9 ())
	    in if isInf then true else loopProving assumptions rest
	    end
	val time = Time.fromSeconds sec
    in TimeLimit.timeLimit time (loopProving assumptions) conjList
       handle TimeLimit.TimeOut => false
    end 
end
end 
