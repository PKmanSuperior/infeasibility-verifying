signature IN =
sig
    datatype cond = OR | SEMI
    datatype system = TRS | CTRS of cond
    val setOpt: string -> system
    val test: string -> Form.form list
						 
    val read: string -> Form.form list
    val encode: string -> unit
end 

structure In : IN =
struct
local
    structure T = Term
    structure F = Form
    structure LU = ListUtil
    structure SU = StringUtil
in
    datatype cond = OR | SEMI
    datatype system = TRS | CTRS of cond

fun setOpt str = if String.isSubstring "CTRS" str
		    then if String.isSubstring "oriented" str
			 then CTRS OR
			 else CTRS SEMI
		 else TRS
			  
fun getSymbols [] acc = rev acc
  | getSymbols (str::rest) acc = 
    let fun getSymbol str =
	    let val arity = tl (SU.split str #" ")
	    in (fn [c1,c2] => (case Int.fromString c2 of
				   SOME k => (Fun.fromString c1, k)
				 | NONE => raise Fail "Error")
	       | _ => raise Fail "Error") arity
	    end
    in getSymbols rest (getSymbol str::acc)
    end
fun makeConv () = F.Imp (F.Or (F.Atom (F.Pred ("P", [T.Var ("x", 0), T.Var ("y", 0)])), F.Atom (F.Pred ("P", [T.Var ("y", 0), T.Var ("x", 0)]))), F.Atom (F.Pred ("Pc", [T.Var ("x", 0), T.Var ("y", 0)])))
fun makeTransConv () = F.Imp (F.And (F.Atom (F.Pred ("Pc", [T.Var ("x", 0), T.Var ("y", 0)])), F.Atom (F.Pred ("Q", [T.Var ("y", 0), T.Var ("z", 0)]))), F.Atom (F.Pred ("Q", [T.Var ("x", 0), T.Var ("z", 0)])))
fun encode filename =
    let val inStream = TextIO.openIn filename
	fun loop acc = case TextIO.inputLine inStream of
			   NONE => List.rev acc
			 | SOME line => if String.isPrefix ";" line then loop acc else loop ((String.substring (line, 1, size line - 3))::acc)
	val lines = loop []
	val _ = TextIO.closeIn inStream
	val (opt, funs, rules, problem) = splitInput lines ([], [], [], [])
	fun main (funs, rule) =
	    let val symbols = List.map (fn str => List.nth (SU.split str #" ", 1)) funs
		fun makeRule [left, right] str = (Term.toString (fromString symbols left)) ^ str ^ (Term.toString (fromString symbols right))
		  | makeRule _ _ = ""
		val (conds, rl) = List.partition (fn str => String.isPrefix "=" str) (tl (getTerms rule))
		val condsStr = List.map (fn cond => makeRule (tl (getTerms cond)) " ->* ") conds
	    in if null condsStr then print ((makeRule rl " -> ") ^ "\n") else print ((makeRule rl " -> ") ^ " <= " ^ (String.concatWith " & " condsStr) ^ "\n")
	    end
	fun main2 (funs, problem) =
	    let val symbols = List.map (fn str => List.nth (SU.split str #" ", 1)) funs
		fun makeRule [left, right] str = (Term.toString (fromString symbols left)) ^ str ^ (Term.toString (fromString symbols right))
		  | makeRule _ _ = ""		       
		val problems = tl (getTerms problem)
		val problemsStr = List.map (fn p => makeRule (tl (getTerms p)) " ->* ") problems
	    in print ((String.concatWith " & " problemsStr) ^ "\n")
	    end 
	val _ = List.map (fn rule => main (funs, rule)) rules
	val _ = print "\n"
	val _ = main2 (funs, problem)
    in ()
    end 
end
end 
