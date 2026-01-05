signature MAUDE =
sig
    val make: string -> unit
end

structure Maude : MAUDE =
struct
local
    structure SU = StringUtil
    structure LU = ListUtil
    structure T = Term
in

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

fun toUpper c = if Char.isLower c then Char.chr (Char.ord c - Char.ord #"a" + Char.ord #"A") else c

fun getTerms str =
    let fun main [] (acc, ts) n = if null acc then rev ts else rev (String.implode (rev acc)::ts)
	  | main (c::cs) (acc, ts) 0 = if c = #"(" then if null acc then main cs (acc, ts) 1 else main cs ([], String.implode (rev acc)::ts) 1
				       else if Char.isGraph c then main cs (c::acc, ts) 0
				       else if null acc then main cs (acc, ts) 0
				       else main cs ([], String.implode (rev acc)::ts) 0
	  | main (c::cs) (acc, ts) 1 = if c = #")" then main cs ([], String.implode (rev acc)::ts) 0
				       else if c = #"(" then main cs (c::acc, ts) 2
				       else main cs (c::acc, ts) 1
	  | main (c::cs) (acc, ts) n = if c = #"(" then main cs (c::acc, ts) (n + 1)
				       else if c = #")" then main cs (c::acc, ts) (n - 1)
				       else main cs (c::acc, ts) n
    in main (String.explode str) ([], []) 0
    end

fun split [] = raise Fail "Error"
  | split (hd::tl) = (hd,tl)

fun fromString funs str = case SU.find str #"(" of
			 SOME pos => let val (symbol, args) = split (getTerms str)
				     in T.Fun (String.map toUpper symbol, List.map (fn t => fromString funs t) args)
				     end 
		       | NONE => let val list = SU.split str #" "
				     val symbol = hd list
				     val args = tl list
				 in if LU.member symbol funs
				    then T.Fun (String.map toUpper symbol, List.map (fn t => fromString funs t) args)
				    else T.Var (Var.fromString symbol)
				 end

fun printOps [] = [] 
  | printOps ((f, k)::rest) =
    let fun sort 0 = "-> S .\n"
	  | sort k = "S " ^ sort (k - 1)
	val str = " op " ^ String.map toUpper f ^ " : " ^ sort k
    in str::printOps rest
    end

fun deleteChar ch str =
    let val cs = String.explode str
    in String.implode (List.filter (fn c => c <> ch) cs)
    end

fun printVars funs rules problem =
    let val (rl, crl) = List.partition (fn xs => length xs = 2) (List.map (fn rule => tl (getTerms rule)) rules)
	fun varsRl ([lhs, rhs]::rest) = T.vars (fromString funs lhs)::T.vars (fromString funs rhs)::varsRl rest
	  | varsRl _ = []
	fun varsCrl ((lhs::rhs::conds)::rest) =
	    let fun varsConds ([s, t]::rest) = T.vars (fromString funs s)::T.vars (fromString funs t)::varsConds rest
		  | varsConds _ = []
		val vars = T.vars (fromString funs lhs)::T.vars (fromString funs rhs)::varsConds (List.map (fn cond => tl (getTerms cond)) conds)
	    in vars @ varsCrl rest
	    end
	  | varsCrl _ = []
	fun varsProblem problem =
	    let fun main ([s, t]::rest) = T.vars (fromString funs s)::T.vars (fromString funs t)::main rest
		  | main _ = []
		val atoms = List.map (fn atom => tl (getTerms atom)) (tl (getTerms problem))
	    in main atoms
	    end 
	val varsStr = List.map (fn x => Var.toString x) (LU.unions (varsRl rl @ varsCrl crl @ varsProblem problem))
    in " vars " ^ String.concatWith " " varsStr ^ " : S .\n"
    end

fun printRules funs rules =
    let val (rl, crl) = List.partition (fn xs => length xs = 2) (List.map (fn rule => tl (getTerms rule)) rules)
	fun printRl ([lhs, rhs]::rest) =
	    let val str = " rl " ^ deleteChar #"?" (T.toString (fromString funs lhs)) ^ " => " ^ deleteChar #"?" (T.toString (fromString funs rhs)) ^ ".\n"
	    in str::printRl rest
	    end 
	  | printRl _ = []
	fun printCrl ((lhs::rhs::conds)::rest) =
	    let val str = " crl " ^ deleteChar #"?" (T.toString (fromString funs lhs)) ^ " => " ^ deleteChar #"?" (T.toString (fromString funs rhs))
		fun toStringConds ([s,t]::rest) = (deleteChar #"?" (T.toString (fromString funs s)) ^ " => " ^ deleteChar #"?" (T.toString (fromString funs t)))::toStringConds rest
		  | toStringConds _ = []
		val strConds = " if " ^ String.concatWith " /\\ " (toStringConds (List.map (fn cond => tl (getTerms cond)) conds)) ^ " .\n"
	    in (str ^ strConds)::printCrl rest
	    end
	  | printCrl _ = []
    in printRl rl @ printCrl crl
    end

fun printGoal funs problem =
    let val atoms = tl (getTerms problem)
	val conds = List.map (fn atom => tl (getTerms atom)) atoms
	fun main ([s, t]::rest) = (deleteChar #"?" (T.toString (fromString funs s)) ^ " ->* " ^ deleteChar #"?" (T.toString (fromString funs t)))::main rest
	  | main _ = []
    in "~(" ^ (String.concatWith " /\\ " (main conds)) ^ ")\n"
    end 

fun splitInput [] (opt, funs, rules, problem) = (hd opt, rev funs, rev rules, hd problem)
  | splitInput (line::rest) (opt, funs, rules, problem) = if String.isPrefix "format" line then splitInput rest (line::opt, funs, rules, problem)
							  else if String.isPrefix "fun" line then splitInput rest (opt, line::funs, rules, problem)
							  else if String.isPrefix "rule" line then splitInput rest (opt, funs, line::rules, problem)
							  else  splitInput rest (opt, funs, rules, line::problem)
									   
fun r filename =
    let val inStream = TextIO.openIn filename
	fun loop acc = case TextIO.inputLine inStream of
			   NONE => List.rev acc
			 | SOME line => if String.isPrefix ";" line then loop acc else loop ((String.substring (line, 1, size line - 3))::acc)
	val lines = loop []
	val _ = TextIO.closeIn inStream
    in splitInput lines ([], [], [], [])
    end

fun w (opt, funs, rules, problem) =
    let val outStream = TextIO.openOut "maude.txt"
	fun loop [] = ()
	  | loop (line::rest) =
	    let val _ = TextIO.output (outStream, line)
	    in loop rest
	    end 
	val _ = TextIO.output (outStream, "mod EX is\n sort S .\n")
	val _ = loop (printOps (getSymbols funs []))
	val _ = TextIO.output (outStream, printVars (List.map (fn str => List.nth (SU.split str #" ", 1)) funs) rules problem)
	val _ = loop (printRules (List.map (fn str => List.nth (SU.split str #" ", 1)) funs) rules)
	val _ = TextIO.output (outStream, "endm .\n")
	val _ = TextIO.output (outStream, printGoal (List.map (fn str => List.nth (SU.split str #" ", 1)) funs) problem)
	val _ = TextIO.closeOut outStream
    in ()
    end

fun make filename = (w o r) filename
end
end 
