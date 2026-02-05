signature MAIN =
sig
    val main: (Trs.ctrs * Trs.reach list) -> int -> bool
end

structure Main : MAIN =
struct
local
    structure LU = ListUtil
    structure F = Form
in

fun select (ctrs, reachs) timeout =
    let val _ = print "FOL eocoding(replace '->' => 'P', '->*' => 'Q'):\n"
	val forms = Trans.getTheory ctrs @ [Trans.getInfeasibility reachs]
	val formsStr = Form.prForms forms
	val _ = print (Trs.prStatus (ctrs, reachs) ^ "==>" ^ String.substring (formsStr, 3, size formsStr - 3) ^ "--------------------\n")
    in if Criterion.proc ctrs reachs then Ages.ages forms timeout else Mace.mace forms (timeout div 2) orelse Ages.ages forms (timeout div 2)
    end																	     
fun main (ctrs, reachs) timeout =
    let val _ = print (Trs.prCRulesDef "R = " ctrs ^ "\nStart verifying whether " ^ Trs.prReachs reachs ^ " is R-infeasible.\n--------------------\n")
	val problems = Decomp.decompose (ctrs,reachs)
	val _ = print ("\n" ^ "ordering check:\n")
    in if List.exists Order.ordInf problems
       then
	   let val _ = print ("--------------------\n" ^ Trs.prReachs reachs ^ " is R-infeasible\n")
	   in true
	   end
       else
	   let val _ = print "--------------------\n"
	   in if List.exists (fn problem => select problem (timeout div (length problems))) problems
	      then
		  let val _ = print ("--------------------\n" ^ Trs.prReachs reachs ^ " is R-infeasible.\n")
		  in true
		  end
	      else
		  let val _ = print ("--------------------\n" ^ "R-infeasibility of " ^ Trs.prReachs reachs ^ " is unknown.\n")
		  in false
		  end
	   end 
    end 
	
end
end 
