signature MAIN =
sig
    val main: (Trs.ctrs * Trs.reach list) -> bool
    val all: (string -> bool) -> string -> unit
end

    
fun bench label (f : 'a -> 'b) (x: 'a) : 'b =
  let
    val t = Timer.startCPUTimer ()
    val y = f x
    val {usr, ...} = Timer.checkCPUTimer t
  in
    print (label ^ " " ^ Time.toString usr ^ "\n");
    y
  end


structure Main : MAIN =
struct
local
    structure LU = ListUtil
    structure F = Form
in

fun decompose (ctrs, reachs) =
    let val reachsList = Decomp.split reachs
    in List.map (fn rc => Decomp.delete (ctrs,rc)) reachsList
    end

fun main (ctrs, reachs) =
    let val problems = decompose (ctrs,reachs)
    in if List.exists Order.ordInf problems then true else false
    end 
(*
fun main forms timeout1 timeout2 = if Inf.checkInfProp forms (IntInf.fromInt timeout1)
				   then
				       let val _ = OS.Process.sleep (Time.fromSeconds 1)
				       in Ages.ages forms timeout2
				       end 							
				   else let val _ = OS.Process.sleep (Time.fromSeconds 1)
					    in Mace.mace forms timeout2
					end
*)

fun all f directry =
    let val dir = OS.FileSys.openDir directry
	val outStream = TextIO.openOut "result.txt"
	fun read () = case OS.FileSys.readDir dir of
			  NONE => []
			| SOME file => file :: (read ())
	fun sort [] = []
	  | sort ss =
	    let val pivot = hd ss
		val rest = tl ss
		val (left, right) = List.partition (fn s => valOf (Int.fromString (String.substring (s, 0, size s - 4))) < valOf (Int.fromString (String.substring (pivot, 0, size pivot - 4)))) rest
	    in sort left @ (pivot :: sort right)
	    end
	fun loop [] = ()
	  | loop (file::rest) =
	    let val path = directry ^ "/" ^ file
		val _ = print (file ^ "\n")
		val result = f path
		val status = if result then TextIO.output (outStream, file ^ ":true\n") else TextIO.output (outStream, file ^ ":false\n") 
	    in loop rest
	    end
	val files = sort (read ())
	val _ = loop files
	val _ = OS.FileSys.closeDir dir
	val _ = TextIO.closeOut outStream
    in ()
    end
	
end
end 
