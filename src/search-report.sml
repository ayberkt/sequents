structure SearchReport = struct
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  open Syntax
  open Utils
  open Color
  open Proofs

  val indent : int ref = ref 0

  fun upIndentLevel () = indent := !indent + 1

  fun downIndentLevel () =
    if !indent > 0
    then indent := !indent - 1
    else raise Fail "indent level must not become negative"

  fun searchWithIndent f x =
    let
      val _ = upIndentLevel ()
      val result = f x
      val _ = downIndentLevel ()
    in
      result
    end

  fun bullet s = (format (Bright, White) "• ") ^ s
  fun line s = (format (Bright, White) "- ") ^ s

  fun printLnWithIndent s =
    (print (replicateStr (!indent) "   ");
     printLn s)

  fun prProps' [] = ""
    | prProps' [p] = Syntax.pretty p
    | prProps' (p::ps) = Syntax.pretty p ^ ", " ^ (prProps' ps)

  fun prProps ps = "[" ^ prProps' (List.rev ps) ^ "]"

  fun prSequent G O C =
    (print (replicateStr (!indent) "    ");
    format (Bright, White) ((prProps G) ^ "; " ^ (prProps O) ^ "  ---->  " ^ (Syntax.pretty C)))

  fun printSequent (G || O) C =
    if Flags.shouldGenLaTeX ()
    then ()
    else printLnWithIndent (bullet (prSequent G O C))

  fun prSequent' (G || O ===> C) =
    (print (replicateStr (!indent) "    ");
    format (Bright, White) ((prProps G) ^ "; " ^ (prProps O) ^ "  ---->  " ^ (Syntax.pretty C)))

  fun mkNewGoalMsg (newgoal1, newgoal2) =
    let
      val green : string -> string = Color.format (Bright, Green)
      val mkMsg : sequent * sequent -> string =
        fn (ngs1, ngs2) =>
          (green "New subgoals: ")
            ^ (prSequent' ngs1) ^ (green " and ") ^ (prSequent' ngs2)
    in
      mkMsg (newgoal1, newgoal2)
    end

  fun printNewGoals (newgoal1, newgoal2) =
    printLnWithIndent ((bullet o mkNewGoalMsg) (newgoal1, newgoal2))

  fun printMsg s =
    if Flags.shouldGenLaTeX ()
    then ()
    else
      (print (replicateStr (!indent) "   ");
       printLn (format (Bright, Yellow) ("  -- " ^ s)))

end
