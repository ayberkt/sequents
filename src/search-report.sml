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
    then indent := (!indent) - 1
    else raise Fail "indent level must not become negative"

  fun searchWithIndent f x =
    let
      val _ = upIndentLevel ()
      val result = f x
      val _ = downIndentLevel ()
    in
      result
    end

  fun bullet s = (format (Bright, Black) "* ") ^ s
  fun line s   = (format (Bright, Black) "- ") ^ s

  fun printLnWithIndent s =
    (print (replicateStr (!indent) "  ");
     printLn s)

  fun prProps' [] = ""
    | prProps' [p] = Syntax.pretty p
    | prProps' (p::ps) = Syntax.pretty p ^ ", " ^ (prProps' ps)

  fun prProps ps = "[" ^ prProps' (List.rev ps) ^ "]"

  fun prSequent' (G || O ===> C) =
    (format (Bright, White) ((prProps G) ^ "; " ^ (prProps O) ^ "  ---->  " ^ (Syntax.pretty C)))

  fun printSequent (G || O) C =
    if Flags.shouldGenLaTeX ()
    then ()
    else printLnWithIndent (bullet (prSequent' (G || O ===> C)))

  fun mkNewGoalMsg newgoal =
    let
      val green : string -> string = Color.format (Bright, Green)
      val mkMsg : sequent -> string =
        fn ngs => (green "New goal: ") ^ (prSequent' ngs)
    in
      mkMsg newgoal
    end

  fun printNewGoal newgoal =
    (upIndentLevel ();
     printLnWithIndent ((line o mkNewGoalMsg) newgoal);
     downIndentLevel ())

  fun printRule rlname =
    (upIndentLevel ();
     printLnWithIndent (line ("Apply " ^ rlname));
     downIndentLevel ())

end
