structure SearchReport = struct
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  open Syntax
  open Utils
  open Color
  open Proofs

  val indent : int ref = ref 0

  fun upIndentLevel () = indent := !indent + 1

  val nts = format (Bright, Yellow) "NTS"

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

  fun bullet s = (format (Bright, DarkGray) "• ") ^ s
  fun line s   = (format (Bright, DarkGray) "- ") ^ s

  fun brackets s = "[" ^ s ^ "]"

  fun reportLn s =
    if not (Flags.shouldGenLaTeX ())
    then
      (print (replicateStr (!indent) "  ");
       print (s ^ "\n"))
    else ()

  fun prProps' [] = ""
    | prProps' [p] = Syntax.pretty p
    | prProps' (p::ps) = Syntax.pretty p ^ ", " ^ (prProps' ps)

  fun prProps ps = prProps' (List.rev ps)

  fun prSequent' ([] || [] ===> C) =
        format (Bright, White ) (" ---> " ^ (Syntax.pretty C))
    | prSequent' (G || O ===> C) =
        (format (Bright, White) ((prProps (O@G)) ^ " ----> " ^ (Syntax.pretty C)))

  fun printSequent (G || O) C =
    if Flags.shouldGenLaTeX ()
    then ()
    else reportLn (bullet (nts ^ " " ^  prSequent' (G || O ===> C)))

  fun mkNewGoalMsg newgoal =
    let
      val yellow : string -> string = Color.format (Bright, Yellow)
      val mkMsg : sequent -> string =
        fn ngs => (yellow "New goal: ") ^ (prSequent' ngs)
    in
      mkMsg newgoal
    end

  fun reportNotProvable () =
    (upIndentLevel ();
     (reportLn o line) (format (Bright, Red) "Proposition not provable.");
     downIndentLevel ())

  fun reportProven () =
    (upIndentLevel ();
    (reportLn o line o (format (Bright, Green))) "QED";
    downIndentLevel ())

  fun printNewGoal newgoal =
    (upIndentLevel ();
     reportLn ((line o mkNewGoalMsg) newgoal);
     downIndentLevel ())

  fun reportRemark s =
    (upIndentLevel ();
     (reportLn o line) (colorize LightCyan "Note: " ^ s);
     downIndentLevel ())

  fun printRule rlname =
    (upIndentLevel ();
     reportLn (line ("Apply " ^ rlname ^ "."));
     downIndentLevel ())

end
