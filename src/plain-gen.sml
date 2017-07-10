structure PlainGen = struct
  structure SX = Syntax

  fun prProps ps =
    let
      fun prProps' [] = ""
        | prProps' [p] = SX.pretty p
        | prProps' (p::ps) = SX.pretty p ^ ", " ^ prProps' ps
    in
      prProps' (List.rev ps)
    end

  fun prSequent' ([] || [] ===> C) =
        format (Bright, White ) (" ---> " ^ (SX.pretty C))
    | prSequent' (G || O ===> C) =
        (format (Bright, White) ((prProps (O@G)) ^ " ----> " ^ (SX.pretty C)))

  fun printSequent (G || O) C =
    if Flags.shouldGenLaTeX ()
    then ()
    else reportLn (bullet (nts ^ " " ^  prSequent' (G || O ===> C)))

end
