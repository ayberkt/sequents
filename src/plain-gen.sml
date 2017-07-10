structure PlainGen = struct
  structure SX = Syntax
  open Proofs
  open Syntax
  open Color
  open Utils
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>

  fun ruleName r =
    let
      fun ruleName' ConjR      = "∧R"
        | ruleName' ConjL      = "∧L"
        | ruleName' TopR       = "⊤R"
        | ruleName' ImplR      = "⊃R"
        | ruleName' Init       = "init"
        | ruleName' DisjL      = "∨L"
        | ruleName' DisjR1     = "∨R_1"
        | ruleName' DisjR2     = "∨R_2"
        | ruleName' TopL       = "⊤L"
        | ruleName' BotL       = "⊥L"
        | ruleName' ImplL      = "⊃L"
        | ruleName' AtomImplL  = "P⊃L"
        | ruleName' ConjImplL  = "∧⊃L"
        | ruleName' TopImplL   = "⊤⊃L"
        | ruleName' DisjImplL  = "∨⊃L"
        | ruleName' BotImplL   = "⊥⊃L"
        | ruleName' ImplImplL  = "⊃⊃L"
    in
      format (Bright, Yellow) (ruleName' r)
    end

  val bullet = fn s => (format (Bright, DarkGray) "• ") ^ s

  val green  = format (Bright, Green)
  val bright = format (Bright, White)

  val longarrow = "---->"

  fun prProps ps =
    let
      fun prProps' [] = ""
        | prProps' [p] = SX.pretty p
        | prProps' (p::ps) = SX.pretty p ^ ", " ^ prProps' ps
    in
      prProps' (List.rev ps)
    end

  fun showProp P = format (Bright, White) (SX.pretty P)

  fun showSequent ([] || [] ===> C) =
        bright (longarrow ^ " " ^ SX.pretty C)
    | showSequent (G || O ===> C) =
        (format
          (Bright, White)
          ((prProps (O@G)) ^ " " ^ longarrow ^ " "  ^ (SX.pretty C)))

  fun printSequent (G || O) C =
    printLn (bullet (showSequent (G || O ===> C)))

  fun reportNotProvable A =
    printLn
      (format (Bright, White) (SX.pretty A)
        ^ (format (Bright, Red) " not provable"))

  fun reportProven () =
    (printLn o format (Bright, Green)) "QED"

  fun declareTheorem P =
    printLn ((green "Theorem: ") ^ showProp P ^ (green "."))

  fun mkInference rule conc =
    "• " ^ showSequent conc ^ " by " ^ ruleName rule

  fun explain P drv : unit =
    let
      fun explain' (ZeroInf (rule, conc)) =
            printLn (mkInference rule conc)
        | explain' (OneInf (rule, D1, conc)) =
            (explain' D1; printLn (mkInference rule conc))
        | explain' (TwoInf (rule, D1, D2, conc)) =
            (explain' D1;
             print "\n";
             explain' D2;
             print "\n";
             printLn (mkInference rule conc))
    in
      (declareTheorem P; explain' drv; reportProven ())
    end

end
