structure PlainGen = struct
  structure SX = Syntax
  open Proofs
  open Syntax
  open Color
  open Utils
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>

  local
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
    fun ruleName r = "\\rlname{" ^ ruleName' r ^ "}"
  end

  fun bullet s = (format (Bright, DarkGray) "• ") ^ s
  fun line s   = (format (Bright, DarkGray) "- ") ^ s

  val longarrow = "---->"

  fun prProps ps =
    let
      fun prProps' [] = ""
        | prProps' [p] = SX.pretty p
        | prProps' (p::ps) = SX.pretty p ^ ", " ^ prProps' ps
    in
      prProps' (List.rev ps)
    end

  fun showSequent ([] || [] ===> C) =
        format (Bright, White) (longarrow ^ SX.pretty C)
    | showSequent (G || O ===> C) =
        (format
          (Bright, White)
          ((prProps (O@G)) ^ " " ^ longarrow ^ " "  ^ (SX.pretty C)))

  fun printSequent (G || O) C =
    if Flags.shouldGenLaTeX ()
    then ()
    else printLn (bullet (showSequent (G || O ===> C)))

  fun mkInference rule conc =
    "Infer " ^ showSequent conc ^ " by " ^ ruleName rule

  fun generate (ZeroInf (rule, conc)) =
        printLn (mkInference rule conc)
    | generate (OneInf (rule, D1, conc)) = raise Fail "TODO"
end
