structure LaTeXGen = struct
  open InvCalc

  fun $ (f, x) = f x
  infix 0 $

  val out = TextIO.openOut "proof.tex"
  fun write s = (TextIO.output (out, s ^ "\n"); TextIO.flushOut)

  fun ruleName ConjR     = "\\wedge R"
    | ruleName ConjL     = "\\wedge L"
    | ruleName TopR      = "\\top R"
    | ruleName ImplR     = "\\supset R"
    | ruleName InitR     = "\\mathsf{init}"
    | ruleName InitL     = "\\mathsf{init}"
    | ruleName AtomRtoL  = "\\mathsf{LR}_P"
    | ruleName DisjRtoL  = "\\mathsf{LR}_\\vee"
    | ruleName TopRtoL   = "\\mathsf{LR}_\\top"
    | ruleName DisjL     = "\\vee L"
    | ruleName DisjR1    = "\\vee R_1"
    | ruleName DisjR2    = "\\vee R_2"
    | ruleName AtomShift = "\\mathsf{shift}_P"
    | ruleName ImplShift = "\\mathsf{shift}_\\supset"
    | ruleName TopL      = "\\top L"
    | ruleName BotL      = "\\bot L"
    | ruleName BotRtoL   = "\\mathsf{LR}_\\bot"
    | ruleName ImplL     = "\\supset L"


  fun genZeroInf r P =
    write $ "\\infer0[" ^ ruleName r ^ "]{" ^ Syntax.pretty P ^ "}"

  fun genLaTeX (ZeroInf (r, A)) = genZeroInf r A
    | genLaTeX _ = raise Fail "genLaTeX TODO"

  val _ = genLaTeX (ZeroInf (ConjR, ATOM "A"))

end
