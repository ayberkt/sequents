structure LaTeXGen = struct
  open InvCalc

  fun $ (f, x) = f x
  infix 0 $

  val out = TextIO.openOut "proof.tex"
  fun write s = (TextIO.output (out, s ^ "\n"); TextIO.flushOut)

  fun genRuleName ConjR = "\\wedge R"
    | genRuleName ConjL = "\\wedge L"
    | genRuleName TopR = "\\top R"
    | genRuleName ImplR = "\\supset R"
    | genRuleName InitR = "\\mathsf{init}"
    | genRuleName InitL = "\\mathsf{init}"
    | genRuleName AtomRtoL = "\\mathsf{LR}_P"
    | genRuleName DisjRtoL = "\\mathsf{LR}_\\vee"
    | genRuleName TopRtoL  = "\\mathsf{LR}_\\top"
    | genRuleName DisjL = "\\vee L"
    | genRuleName DisjR1 = "\\vee R_1"
    | genRuleName DisjR2 = "\\vee R_2"
    | genRuleName AtomShift = "\\mathsf{shift}_P"
    | genRuleName ImplShift = "\\mathsf{shift}_\\supset"
    | genRuleName TopL = "\\top L"
    | genRuleName BotL = "\\bot L"
    | genRuleName BotRtoL = "\\mathsf{LR}_\\bot"
    | genRuleName ImplL = "\\supset L"


  fun genZeroInf r P =
    write $ "\\infer0[" ^ genRuleName r ^ "]{" ^ Syntax.pretty P ^ "}"

  fun genLaTeX (ZeroInf (r, A)) = genZeroInf r A
    | genLaTeX _ = raise Fail "genLaTeX TODO"

  val _ = genLaTeX (ZeroInf (ConjR, ATOM "A"))

end
