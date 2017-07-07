structure LaTeXGen = struct
  open InvCalc
  structure U = Unparse
  structure TIO = TextIO

  infixr 5 ||
  infixr 4 ===>
  infixr 6 CONJ
  infixr 6 DISJ
  infixr 6 IMPL

  fun $ (f, x) = f x
  infix 0 $

  fun <$> (f, xs) = List.map f xs
  infix 1 <$>

  val out = TextIO.stdOut

  fun write s = (TextIO.output (out, s); TextIO.flushOut)

  fun writeLn s = write $ "  " ^ s ^ "\n"

  fun copyBeforeProof strm =
    case TIO.inputLine strm of
      SOME line =>
        (if String.isPrefix "  %% START" line
        then (writeLn "%% STARTING GENERATING CODE"; ())
        else (write line; copyBeforeProof strm))
    | NONE => print "Could not copy before proof.\n"

  fun copyAfterProof strm =
    if TIO.endOfStream strm
    then (TIO.closeIn strm; ())
    else (write o valOf o TIO.inputLine $ strm;
          copyAfterProof strm)

  local
    fun ruleName' ConjR      = "{\\wedge}R"
      | ruleName' ConjL      = "{\\wedge}L"
      | ruleName' TopR       = "{\\top}R"
      | ruleName' ImplR      = "{\\supset}R"
      | ruleName' Init       = "\\mathsf{init}"
      | ruleName' DisjL      = "{\\vee}L"
      | ruleName' DisjR1     = "{\\vee}R_1"
      | ruleName' DisjR2     = "{\\vee}R_2"
      | ruleName' TopL       = "{\\top}L"
      | ruleName' BotL       = "{\\bot}L"
      | ruleName' ImplL      = "{\\supset}L"
      | ruleName' AtomImplL  = "P{\\supset}L"
      | ruleName' ConjImplL  = "\\wedge\\supset L"
      | ruleName' TopImplL   = "\\top\\supset L"
      | ruleName' DisjImplL  = "\\vee\\supset L"
      | ruleName' BotImplL   = "\\bot\\supset L"
      | ruleName' ImplImplL  = "\\supset\\supset L"
  in
    fun ruleName r = "\\rlname{" ^ ruleName' r ^ "}"
  end

  fun mkItem (ATOM P) = U.atom P
    | mkItem (A CONJ B) = U.infix' (U.Right, 3, "\\wedge") (mkItem A, mkItem B)
    | mkItem TOP = U.atom "\\top"
    | mkItem (A DISJ B) = U.infix' (U.Non, 2, "\\vee") (mkItem A, mkItem B)
    | mkItem BOT = U.atom "\\bot"
    | mkItem (A IMPL B) = U.infix' (U.Right, 1, "\\supset") (mkItem A, mkItem B)

  val genProp = U.parens o U.done o mkItem

  fun intersperse y [] = []
    | intersperse y [x] = [x]
    | intersperse y (x::xs)=x::y::(intersperse y xs)

  local
    open String
    fun showProps PS = concat o (intersperse ", ") $ genProp <$> (List.rev PS)
  in
    fun mkCtx (G  || O) = showProps $ G @ O
  end

  fun mkSequent (CTX ===> C) = (mkCtx CTX) ^ " \\Longrightarrow " ^ (genProp C)

  fun mkInfer n rname seq =
    "\\infer" ^ Int.toString n ^
      "[$" ^ ruleName rname ^ "$]" ^ (* The rule name. *)
       (* The proposition that is being inferred. *)
      "{"  ^ mkSequent seq  ^  "}"

  fun genDrv (ZeroInf (r, seq)) = writeLn $ mkInfer 0 r seq
    | genDrv (OneInf (r, d, seq)) = (genDrv d; writeLn $ mkInfer 1 r seq)
    | genDrv (TwoInf (r, d1, d2, seq)) = (genDrv d1; genDrv d2; writeLn $ mkInfer 2 r seq)

  local
    open TextIO
  in
    fun generate drv =
      let
        val preamble = TextIO.openIn "resources/preamble.tex"
        val _ = copyBeforeProof preamble
      in
        (genDrv drv;
        copyAfterProof preamble;
        TextIO.closeOut out)
      end
  end

end
