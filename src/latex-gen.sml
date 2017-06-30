structure LaTeXGen = struct
  open InvCalc
  structure U = Unparse
  structure TIO = TextIO

  infixr 5 ||
  infixr 4 SeqL
  infixr 4 SeqR
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
    fun ruleName' ConjR     = "\\wedge R"
      | ruleName' ConjL     = "\\wedge L"
      | ruleName' TopR      = "\\top R"
      | ruleName' ImplR     = "\\supset R"
      | ruleName' InitR     = "\\mathsf{init}"
      | ruleName' InitL     = "\\mathsf{init}"
      | ruleName' DisjL     = "\\vee L"
      | ruleName' DisjR1    = "\\vee R_1"
      | ruleName' DisjR2    = "\\vee R_2"
      | ruleName' TopL      = "\\top L"
      | ruleName' BotL      = "\\bot L"
      | ruleName' ImplL     = "\\supset L"
  in
    fun ruleName r = "\\rlname{" ^ ruleName' r ^ "}"
  end

  fun propToItem (ATOM P) = U.atom P
    | propToItem (A CONJ B) =
        U.infix' (U.Non, 3, "\\wedge") (propToItem A, propToItem B)
    | propToItem (A DISJ B) =
        U.infix' (U.Non, 2, "\\vee") (propToItem A, propToItem B)
    | propToItem (A IMPL B) =
        U.infix' (U.Right, 1, "\\supset") (propToItem A, propToItem B)

  local
  in
    fun genProp A = U.parens o U.done o propToItem $ A
  end

  fun intersperse y [] = []
    | intersperse y [x] = [x]
    | intersperse y (x::xs)=x::y::(intersperse y xs)

  local
    open String
    fun showProps PS = concat o (intersperse ", ") $ genProp <$> PS
  in
    fun mkCtx (G  || O) = showProps $ G @ O
  end

  fun mkSequent (CTX SeqR C) = (mkCtx CTX) ^ " \\Longrightarrow " ^ (genProp C)
    | mkSequent (CTX SeqL C) = (mkCtx CTX) ^ " \\Longrightarrow " ^ (genProp C)

  fun mkInfer n rname seq =
    "\\infer" ^ Int.toString n ^
      "[$" ^ ruleName rname ^ "$]" ^ (* The rule name. *)
       (* The proposition that is being inferred. *)
      "{"  ^ mkSequent seq  ^  "}"

  fun genDrv (ZeroInf (r, seq)) = writeLn $ mkInfer 0 r seq
    | genDrv (OneInf (r, d, seq)) = (genDrv d; writeLn $ mkInfer 1 r seq)
    | genDrv (TwoInf (r, d1, d2, seq)) = (genDrv d1; genDrv d2; writeLn $ mkInfer 2 r seq)
    | genDrv _ = raise Fail "genDrv TODO"

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
