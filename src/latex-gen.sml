structure LaTeXGen = struct
  open InvCalc
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

  local
    fun genProp' (ATOM P) = P
      | genProp' (A CONJ B) = (genProp' A) ^ " \\wedge " ^ (genProp' B)
      | genProp' (A DISJ B) = (genProp' A) ^ " \\vee " ^ (genProp' B)
      | genProp' (A IMPL B) = (genProp' A) ^ " \\supset " ^ (genProp' B)
      | genProp' TOP = "\\top"
      | genProp' BOT = "\\bot"
    fun pars s = "(" ^ s ^ ")"
  in
    fun genProp (ATOM P) = P
      | genProp ((ATOM A) DISJ (ATOM B)) = (genProp' (ATOM A)) ^ " \\vee " ^ (genProp' (ATOM B))
      | genProp ((ATOM A) CONJ (ATOM B)) = (genProp' (ATOM A)) ^ " \\wedge " ^ (genProp' (ATOM B))
      | genProp ((ATOM A) IMPL (ATOM B)) = (genProp' (ATOM A)) ^ " \\supset " ^ (genProp' (ATOM B))
      | genProp (A CONJ B) = (pars $ genProp' A) ^ " \\wedge " ^ (pars $ genProp' B)
      | genProp (A DISJ B) = (pars $ genProp' A) ^ " \\vee " ^ (pars $ genProp' B)
      | genProp (A IMPL B) = (pars $ genProp' A) ^ " \\supset " ^ (pars $ genProp' B)
      | genProp TOP = "\\top"
      | genProp BOT = "\\bot"
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
        ((* Write the proof here. *)
        genDrv drv;
        copyAfterProof preamble;
        TextIO.closeOut out)
      end
  end

end
