structure LaTeXGen = struct
  open InvCalc
  structure TIO = TextIO

  fun $ (f, x) = f x
  infix 0 $

  val preamble = TextIO.openIn "resources/preamble.tex"

  val out = TextIO.openOut "proof.tex"

  fun write s = (TextIO.output (out, s); TextIO.flushOut)

  fun copyBeforeProof strm =
    let
      val line = valOf $ TIO.inputLine strm
    in
      if String.isPrefix "  %% START" line
      then strm
      else (write line; copyBeforeProof strm)
    end

  fun copyAfterProof strm =
    if TIO.endOfStream strm
    then ()
    else (write o valOf o TIO.inputLine $ strm;
          copyAfterProof strm)

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

  local
    open TextIO
  in
    val _ =
      let
        val strm = copyBeforeProof preamble
      in
        (print o valOf o inputLine $ strm;
        (* Write the proof here. *)
        write "foo\n";
        write "bar\n";
        copyAfterProof strm)
      end
  end

end
