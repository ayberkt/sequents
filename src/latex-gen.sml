structure LaTeXGen = struct
  open InvCalc
  structure TIO = TextIO

  fun $ (f, x) = f x
  infix 0 $

  val out = TextIO.stdOut

  fun write s = (TextIO.output (out, s); TextIO.flushOut)

  fun writeLn s = write $ "  " ^ s ^ "\n"

  fun copyBeforeProof strm =
    if TIO.endOfStream strm
    then (print "End of stream\n"; ())
    else
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
      | ruleName' AtomRtoL  = "\\mathsf{LR}_P"
      | ruleName' DisjRtoL  = "\\mathsf{LR}_\\vee"
      | ruleName' TopRtoL   = "\\mathsf{LR}_\\top"
      | ruleName' DisjL     = "\\vee L"
      | ruleName' DisjR1    = "\\vee R_1"
      | ruleName' DisjR2    = "\\vee R_2"
      | ruleName' AtomShift = "\\mathsf{shift}_P"
      | ruleName' ImplShift = "\\mathsf{shift}_\\supset"
      | ruleName' TopL      = "\\top L"
      | ruleName' BotL      = "\\bot L"
      | ruleName' BotRtoL   = "\\mathsf{LR}_\\bot"
      | ruleName' ImplL     = "\\supset L"
  in
    fun ruleName r = "\\rlname{" ^ ruleName' r ^ "}"
  end

  fun genProp (ATOM P) = P
    | genProp (CONJ (A, B)) = (genProp A) ^ " \\wedge " ^ (genProp A)
    | genProp (DISJ (A, B)) = (genProp A) ^ " \\vee " ^ (genProp A)
    | genProp (IMPL (A, B)) = (genProp A) ^ " \\supset " ^ (genProp A)
    | genProp TOP = "\\top"
    | genProp BOT = "\\bot"


  fun genInf 0 r A =
        writeLn $ "\\infer0[$" ^ ruleName r ^ "$]{" ^ genProp A ^ "}"
    | genInf n r _ =
        writeLn $ "\\infer" ^ Int.toString n ^ "[$" ^ ruleName r ^ "$]{" ^ "TODO" ^ "}"

  fun genProof (ZeroInf (r, A)) = genInf 0 r A
    | genProof (OneInf (r, d)) = (genProof d; genInf 1 r TOP)
    | genProof (TwoInf (r, d1, d2)) = (genProof d1; genProof d2; genInf 2 r TOP)
    | genProof _ = raise Fail "genProof TODO"

  local
    open TextIO
  in
    fun generate drv =
      let
        val preamble = TextIO.openIn "resources/preamble.tex"
        val _ = copyBeforeProof preamble
      in
        ((* Write the proof here. *)
        genProof drv;
        copyAfterProof preamble;
        TextIO.closeOut out)
      end
  end

end
