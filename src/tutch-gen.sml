structure TutchGen = struct
  open Proofs
  open Utils
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>

  val level : int ref = ref 0
  fun indentLeft  () = level := (!level) + 1
  fun indentRight () = level := (!level) - 1

  local
    fun emit s = printLn ((replicateStr (!level) "  ") ^ s)

    fun showProp (ATOM X) = X
      | showProp TOP = "T"
      | showProp BOT = "F"
      | showProp (A CONJ B) = "(" ^ showProp A ^ " & " ^ showProp B ^ ")"
      | showProp (A IMPL B) = "(" ^ showProp A ^ " => " ^ showProp B ^ ")"
      | showProp (A DISJ B) = "(" ^ showProp A ^ " | " ^ showProp B ^ ")"
  in
    fun genProp A = emit (showProp A ^ ";")

    fun genStatement (G || O ===> A) =
      printLn ("proof tm : " ^ showProp A ^ " =")

    fun genOpenBracket () = emit "["

    fun genCloseBracket () = emit "];"
  end

  fun genBegin () = printLn "begin"
  fun genEnd   () = printLn "end;"

  fun generateProof (ZeroInf (Init, _ || _ ===> P)) = genProp P
    | generateProof (ZeroInf (TopR, _)) = genProp TOP
    | generateProof (OneInf (ImplR, D1, _ || _ ===> A IMPL B)) =
        (genOpenBracket ();
         indentLeft ();
         genProp A;
         generateProof D1;
         indentRight ();
         genCloseBracket ();
         genProp (A IMPL B))
    | generateProof (OneInf (ConjL, D1, (A CONJ B::_) || _ ===> C))  =
        ( genProp A; genProp B; generateProof D1)
    | generateProof (TwoInf (ConjR, D1, D2, _ || _ ===> A CONJ B))  =
        (generateProof D1; generateProof D2; genProp (A CONJ B))
    | generateProof _ = printLn "TODO"

  fun genTutch drv =
    (genStatement (getConc drv);
     genBegin ();
     generateProof drv;
     genEnd ())

end
