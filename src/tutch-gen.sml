structure TutchGen = struct
  open Proofs
  open Utils
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>

  fun genProp (ATOM X) = X
    | genProp TOP = "T"
    | genProp BOT = "F"
    | genProp (A CONJ B) = "(" ^ genProp A ^ " & " ^ genProp B ^ ")"
    | genProp (A IMPL B) = "(" ^ genProp A ^ " => " ^ genProp B ^ ")"
    | genProp (A DISJ B) = "(" ^ genProp A ^ " | " ^ genProp B ^ ")"

  fun genStatement (G || O ===> A) =
    printLn ("proof tm : " ^ genProp A ^ " =")

  fun genBegin () = printLn "begin"
  fun genEnd   () = printLn "end;"
  fun indent s = "  " ^ s

  fun generateProof (ZeroInf (TopR, _)) = genProp TOP
    | generateProof (TwoInf (ConjR, D1, D2, _ || _ ===> A CONJ B))  =
        (generateProof D1; generateProof D2; genProp (A CONJ B))

  fun genTutch drv =
    (genStatement (getConc drv);
     genBegin ();
     generateProof drv;
     genEnd ())

end
