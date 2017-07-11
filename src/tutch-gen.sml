structure TutchGen = struct
  open Proofs
  open Utils
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>

  fun showProp (ATOM X) = X
    | showProp TOP = "T"
    | showProp BOT = "F"
    | showProp (A CONJ B) = "(" ^ showProp A ^ " & " ^ showProp B ^ ")"
    | showProp (A IMPL B) = "(" ^ showProp A ^ " => " ^ showProp B ^ ")"
    | showProp (A DISJ B) = "(" ^ showProp A ^ " | " ^ showProp B ^ ")"

  fun indent s = "  " ^ s

  fun genProp A = (printLn o indent) (showProp A ^ ";")

  fun genStatement (G || O ===> A) =
    printLn ("proof tm : " ^ showProp A ^ " =")

  fun genBegin () = printLn "begin"
  fun genEnd   () = printLn "end;"

  fun generateProof (ZeroInf (TopR, _)) = genProp TOP
    | generateProof (TwoInf (ConjR, D1, D2, _ || _ ===> A CONJ B))  =
        (generateProof D1; generateProof D2; genProp (A CONJ B))

  fun genTutch drv =
    (genStatement (getConc drv);
     genBegin ();
     generateProof drv;
     genEnd ())

end
