structure CoqGen = struct
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  open Proofs
  open Utils

  (*fun tacticOf ConjR = "split"
    | tacticOf ConjL = "destruct H"
    | tacticOf TopR = "trivial"
    | tacticOf ImplR = "intros"
    | tacticOf ImplL = "TODO"
    | tacticOf Init = "auto"
    | tacticOf DisjL = raise Fail "TODO"
    | tacticOf DisjR1 = raise Fail "TODO"
    | tacticOf DisjR2 = raise Fail "TODO"
    | tacticOf TopL = ""
    | tacticOf BotL = raise Fail "TODO"
    | tacticOf AtomImplL = raise Fail "TODO"
    | tacticOf ConjImplL = raise Fail "TODO"
    | tacticOf TopImplL = raise Fail "TODO"
    | tacticOf DisjImplL = raise Fail "TODO"
    | tacticOf BotImplL = raise Fail "TODO"
    | tacticOf ImplImplL = raise Fail "TODO"*)

  fun vars (ATOM X) = [X]
    | vars TOP = []
    | vars BOT = []
    | vars (A CONJ B) = vars A @ vars B
    | vars (A IMPL B) = vars A @ vars B
    | vars (A DISJ B) = vars A @ vars B

  val quantify : string list -> string =
    let
      fun annotate s = "(" ^ s ^ " : Prop)"
    in
      fn ss => "forall " ^ (String.concat (intersperse " " (List.map annotate (nub ss)))) ^ ", "
    end

  fun isGround (ATOM _) = false
    | isGround TOP = true
    | isGround BOT = true
    | isGround (A CONJ B) = isGround A andalso isGround B
    | isGround (A DISJ B) = isGround A andalso isGround B
    | isGround (A IMPL B) = isGround A andalso isGround B

  fun coqProp (ATOM X) = X
    | coqProp TOP = "True"
    | coqProp BOT = "False"
    | coqProp (A CONJ B) = "(" ^ coqProp A ^ " /\\ " ^ coqProp B ^ ")"
    | coqProp (A DISJ B) = "(" ^ coqProp A ^ " \\/ " ^ coqProp B ^ ")"
    | coqProp (A IMPL B) = "(" ^ coqProp A ^ " ->  " ^ coqProp B ^ ")"

  fun mkTheorem A =
    if isGround A
    then "Theorem foo : " ^ coqProp A ^ "."
    else "Theorem foo : " ^ quantify (vars A) ^ coqProp A ^ "."

  fun genTheoremStatement P = print (mkTheorem P ^ "\n")

  fun genTactic s = print ("  " ^ s ^ ".\n")

  fun genTactics (ZeroInf (TopR, _)) _ = genTactic "trivial"
    | genTactics (ZeroInf (BotL, _)) _ = genTactic "destruct void"
    | genTactics (ZeroInf (Init, _)) _ = genTactic "auto"
    | genTactics (OneInf (ImplR, D1, _ || _ ===> BOT IMPL _)) n =
        (genTactic "intros void"; genTactics D1 n)
    | genTactics (OneInf (DisjR1, D1, _)) n =
        (genTactic "left"; genTactics D1 n)
    | genTactics (OneInf (DisjR2, D1, _)) n =
        (genTactic "right"; genTactics D1 n)
    | genTactics (OneInf (ImplR, D1, _)) n =
        (genTactic "intros"; genTactics D1 n)
    | genTactics (OneInf (ConjL, D1, _)) n =
        if n > 0
        then
          (genTactic ("destruct H" ^ (Int.toString (n-1)));
           genTactics D1 (n+1))
        else
          (genTactic "destruct H";
           genTactics D1 (n+1))
    | genTactics (TwoInf (ConjR, D1, D2, _)) n =
        (genTactic "split"; genTactics D1 n; genTactics D2 n)
    | genTactics _ _ = (print "TODO\n"; raise Fail "TODO")

  fun genProofStart () = print "Proof.\n"
  fun genQed () = print "Qed.\n"

  fun generateCoq P drv =
    (genTheoremStatement P;
     genProofStart ();
     genTactics drv 0;
     genQed ())

end
