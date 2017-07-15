structure CoqGen = struct
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  structure L = List
  open Proofs
  open Utils

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

  fun getId n = if n > 0 then "H" ^ (Int.toString (n-1)) else "H"

  fun genTactics (ZeroInf (TopR, _)) = genTactic "trivial"
    | genTactics (ZeroInf (BotL, _)) = genTactic "destruct void"
    | genTactics (ZeroInf (Init, _ || _ ===> ATOM X)) =
        genTactic "assumption"
    | genTactics (OneInf (TopL, D1, _)) = genTactics D1
    | genTactics (OneInf (ImplR, D1, _ || _ ===> (ATOM X) IMPL C)) =
        (genTactic ("intro p" ^ X); genTactics D1)
    | genTactics (OneInf (ImplR, D1, _ || _ ===> BOT IMPL _)) =
        (genTactic "intro void"; genTactics D1)
    | genTactics (OneInf (DisjR1, D1, _)) =
        (genTactic "left"; genTactics D1)
    | genTactics (OneInf (DisjR2, D1, _)) =
        (genTactic "right"; genTactics D1)
    | genTactics (OneInf (ImplR, D1, _)) =
        (genTactic "intro"; genTactics D1)
    | genTactics (OneInf (ConjL, D1, _)) =
        (genTactic "destruct H"; genTactics D1)
    | genTactics (TwoInf (ConjR, D1, D2, _)) =
        (genTactic "split"; genTactics D1; genTactics D2)
    | genTactics (OneInf (ConjImplL, D1, _ || _ ===> C)) =
        genTactic "TODO"
    | genTactics _ = genTactic "admit"

  fun genProofStart () = print "Proof.\n"
  fun genQed () = print "Qed.\nCheck foo.\n"
  fun indent s = "  " ^ s

  fun generateCoq A drv =
    let
      val vars = (nub o vars) A
      val mkIntro = fn s => "intro " ^ s ^ ". "
      val varIntros = (indent o String.concat) (L.map mkIntro vars)
    in
      (genTheoremStatement A;
       genProofStart ();
       printLn varIntros;
       genTactics drv;
       genQed ())
    end

end
