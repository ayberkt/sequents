structure CoqGen = struct
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  open Proofs

  fun tacticOf ConjR = "split"
    | tacticOf ConjL = raise Fail "TODO"
    | tacticOf TopR = "trivial"
    | tacticOf ImplR = raise Fail "TODO"
    | tacticOf ImplL = raise Fail "TODO"
    | tacticOf Init = raise Fail "TODO"
    | tacticOf DisjL = raise Fail "TODO"
    | tacticOf DisjR1 = raise Fail "TODO"
    | tacticOf DisjR2 = raise Fail "TODO"
    | tacticOf TopL = raise Fail "TODO"
    | tacticOf BotL = raise Fail "TODO"
    | tacticOf AtomImplL = raise Fail "TODO"
    | tacticOf ConjImplL = raise Fail "TODO"
    | tacticOf TopImplL = raise Fail "TODO"
    | tacticOf DisjImplL = raise Fail "TODO"
    | tacticOf BotImplL = raise Fail "TODO"
    | tacticOf ImplImplL = raise Fail "TODO"

  fun coqProp (ATOM X) = X
    | coqProp TOP = "True"
    | coqProp BOT = "False"
    | coqProp (A CONJ B) = coqProp A ^ " /\\ " ^ coqProp B
    | coqProp (A DISJ B) = coqProp A ^ " \\/ " ^ coqProp B
    | coqProp (A IMPL B) = coqProp A ^ " ->  " ^ coqProp B

  fun mkTheorem P = "Theorem foo : " ^ coqProp P ^ "."

  fun genTheoremStatement P = print (mkTheorem P ^ "\n")

  fun genTactic r = print (tacticOf r ^ ".\n")

  fun genTactics (ZeroInf (r, _)) = genTactic r
    | genTactics (OneInf (r, _, _)) = genTactic r
    | genTactics _ = raise Fail "TODO"

  fun generateCoq P drv =
    (genTheoremStatement P;
     genTactics drv)

end
