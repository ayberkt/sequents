structure ContFree = struct
  open Syntax
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  open Proofs

  fun isAtom (ATOM _) = true
    | isAtom _        = false

  fun isLeftSync (ATOM P) = true
    | isLeftSync ((ATOM P) IMPL B) = true
    | isLeftSync ((D IMPL E) IMPL B) = true
    | isLeftSync _ = false

  exception NoProof

  fun concByBotL (G || O) C = ZeroInf (BotL, (BOT::G) || O ===> C)

  fun updateCtx (G || O) A =
    if isLeftSync A then ((A::G) || O) else (G || (A::O))

  fun appConjR (G || O) A B = (G || O ===> A, G || O ===> B)

  fun appTopR (G || O) TOP = G || O ===> TOP

  fun appImplR ctx A B = (updateCtx ctx A) ===> B

  fun appConjL (G || O) (A : prop) (B : prop) (C : prop) =
    let val ctx' = updateCtx (updateCtx (G || O) A) B
    in ctx' ===> C end

  fun appTopL (G || O) C = G || O ===> C

  fun appTopImplL (G || O) B C = (updateCtx (G || O) B) ===> C

  fun disjImplL ctx D E B C =
    let val ctx' = updateCtx (updateCtx ctx (D IMPL B)) (E IMPL B)
    in ctx' ===> C end

  fun botImplL B G C = G ===> C

  fun appInit G P = List.exists (fn x => x = P) G

  fun appDisjL (G || O) A B C =
    let val ctx1 = updateCtx (G || O) A
        val ctx2 = updateCtx (G || O) B
    in (ctx1 ===> C, ctx2 ===> C) end

  fun appAtomImplL (G || O) P B C : sequent =
    if List.exists (fn x => x = P) G
    then (updateCtx (G || O) B) ===> C
    else raise NoProof

  fun appImplImplL (G || O) D E B C =
    let val ctx1 = updateCtx (updateCtx (G || O) (E IMPL B)) D
        val ctx2 = updateCtx (G || O) B
    in (ctx1 ===> E, ctx2 ===> C) end

  fun prove (G || [] ===> (ATOM X)) : derivation =
        if appInit G (ATOM X)
        then ZeroInf (Init, G || [] ===> (ATOM X))
        else raise NoProof
    | prove ((((ATOM X) IMPL B::G) || []) ===> C) =
        let val ctx = ((ATOM X) IMPL B::G) || []
            val newgoal = appAtomImplL (G || []) (ATOM X) B C
        in OneInf (AtomImplL, prove newgoal, ctx ===> C) end
    | prove (G || [] ===> BOT) = raise NoProof
    | prove (G || [] ===> (A DISJ B)) =
        (OneInf (DisjR1, prove (G || [] ===> A), G || [] ===> (A DISJ B))
         handle NoProof =>
          OneInf (DisjR2, prove (G || [] ===> B), G || [] ===> (A DISJ B)))
    | prove ((((D IMPL E) IMPL B::G) || []) ===> C) =
        let
          val goal = ((D IMPL E) IMPL B::G) || [] ===> C
          val (newgoal1, newgoal2) = appImplImplL (G || []) D E B C
        in TwoInf (ImplImplL, prove newgoal1, prove newgoal2, goal) end


end
