structure LJT = struct
  open Syntax
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  open Proofs

  fun isLeftSync (ATOM _) = true
    | isLeftSync ((ATOM _) IMPL _) = true
    | isLeftSync ((_ IMPL _) IMPL _) = true
    | isLeftSync _ = false

  exception NoProof

  fun concludeWithBotL (G || O) C = ZeroInf (BotL, (BOT::G) || O ===> C)

  fun insrt (G || O) A =
    if isLeftSync A then (A::G) || O else G || (A::O)

  fun appConjR (G || O) A B = (G || O ===> A, G || O ===> B)

  fun appImplR ctx A B = (insrt ctx A) ===> B

  fun appConjL (G || O) (A : prop) (B : prop) (C : prop) =
    let val ctx' = insrt (insrt (G || O) A) B
    in ctx' ===> C end

  fun appTopL (G || O) C = G || O ===> C

  fun appTopImplL (G || O) B C = (insrt (G || O) B) ===> C

  fun appDisjImplL ctx D E B C =
    let val ctx' = insrt (insrt ctx (D IMPL B)) (E IMPL B)
    in ctx' ===> C end

  fun appInit G P = List.exists (fn x => x = P) G

  val appDisjL : context -> prop * prop * prop -> sequent * sequent =
    fn (G || O) => fn (A, B, C) =>
      let val ctx1 = insrt (G || O) A
          val ctx2 = insrt (G || O) B
      in (ctx1 ===> C, ctx2 ===> C) end

  val appConjImplL : context -> prop * prop * prop * prop -> sequent =
    fn (G || O) => fn (D : prop, E : prop, B : prop, C : prop) =>
      let val ctx' = insrt (G || O) (D IMPL E IMPL B)
      in ctx' ===> C end

  val appAtomImplL  : context -> prop * prop * prop -> sequent =
    fn (G || O) => fn (P, B, C) =>
      if List.exists (fn x => x = P) G
      then (insrt (G || O) B) ===> C
      else raise NoProof

  val appImplImplL : context
                  -> prop * prop * prop * prop
                  -> sequent * sequent =
    fn (G || O) => fn (D, E, B, C) =>
      let val ctx1 = insrt (insrt (G || O) (E IMPL B)) D
          val ctx2 = insrt (G || O) B
      in (ctx1 ===> E, ctx2 ===> C) end

  (* Keep breaking down the asynchronous rules *)
  fun right (G || O ===> TOP) : derivation = ZeroInf (TopR, G || O ===> TOP)
    | right (G || O ===> A CONJ B) =
        let val goal = G || O ===> A CONJ B
            val (newgoal1, newgoal2) = appConjR (G || O) A B
        in TwoInf (ConjR, right newgoal1, right newgoal2, goal) end
    | right (G || O ===> A IMPL B) =
        let val newgoal = appImplR (G || O) A B
        in OneInf (ImplR, right newgoal, G || O ===> A IMPL B) end
    | right (G || (A CONJ B::O) ===> C) =
        let val goal = (A CONJ B::G) || O ===> C
            val newgoal = appConjL (G || O) A B C
        in OneInf (ConjL, right newgoal, goal) end
    | right (G || (BOT::O) ===> C) = concludeWithBotL (G || O) C
    | right (G || (A DISJ B::O) ===> C) =
        let val goal = G || (A DISJ B::O) ===> C
            val (newgoal1, newgoal2) = appDisjL (G || O) (A, B, C)
        in TwoInf (DisjL, right newgoal1, right newgoal2, goal) end
    | right (G || (TOP IMPL B::O) ===> C) =
        let val newgoal = appTopImplL (G || O) B C
        in OneInf (TopImplL, right newgoal, G || (TOP IMPL B::O) ===> C) end
    | right (G || (BOT IMPL B::O) ===> C) =
        let val newgoal = G || O ===> C
        in OneInf (BotImplL, right newgoal, G || (BOT IMPL B::O) ===> C) end
    | right (G || (D CONJ E IMPL B::O) ===> C) =
        let val goal = G || (D CONJ E IMPL B::O) ===> C
            val newgoal = appConjImplL (G || O) (D, E, B, C)
        in OneInf (ConjImplL, right newgoal, goal) end
    | right (G || (D DISJ E IMPL B::O) ===> C) =
        let val goal = G || (D DISJ E IMPL B::O) ===> C
            val newgoal = appDisjImplL (G || O) D E B C
        in OneInf (DisjImplL, right newgoal, goal) end
    | right (G || [] ===> A DISJ B)         = raise Fail "TODO"
    | right (G || [] ===> C) = left G C

  and left _ _ = raise Fail "TODO"

  fun search (G || [] ===> ATOM X) : derivation =
        if appInit G (ATOM X)
        then ZeroInf (Init, G || [] ===> ATOM X)
        else raise NoProof
    | search ((ATOM X IMPL B::G) || [] ===> C) =
        let val ctx = (ATOM X IMPL B::G) || []
            val newgoal = appAtomImplL (G || []) (ATOM X, B, C)
        in OneInf (AtomImplL, search newgoal, ctx ===> C) end
    | search (G || [] ===> BOT) = raise NoProof
    | search (G || [] ===> A DISJ B) =
        (OneInf (DisjR1, search (G || [] ===> A), G || [] ===> A DISJ B)
         handle NoProof =>
          OneInf (DisjR2, search (G || [] ===> B), G || [] ===> A DISJ B))
    | search ((((D IMPL E) IMPL B::G) || []) ===> C) =
        let val goal = ((D IMPL E) IMPL B::G) || [] ===> C
            val (newgoal1, newgoal2) = appImplImplL (G || []) (D, E, B, C)
        in TwoInf (ImplImplL, search newgoal1, search newgoal2, goal) end

  fun prove (A : prop) : derivation option =
    SOME (search ([] || [] ===> A))
    handle NoProof => NONE


end
