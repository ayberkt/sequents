structure LJT = struct
  open Syntax
  open Utils
  structure L = List
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  open Proofs
  open Color

  exception NoProof

  val concludeWithBotL : context -> prop -> derivation =
    fn G || O => fn C => ZeroInf (BotL, (BOT::G) || O ===> C)

  val concludeWithInit : context -> prop -> derivation =
    fn G || O => fn C => ZeroInf (Init, G || O ===> C)

  val concludeWithTopR : context -> derivation =
    fn G || O => ZeroInf (Init, G || O ===> TOP)

  fun insrt (ATOM X) (G || O) = (ATOM X::G) || O
    | insrt (ATOM X IMPL B) (G || O) = (ATOM X IMPL B::G) || O
    | insrt ((A IMPL B) IMPL D) (G || O) = (((A IMPL B) IMPL D)::G) || O
    | insrt A (G || O) = G || (A::O)

  val appConjR = fn ctx => fn (A, B) => (ctx ===> A, ctx ===> B)

  val appImplR = fn ctx => fn (A, B) => insrt A ctx ===> B

  val appConjL = fn ctx => fn (A, B, C) => (insrt B o insrt A) ctx ===> C

  val appTopL = fn ctx => fn C => ctx ===> C

  fun appTopImplL (G || O) B C = insrt B (G || O) ===> C

  val appDisjImplL =
    fn ctx => fn (D, E, B, C) =>
      (insrt (E IMPL B) o insrt (D IMPL B)) ctx ===> C

  fun except xs n = List.take (xs, n) @ List.drop (xs, n+1)

  fun allCtxs [] = []
    | allCtxs G =
        L.map (fn i => (L.nth (G, i), except G i)) (range (L.length G - 1))

  val appDisjL : context -> prop * prop * prop -> sequent * sequent =
    fn (G || O) => fn (A, B, C) =>
      let
        val (ctx1, ctx2) = (insrt A (G || O), insrt B (G || O))
      in (ctx1 ===> C, ctx2 ===> C) end

  val appConjImplL : context -> prop * prop * prop * prop -> sequent =
    fn (G || O) => fn (D, E, B, C) =>
      insrt (D IMPL (E IMPL B)) (G || O) ===> C

  val appAtomImplL  : prop list -> prop * prop * prop -> sequent =
      fn G => fn (P, B, C) =>
        if List.exists (fn x => x = P) G
        then (insrt B (G || [])) ===> C
        else raise NoProof

  val appImplImplL =
    fn G || O => fn (D, E, B, C) =>
      let
        val ctx1 = (insrt D o insrt (E IMPL B)) (G || O)
        val ctx2 = insrt B (G || O)
      in
        (ctx1 ===> E, ctx2 ===> C)
      end

  (* Keep breaking down the asynchronous rules *)
  fun breakdown (ctx ===> TOP) =
        concludeWithTopR ctx
    | breakdown (ctx ===> A CONJ B) =
        let
          val goal = ctx ===> A CONJ B
          val (newgoal1, newgoal2) = appConjR ctx (A, B)
        in TwoInf (ConjR, breakdown newgoal1, breakdown newgoal2, goal) end
    | breakdown (ctx ===> A IMPL B) =
        let
          val newgoal = appImplR ctx (A, B)
        in OneInf (ImplR, breakdown newgoal, ctx ===> A IMPL B) end
    | breakdown (G || (A CONJ B::O) ===> C) =
        let
          val goal = (A CONJ B::G) || O ===> C
          val newgoal = appConjL (G || O) (A, B, C)
        in OneInf (ConjL, breakdown newgoal, goal) end
    | breakdown (G || (TOP::O) ===> C) =
        let
          val newgoal = appTopL (G || O ) C
        in
          OneInf (TopL, breakdown newgoal, G || (TOP::O) ===> C)
        end
    | breakdown (G || (BOT::O) ===> C) =
        concludeWithBotL (G || O) C
    | breakdown (G || (A DISJ B::O) ===> C) =
        let
          val goal = G || (A DISJ B::O) ===> C
          val (newgoal1, newgoal2) = appDisjL (G || O) (A, B, C)
        in TwoInf (DisjL, breakdown newgoal1, breakdown newgoal2, goal) end
    | breakdown (G || (TOP IMPL B::O) ===> C) =
        let
          val newgoal = appTopImplL (G || O) B C
        in OneInf (TopImplL, breakdown newgoal, G || (TOP IMPL B::O) ===> C) end
    | breakdown (G || (BOT IMPL B::O) ===> C) =
        let val newgoal = G || O ===> C
        in OneInf (BotImplL, breakdown newgoal, G || (BOT IMPL B::O) ===> C) end
    | breakdown (G || (D CONJ E IMPL B::O) ===> C) =
        let val goal = G || (D CONJ E IMPL B::O) ===> C
            val newgoal = appConjImplL (G || O) (D, E, B, C)
        in OneInf (ConjImplL, breakdown newgoal, goal) end
    | breakdown (G || (D DISJ E IMPL B::O) ===> C) =
        let
          val goal = G || (D DISJ E IMPL B::O) ===> C
          val newgoal = appDisjImplL (G || O) (D, E, B, C)
        in OneInf (DisjImplL, breakdown newgoal, goal) end
    | breakdown (G || [] ===> A DISJ B) =
        let val goal = (G || [] ===> A DISJ B)
        in
          OneInf (DisjL, searchSync G (A DISJ B), goal)
          handle NoProof =>
            (OneInf (DisjR1, breakdown (G || [] ===> A), goal)
             handle NoProof =>
                 OneInf (DisjR2, breakdown (G || [] ===> B), goal))
        end
    | breakdown (G || [] ===> C) = searchSync G C
    | breakdown _ = raise Fail "breakdown case not supposed to happen"

  and searchSync G C =
    case getSome (eliminate C) (allCtxs G) of
      SOME d => d
    | NONE => raise NoProof

  and eliminate (ATOM Y) (ATOM X, ctx)  =
        if X = Y
        then SOME (concludeWithInit ((ATOM X::ctx) || []) (ATOM Y))
        else NONE
    | eliminate _ (ATOM X, _) = NONE
    | eliminate C (ATOM X IMPL B, ctx) =
        let
          val goal = (ATOM X IMPL B::ctx) || [] ===> C
        in
          (case appAtomImplL ctx (ATOM X, B, C) of
             newgoal => SOME (OneInf (AtomImplL, breakdown newgoal, goal)))
           handle NoProof => NONE
        end
    | eliminate C ((D IMPL E) IMPL B, ctx) =
        let
          val goal = ((D IMPL E) IMPL B::ctx) || [] ===> C
        in
          case appImplImplL (ctx || []) (D, E, B, C) of
            (newgoal1, newgoal2) =>
              SOME (TwoInf (ImplImplL, breakdown newgoal1, breakdown newgoal2, goal))
          handle NoProof => NONE
        end
    | eliminate _ _ = raise Fail "internal error"

  fun search C =
    SOME (breakdown ([] || [] ===> C))
    handle NoProof => NONE

  val prove : prop -> derivation option = search

end
