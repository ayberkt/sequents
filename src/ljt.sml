structure LJT = struct
  open Syntax
  open Utils
  open SearchReport
  structure L = List
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  open Proofs
  open Color

  fun isLeftSync (ATOM _) = true
    | isLeftSync ((ATOM _) IMPL _) = true
    | isLeftSync ((_ IMPL _) IMPL _) = true
    | isLeftSync _ = false

  exception NoProof

  fun concludeWithBotL (G || O) C =
    (printMsg "Ex falso quodlibet 💥 . Conclude proof with ⊥L.";
     ZeroInf (BotL, (BOT::G) || O ===> C))

  fun concludeWithInit (G || O) C =
    (printMsg ("Proved " ^ (prSequent G O C) ^ " using init.");
     ZeroInf (Init, G || O ===> C))

  fun concludeWithTopR (G || O) =
    (printMsg ("Proved " ^ (prSequent G O TOP) ^ " using ⊤R.");
     ZeroInf (Init, G || O ===> TOP))

  fun insrt (G || O) (ATOM X)  = ((ATOM X)::G) || O
    | insrt (G || O) TOP = G || (TOP::O)
    | insrt (G || O) BOT = G || (BOT::O)
    | insrt (G || O) ((ATOM X) IMPL B) = (ATOM X IMPL B::G) || O
    | insrt (G || O) ((A IMPL B) IMPL D) = (((A IMPL B) IMPL D)::G) || O
    | insrt (G || O) (A IMPL B) = G || (A IMPL B::O)
    | insrt (G || O) (A CONJ B) = G || (A CONJ B::O)
    | insrt (G || O) (A DISJ B) = G || (A DISJ B::O)

  fun appConjR (G || O) A B =
    (printMsg "Apply ∧R.";
     (G || O ===> A, G || O ===> B))

  fun appImplR ctx A B =
    (printMsg "Apply ⊃R.";
     (insrt ctx A) ===> B)

  fun appConjL (G || O) (A : prop) (B : prop) (C : prop) =
    let
      val _ = printMsg "Apply ∧L."
      val ctx' = insrt (insrt (G || O) A) B
    in ctx' ===> C end

  fun appTopL (G || O) C =
    (printMsg "Apply ⊤L."; G || O ===> C)

  fun appTopImplL (G || O) B C =
    (printMsg "Apply ⊤⊃L.";
     (insrt (G || O) B) ===> C)

  fun appDisjImplL ctx D E B C =
    (printMsg "Apply ∨⊃L.";
     (insrt (insrt ctx (D IMPL B)) (E IMPL B)) ===> C)

  fun isImpl (_ IMPL _) = true
    | isImpl _ = false

  fun except xs n = (List.take (xs, n)) @ (List.drop (xs, n+1))

  fun allCtxs [] = []
    | allCtxs G =
    let
      (*val _ = (printLn o prCtxs) result*)
      val result = L.map (fn i => (L.nth (G, i), except G i)) (range ((L.length G)-1))
    in
      result
    end

  val appDisjL : context -> prop * prop * prop -> sequent * sequent =
    fn (G || O) => fn (A, B, C) =>
      let
        val _ = printMsg "Apply ∨L."
        val ctx1 = insrt (G || O) A
        val ctx2 = insrt (G || O) B
      in (ctx1 ===> C, ctx2 ===> C) end

  val appConjImplL : context -> prop * prop * prop * prop -> sequent =
    fn (G || O) => fn (D, E, B, C) =>
      (printMsg "Apply ∧⊃L.";
       (insrt (G || O) (D IMPL (E IMPL B))) ===> C)

  val appAtomImplL  : prop list -> prop * prop * prop -> sequent =
      fn G => fn (P, B, C) =>
        let val _ = printMsg "Apply P⊃L." in
          if List.exists (fn x => x = P) G
          then (insrt (G || []) B) ===> C
          else
            (printMsg ((Syntax.pretty P) ^ " ∉ " ^ prProps G);
             raise NoProof)
        end

  val appImplImplL : context
                  -> prop * prop * prop * prop
                  -> sequent * sequent =
    fn (G || O) => fn (D, E, B, C) =>
      let val ctx1 = insrt (insrt (G || O) (E IMPL B)) D
          val ctx2 = insrt (G || O) B
      in (ctx1 ===> E, ctx2 ===> C) end

  (* Keep breaking down the asynchronous rules *)
  fun right (G || O ===> TOP) =
        concludeWithTopR (G || O)
    | right (G || O ===> A CONJ B) =
        let
          val _ = printSequent G O (A CONJ B)
          val goal = G || O ===> A CONJ B
          val (newgoal1, newgoal2) = appConjR (G || O) A B
        in TwoInf (ConjR, right newgoal1, right newgoal2, goal) end
    | right (G || O ===> A IMPL B) =
        let
          val _ = printSequent G O (A IMPL B)
          val newgoal = appImplR (G || O) A B
        in OneInf (ImplR, right newgoal, G || O ===> A IMPL B) end
    | right (G || (A CONJ B::O) ===> C) =
        let
          val goal = (A CONJ B::G) || O ===> C
          val _ = printSequent G (A CONJ B::O) C
          val newgoal = appConjL (G || O) A B C
        in OneInf (ConjL, right newgoal, goal) end
    | right (G || (TOP::O) ===> C) =
        let
          val newgoal = appTopL (G || O ) C
        in
          OneInf (TopL, right newgoal, G || (TOP::O) ===> C)
        end
    | right (G || (BOT::O) ===> C) =
        (printSequent G (BOT::O) C;
         concludeWithBotL (G || O) C)
    | right (G || (A DISJ B::O) ===> C) =
        let
          val _ = printSequent G (A DISJ B::O) C
          val goal = G || (A DISJ B::O) ===> C
          val (newgoal1, newgoal2) = appDisjL (G || O) (A, B, C)
        in TwoInf (DisjL, right newgoal1, right newgoal2, goal) end
    | right (G || (TOP IMPL B::O) ===> C) =
        let
          val _ = printSequent G (TOP IMPL B::O) C
          val newgoal = appTopImplL (G || O) B C
        in OneInf (TopImplL, right newgoal, G || (TOP IMPL B::O) ===> C) end
    | right (G || (BOT IMPL B::O) ===> C) =
        let val newgoal = G || O ===> C
        in OneInf (BotImplL, right newgoal, G || (BOT IMPL B::O) ===> C) end
    | right (G || (D CONJ E IMPL B::O) ===> C) =
        let val goal = G || (D CONJ E IMPL B::O) ===> C
            val newgoal = appConjImplL (G || O) (D, E, B, C)
        in OneInf (ConjImplL, right newgoal, goal) end
    | right (G || (D DISJ E IMPL B::O) ===> C) =
        let val _ = printSequent G (D DISJ E IMPL B::O) C
            val goal = G || (D DISJ E IMPL B::O) ===> C
            val newgoal = appDisjImplL (G || O) D E B C
        in OneInf (DisjImplL, right newgoal, goal) end
    | right (G || [] ===> A DISJ B) =
        let val goal = (G || [] ===> A DISJ B)
        in
          OneInf (DisjL, left G (A DISJ B), goal)
          handle NoProof =>
            (OneInf (DisjR1, right (G || [] ===> A), goal)
             handle NoProof =>
                 OneInf (DisjR2, right (G || [] ===> B), goal))
        end
    | right (G || [] ===> C) =
      (printSequent G [] C;
       printMsg "Will switch to left.";
       left G C)

  and left G C =
    case getSome (eliminate C) (allCtxs G) of
      SOME d => d
    | NONE => (printMsg "Derivation not found"; raise NoProof)

  and eliminate (ATOM Y) (ATOM X, ctx)  =
        if X = Y
        then
          (printMsg (X ^ " ∈ " ^ (prProps (ATOM X::ctx)));
           SOME (concludeWithInit ((ATOM X::ctx) || []) (ATOM Y)))
        else NONE
    | eliminate _ (ATOM X, _) = NONE
    | eliminate C (ATOM X IMPL B, ctx) =
        let val _ = printSequent (ATOM X IMPL B::ctx) [] C
            val goal = (ATOM X IMPL B::ctx) || [] ===> C
        in
          (case appAtomImplL ctx (ATOM X, B, C) of
             newgoal => SOME (OneInf (AtomImplL, right newgoal, goal)))
           handle NoProof => NONE
        end
    | eliminate C ((D IMPL E) IMPL B, ctx) =
        let
          val goal = ((D IMPL E) IMPL B::ctx) || [] ===> C
        in
          case appImplImplL (ctx || []) (D, E, B, C) of
            (newgoal1, newgoal2) =>
              (printMsg "Apply ⊃⊃L.";
              SOME (TwoInf (ImplImplL, right newgoal1, right newgoal2, goal)))
          handle NoProof => NONE
        end
    | eliminate _ _ = (printLn "impossible case"; raise Fail "TODO")

  fun search C =
    (printLn (format (Bright, Magenta) ("Theorem.  " ^ (prSequent [] [] C)));
     (SOME (right ([] || [] ===> C))
      handle NoProof => NONE))

  fun prove (A : prop) : derivation option = search A


end
