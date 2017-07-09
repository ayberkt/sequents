structure LJT = struct
  open Syntax
  open Utils
  open SearchReport
  structure L = List
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  open Proofs
  open Color

  exception NoProof

  val concludeWithBotL =
    fn G || O => fn C =>
      (reportRemark "Ex falso quodlibet 💥 ";
       reportProven ();
       ZeroInf (BotL, (BOT::G) || O ===> C))

  val concludeWithInit =
    fn G || O => fn C =>
      (printRule "init";
       reportProven ();
       ZeroInf (Init, G || O ===> C))

  val concludeWithTopR =
    fn G || O =>
      (reportRemark "⊤ is always provable by ⊤R";
       printRule "⊤R";
       reportProven ();
       ZeroInf (Init, G || O ===> TOP))

  fun insrt (ATOM X) (G || O) = (ATOM X::G) || O
    | insrt (ATOM X IMPL B) (G || O) = (ATOM X IMPL B::G) || O
    | insrt ((A IMPL B) IMPL D) (G || O) = (((A IMPL B) IMPL D)::G) || O
    | insrt A (G || O) = G || (A::O)

  fun appConjR ctx A B =
    (printRule "∧R";
     printNewGoal (ctx ===> A);
     printNewGoal (ctx ===> B);
     (ctx ===> A, ctx ===> B))

  fun appImplR ctx A B =
    let
      val newgoal = insrt A ctx ===> B
    in
      (printRule "⊃R";
       printNewGoal newgoal;
       newgoal)
    end

  val appConjL =
    fn ctx => fn (A, B, C) =>
      let
        val newgoal = (insrt B o insrt A) ctx ===> C
      in
        (printNewGoal newgoal; printRule "∧L"; newgoal)
      end

  val appTopL = fn ctx => fn C => (printRule "⊤L"; ctx ===> C)

  fun appTopImplL (G || O) B C =
    let
      val newgoal = insrt B (G || O) ===> C
    in
      (printRule "⊤⊃L"; printNewGoal newgoal; newgoal)
    end

  fun appDisjImplL ctx D E B C =
    let
      val newgoal = (insrt (E IMPL B) o insrt (D IMPL B)) ctx ===> C
      val _ = printNewGoal newgoal
      val _ = printRule "∨⊃L"
    in
      newgoal
    end

  fun isImpl (_ IMPL _) = true
    | isImpl _ = false

  fun except xs n = (List.take (xs, n)) @ (List.drop (xs, n+1))

  fun allCtxs [] = []
    | allCtxs G =
        L.map (fn i => (L.nth (G, i), except G i)) (range ((L.length G)-1))

  val appDisjL : context -> prop * prop * prop -> sequent * sequent =
    fn (G || O) => fn (A, B, C) =>
      let
        val _ = printRule "∨L"
        val (ctx1, ctx2) = (insrt A (G || O), insrt B (G || O))
      in (ctx1 ===> C, ctx2 ===> C) end

  val appConjImplL : context -> prop * prop * prop * prop -> sequent =
    fn (G || O) => fn (D, E, B, C) =>
      (printRule "∧⊃L";
       (insrt (D IMPL (E IMPL B)) (G || O)) ===> C)

  val appAtomImplL  : prop list -> prop * prop * prop -> sequent =
      fn G => fn (P, B, C) =>
        let val _ = printRule "P⊃L" in
          if List.exists (fn x => x = P) G
          then (insrt B (G || [])) ===> C
          else
            (printRule ((Syntax.pretty P) ^ " ∉ " ^ prProps G);
             raise NoProof)
        end

  val appImplImplL =
    fn G || O => fn (D, E, B, C) =>
      let val ctx1 = (insrt D o insrt (E IMPL B)) (G || O)
          val ctx2 = insrt B (G || O)
      in (ctx1 ===> E, ctx2 ===> C) end

  (* Keep breaking down the asynchronous rules *)
  fun right (ctx ===> TOP) =
        concludeWithTopR ctx
    | right (ctx ===> A CONJ B) =
        let
          val _ = printSequent ctx (A CONJ B)
          val goal = ctx ===> A CONJ B
          val (newgoal1, newgoal2) = appConjR ctx A B
        in TwoInf (ConjR, searchWithIndent right newgoal1, searchWithIndent right newgoal2, goal) end
    | right (ctx ===> A IMPL B) =
        let
          val _ = printSequent ctx (A IMPL B)
          val newgoal = appImplR ctx A B
        in OneInf (ImplR, right newgoal, ctx ===> A IMPL B) end
    | right (G || (A CONJ B::O) ===> C) =
        let
          val goal = (A CONJ B::G) || O ===> C
          val _ = printSequent (G || (A CONJ B::O)) C
          val newgoal = appConjL (G || O) (A, B, C)
        in OneInf (ConjL, right newgoal, goal) end
    | right (G || (TOP::O) ===> C) =
        let
          val newgoal = appTopL (G || O ) C
        in
          OneInf (TopL, right newgoal, G || (TOP::O) ===> C)
        end
    | right (G || (BOT::O) ===> C) =
        (printSequent (G || (BOT::O)) C;
         concludeWithBotL (G || O) C)
    | right (G || (A DISJ B::O) ===> C) =
        let
          val _ = printSequent (G || (A DISJ B::O)) C
          val goal = G || (A DISJ B::O) ===> C
          val (newgoal1, newgoal2) = appDisjL (G || O) (A, B, C)
        in TwoInf (DisjL, right newgoal1, right newgoal2, goal) end
    | right (G || (TOP IMPL B::O) ===> C) =
        let
          val _ = printSequent (G || (TOP IMPL B::O)) C
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
        let val _ = printSequent (G || (D DISJ E IMPL B::O)) C
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
      (printSequent (G || []) C; left G C)

  and left G C =
    case getSome (eliminate C) (allCtxs G) of
      SOME d => d
    | NONE => (reportNotProvable (); raise NoProof)

  and eliminate (ATOM Y) (ATOM X, ctx)  =
        if X = Y
        then
          (reportRemark (X ^ " ∈ " ^ brackets (prProps (ATOM X::ctx)));
           SOME (concludeWithInit ((ATOM X::ctx) || []) (ATOM Y)))
        else NONE
    | eliminate _ (ATOM X, _) = NONE
    | eliminate C (ATOM X IMPL B, ctx) =
        let val _ = printSequent ((ATOM X IMPL B::ctx) || []) C
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
              (printRule "⊃⊃L";
              SOME (TwoInf (ImplImplL, right newgoal1, right newgoal2, goal)))
          handle NoProof => NONE
        end
    | eliminate _ _ = (printLn "impossible case"; raise Fail "TODO")

  fun search C =
    SOME (right ([] || [] ===> C))
    handle NoProof => NONE

  val prove : prop -> derivation option = search

end
