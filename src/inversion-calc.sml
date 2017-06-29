structure InvCalc = struct
  open Syntax

  fun $ (f, x) = f x
  infix 0 $

  fun <$> (f, xs) = List.map f xs
  infix 0 <$>

  infixr 9 CONJ
  infixr 8 DISJ
  infixr 7 IMPL

  datatype context = || of (prop list) * (prop list)
  infix 5 ||

  datatype sequent = SeqL of context * prop | SeqR of context * prop

  infixr 4 SeqL
  infixr 4 SeqR

  datatype rule =
      ConjR
    | ConjL
    | TopR
    | ImplR
    | InitR
    | InitL
    | AtomRtoL
    | DisjRtoL
    | TopRtoL
    | DisjL
    | DisjR1
    | DisjR2
    | AtomShift
    | ImplShift
    | TopL
    | BotL
    | BotRtoL
    | ImplL

  datatype derivation =
      Goal of sequent
    | ZeroInf of rule * prop
    | OneInf of rule * derivation * sequent
    | TwoInf of rule * derivation * derivation * prop
    | Switch of rule * derivation

  infixr 5 mem
  fun x mem xs = List.exists (fn y => x = y) xs

  fun justified (Goal _) = false
    | justified (ZeroInf (_, _)) = true
    | justified (OneInf (_, d', _)) = justified d'
    | justified (TwoInf (_, d1, d2, _)) = justified d1 andalso justified d2
    | justified (Switch (_, d')) = justified d'

  exception NoProof

    (* If an atomic formula is encountered in a right-decomposition sequent we
       simply need to verify that it occurs in Γ. *)
  fun tryDisjR rule G P =
    case rightInv $ G || [] $ P of
      drv => SOME $ OneInf (rule, rightInv $ G || [] $ P, G || [] SeqL P)
    handle NoProof => NONE

  and tryImplL [] r = NONE
    | tryImplL G r =
        let
          fun isImpl (_ IMPL _) = true
            | isImpl _ = false
          val impls = List.filter isImpl G
          fun try (p IMPL q) =
                let
                  val d1 = rightInv $ (p IMPL q::G) || [] $ r
                  val d2 = rightInv $ G || [q] $ r
                  val candidate = TwoInf (ImplL, d1, d2, p IMPL q)
                in
                  if justified candidate
                  then SOME candidate
                  else NONE
                end
            | try _ = raise Fail "should not happend"
        in
          case List.filter (fn x => not $ x = NONE) (try <$> impls) of
            d::_ => d
          | [] => NONE
        end

  and handleRightAtomic (G || O) P =
    if P mem G
    (* If P ∈ Γ then we can just use initR once to conclude our proof. *)
    then ZeroInf (InitR, P)
    (* If P ∉ Γ we switch to left-inversion on P. *)
    else OneInf (AtomRtoL, leftInv $ G || O $ P, G || O SeqR P)

  and rightInv ctx (ATOM p) = handleRightAtomic ctx (ATOM p)
      (* Decompose `p CONJ q` to the task of decomposing p and decomposing q*)
    | rightInv ctx (p CONJ q) = TwoInf (ConjR, rightInv ctx p, rightInv ctx q, p CONJ q)
      (* ⊤ cannot be decomposed further, end proof by ⊤R. *)
    | rightInv _ TOP = ZeroInf (TopR, TOP)
      (* Extend Ω with A and decompose B on the right with that context. *)
      (* Rule: ⊃R. *)
    | rightInv (G || O) (A IMPL B) = OneInf (ImplR, rightInv $ G || (A::O) $ B, G || O SeqR (A IMPL B))
      (* If we encounter disjunction or falsehood, we punt and switch to left
       * inversion. *)
    | rightInv (G || O) (A DISJ B) =
        OneInf (DisjRtoL, leftInv $ G || O $ A DISJ B, G || O SeqR (A DISJ B))
    | rightInv (G || O) BOT = OneInf (BotRtoL, leftInv $ G || O $ BOT, G || O SeqR BOT)
  and handleLeftAtomic (G || (P::O)) C =
        (* If P = C, we have C contained in Ω hence are done. *)
        (* Otherwise we move P into Γ and continue. *)
        if P = C then ZeroInf (InitL, P) else OneInf (AtomShift, leftInv ((P::G) || O) C, G || (P::O) SeqL C)
   | handleLeftAtomic (_ || _) _ = raise Fail "impossible case in handleLeftAtomic"
  and leftInv (G || ((ATOM P)::O)) C = handleLeftAtomic (G || ((ATOM P)::O)) C
      (* If there is an A ∧ B at the end of Ω, perform left inversion with
       * Γ; Ω, A, B with the same succedent. *)
    | leftInv (G || (A CONJ B::O)) C = OneInf (ConjL, leftInv $ G || (A::B::O) $ C, G || ((A CONJ B)::O) SeqL C)
      (* If there is an A ∨ B at the end of Ω, we need to prove C with both
       * A at the end of Ω and B at the end of Ω. *)
    | leftInv (G || (A DISJ B::O)) C =
        let
          val (goal1, goal2) = (leftInv $ G || (A::O) $ C, leftInv $ G || (B::O) $ C)
        in TwoInf (DisjL, goal1, goal2, C) end
      (* If there is a ⊤ at the right of Ω just get rid of that and continue
       * the left-inversion. *)
    | leftInv (G || (TOP::O)) C = OneInf (TopL, leftInv $ G || O $ C, (G || (TOP::O)) SeqL C)
      (* If there is a ⊥ at the right of Ω we can prove C regardless of
       * whatever it is by using ⊥L. *)
    | leftInv (G || (BOT::O)) r = ZeroInf (BotL, BOT)
    | leftInv (G || (A IMPL B::O)) C =
        OneInf (ImplShift, leftInv $ (A IMPL B::G) || O $ C, G || (A IMPL B::O) SeqL C)
    | leftInv (G || []) (A DISJ B) =
        (case (tryDisjR DisjR1 G A, tryDisjR DisjR2 G A) of
          (SOME d1, _)  => OneInf (DisjR1, d1, G || [] SeqL (A DISJ B))
        | (_, SOME d2)  => OneInf (DisjR2, d2, G || [] SeqL (A DISJ B))
        | (_, _)  => raise NoProof)
    | leftInv (G || []) C =
        (case tryImplL G C of
          SOME d1 => OneInf (ImplL, d1, G || [] SeqL C)
        | NONE => raise NoProof)

  fun prove p =
    SOME $ rightInv ([] || []) p
    handle NoProof =>
      SOME $ leftInv ([] || []) p
      handle NoProof => NONE

end
