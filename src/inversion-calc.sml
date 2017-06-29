structure InvCalc = struct
  open Syntax

  fun $ (f, x) = f x infix 0 $

  fun <$> (f, xs) = List.map f xs infix 0 <$>

  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL

  datatype context = || of (prop list) * (prop list) infix 5 ||

  datatype sequent = SeqL of context * prop | SeqR of context * prop
  infixr 4 SeqL infixr 4 SeqR

  datatype rule =
      ConjR | ConjL  | TopR
    | ImplR | ImplL
    | InitR | InitL
    | DisjL | DisjR1 | DisjR2
    | TopL  | BotL

  datatype derivation =
      Goal of sequent
    | ZeroInf of rule * sequent
    | OneInf of rule * derivation * sequent
    | TwoInf of rule * derivation * derivation * sequent

  exception NoProof

  (* If an atomic formula is encountered in a right-decomposition sequent we
     simply need to verify that it occurs in Γ. *)
  fun tryDisjR rule G P =
    SOME $ OneInf (rule, rightInv $ G || [] $ P, G || [] SeqL P)
    handle NoProof => NONE

  and tryImplL [] r = NONE
    | tryImplL G r =
        let
          val isImpl = fn (_ IMPL _) => true | _ => false
          val impls = List.filter isImpl G
          fun try (p IMPL q) =
                (let
                  val D1 = rightInv $ (p IMPL q::G) || [] $ r
                  val D2 = rightInv $ G || [q] $ r
                in
                  SOME $ TwoInf (ImplL, D1, D2, G || [] SeqL p IMPL q)
                end
                handle NoProof => NONE)
            | try _ = raise Fail "should not happen"
        in
          case List.filter isSome (try <$> impls) of
            d::_ => d
          | [] => NONE
        end

  and handleRightAtomic (G || O) P =
    if List.exists (fn x => P = x) G
    (* If P ∈ Γ then we can just use initR once to conclude our proof. *)
    then ZeroInf (InitR, G || O SeqR P)
    (* If P ∉ Γ we switch to left-inversion on P. *)
    else leftInv $ G || O $ P

  and rightInv ctx (ATOM p) = handleRightAtomic ctx (ATOM p)
      (* Decompose `p CONJ q` to the task of decomposing p and decomposing q*)
    | rightInv ctx (p CONJ q) =
        TwoInf (ConjR, rightInv ctx p, rightInv ctx q, ctx SeqL (p CONJ q))
      (* ⊤ cannot be decomposed further, end proof by ⊤R. *)
    | rightInv ctx TOP = ZeroInf (TopR, ctx SeqR TOP)
      (* Extend Ω with A and decompose B on the right with that context. *)
      (* Rule: ⊃R. *)
    | rightInv (G || O) (A IMPL B) =
        OneInf (ImplR, rightInv $ G || (A::O) $ B, G || O SeqR (A IMPL B))
      (* If we encounter disjunction or falsehood, we punt and switch to left
       * inversion. *)
    | rightInv (G || O) (A DISJ B) = leftInv $ G || O $ A DISJ B
    | rightInv (G || O) BOT = leftInv $ G || O $ BOT

  and handleLeftAtomic (G || (P::O)) C =
        (* If P = C, we have C contained in Ω hence are done. *)
        (* Otherwise we move P into Γ and continue. *)
        if P = C
        then ZeroInf (InitL, G || (P::O) SeqR P)
        else leftInv ((P::G) || O) C
   | handleLeftAtomic (_ || _) _ = raise Fail "impossible case in `handleLeftAtomic`"

  and leftInv (G || ((ATOM P)::O)) C = handleLeftAtomic (G || ((ATOM P)::O)) C
      (* If there is an A ∧ B at the end of Ω, perform left inversion with
       * Γ; Ω, A, B with the same succedent. *)
    | leftInv (G || (A CONJ B::O)) C =
        let val D' = leftInv $ G || (A::B::O) $ C
        in OneInf (ConjL, D', G || ((A CONJ B)::O) SeqL C) end
      (* If there is an A ∨ B at the end of Ω, we need to prove C with both
       * A at the end of Ω and B at the end of Ω. *)
    | leftInv (G || (A DISJ B::O)) C =
        let val subG1 = leftInv $ G || (A::O) $ C
            val subG2 = leftInv $ G || (B::O) $ C
        in TwoInf (DisjL, subG1, subG2, (G || (A DISJ B::O)) SeqL C) end
      (* If there is a ⊤ at the right of Ω just get rid of that and continue
       * the left-inversion. *)
    | leftInv (G || (TOP::O)) C =
        OneInf (TopL, leftInv $ G || O $ C, (G || (TOP::O)) SeqL C)
      (* If there is a ⊥ at the right of Ω we can prove C regardless of
       * whatever it is by using ⊥L. *)
    | leftInv (G || (BOT::O)) r = ZeroInf (BotL, G || (BOT::O) SeqL BOT)
    | leftInv (G || (A IMPL B::O)) C = leftInv $ (A IMPL B::G) || O $ C
    | leftInv (G || []) (A DISJ B) =
        (case (tryDisjR DisjR1 G A, tryDisjR DisjR2 G A) of
          (SOME d1, _)  => OneInf (DisjR1, d1, G || [] SeqL (A DISJ B))
        | (_, SOME d2)  => OneInf (DisjR2, d2, G || [] SeqL (A DISJ B))
        | (_, _)  => raise NoProof)
    | leftInv (G || []) C =
        case tryImplL G C of
          SOME D1 => OneInf (ImplL, D1, G || [] SeqL C)
        | NONE => raise NoProof

  fun prove p =
    SOME $ rightInv ([] || []) p
    handle NoProof =>
      (SOME $ leftInv ([] || []) p
      handle NoProof => NONE)

end
