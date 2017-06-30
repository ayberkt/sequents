structure InvCalc = struct
  structure L = List
  open Syntax

  fun $ (f, x) = f x
  infix 0 $

  fun <$> (f, xs) = L.map f xs
  infixr 1 <$>

  fun <*> (_,  []) = []
    | <*> ([], _ ) = []
    | <*> ((x::xs), ys) = ((fn y => (x, y)) <$> ys) @ (<*>(xs, ys))
  infix 2 <*>

  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL

  datatype context = || of (prop list) * (prop list) infix 5 ||

  datatype sequent = ===> of context * prop
  infixr 4 ===>

  datatype rule =
      ConjR | ConjL  | TopR
    | ImplR | ImplL
    | InitR | InitL
    | DisjL | DisjR1 | DisjR2
    | TopL  | BotL

  datatype derivation =
      ZeroInf of rule * sequent
    | OneInf  of rule * derivation * sequent
    | TwoInf  of rule * derivation * derivation * sequent

  val isImpl = fn (_ IMPL _) => true | _ => false

  exception NoProof

  (* If an atomic formula is encountered in a right-decomposition sequent we
     simply need to verify that it occurs in Γ. *)
  fun tryDisjR rule G P =
    SOME $ OneInf (rule, rightInv $ G || [] $ P, G || [] ===> P)
    handle NoProof => NONE

  and tryImplL [] _ = NONE
    | tryImplL G C =
        let
          fun try (A IMPL B, G') =
                (let
                  val D1 = rightInv $ (A IMPL B::G') || [] $ A
                  val D2 = leftInv  $ G || [B] $ C
                in
                  SOME $ TwoInf (ImplL, D1, D2, G || [] ===> A IMPL B)
                end
                handle NoProof => NONE)
            | try (_, _) = NONE
          val indices : int list = valOf <$> L.filter isSome (L.mapi (fn (i, x) => if isImpl x then SOME i else NONE) G)
          fun mkCtx i = (fn (xs, ys) => (hd ys, xs @ (tl ys))) o L.splitAt $ (G, i)
        in
          case L.filter isSome (try <$> (mkCtx <$> indices)) of
            d::_ => d
          | [] => NONE
        end

  and handleRightAtomic (G || O) P =
    if List.exists (fn x => P = x) G
    (* If P ∈ Γ then we can just use initR once to conclude our proof. *)
    then ZeroInf (InitR, G || O ===> P)
    (* If P ∉ Γ we switch to left-inversion on P. *)
    else leftInv $ G || O $ P

  and rightInv ctx (ATOM p) = handleRightAtomic ctx (ATOM p)
      (* Decompose `p CONJ q` to the task of decomposing p and decomposing q*)
    | rightInv ctx (p CONJ q) =
        TwoInf (ConjR, rightInv ctx p, rightInv ctx q, ctx ===> p CONJ q)
      (* ⊤ cannot be decomposed further, end proof by ⊤R. *)
    | rightInv ctx TOP = ZeroInf (TopR, ctx ===> TOP)
      (* Extend Ω with A and decompose B on the right with that context. *)
      (* Rule: ⊃R. *)
    | rightInv (G || O) (A IMPL B) =
        OneInf (ImplR, rightInv $ G || (A::O) $ B, G || O ===> A IMPL B)
      (* If we encounter disjunction or falsehood, we punt and switch to left
       * inversion. *)
    | rightInv (G || O) (A DISJ B) = leftInv $ G || O $ A DISJ B
    | rightInv (G || O) BOT = leftInv $ G || O $ BOT

  and handleLeftAtomic (G || (P::O)) C =
        (* If P = C, we have C contained in Ω hence are done. *)
        (* Otherwise we move P into Γ and continue. *)
        if P = C
        then ZeroInf (InitL, G || (P::O) ===> P)
        else leftInv ((P::G) || O) C
   | handleLeftAtomic (_ || _) _ = raise Fail "impossible case in `handleLeftAtomic`"

  and leftInv (G || ((ATOM P)::O)) C = handleLeftAtomic (G || ((ATOM P)::O)) C
      (* If there is an A ∧ B at the end of Ω, perform left inversion with
       * Γ; Ω, A, B with the same succedent. *)
    | leftInv (G || (A CONJ B::O)) C =
        let val D' = leftInv $ G || (A::B::O) $ C
        in OneInf (ConjL, D', G || (A CONJ B::O) ===> C) end
      (* If there is an A ∨ B at the end of Ω, we need to prove C with both
       * A at the end of Ω and B at the end of Ω. *)
    | leftInv (G || (A DISJ B::O)) C =
        let val D1 = leftInv $ G || (A::O) $ C
            val D2 = leftInv $ G || (B::O) $ C
        in TwoInf (DisjL, D1, D2, (G || (A DISJ B::O)) ===> C) end
      (* If there is a ⊤ at the right of Ω just get rid of that and continue
       * the left-inversion. *)
    | leftInv (G || (TOP::O)) C =
        OneInf (TopL, leftInv $ G || O $ C, G || (TOP::O) ===> C)
      (* If there is a ⊥ at the right of Ω we can prove C regardless of
       * whatever it is by using ⊥L. *)
    | leftInv (G || (BOT::O)) r = ZeroInf (BotL, G || (BOT::O) ===> BOT)
    | leftInv (G || (A IMPL B::O)) C = leftInv $ (A IMPL B::G) || O $ C
    | leftInv (G || []) (A DISJ B) =
        (case tryDisjR DisjR1 G A of
          SOME drv => OneInf (DisjR1, drv, G || [] ===> A DISJ B)
        | NONE => (case tryDisjR DisjR2 G B of
                     SOME drv => OneInf (DisjR2, drv, G || [] ===> A DISJ B)
                   | NONE => case tryImplL G (A DISJ B) of
                               SOME drv => drv
                             | NONE => raise NoProof))
    | leftInv (G || []) C =
        (case tryImplL G C of
           SOME D1 => D1
         | NONE => raise NoProof)

  fun prove A =
    SOME (rightInv $ [] || [] $ A)
    handle NoProof => NONE

end
