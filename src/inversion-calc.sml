structure InvCalc = struct
  open Syntax

  fun $ (f, x) = f x
  infix 0 $

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
    | TopR
    | ImplR
    | InitR
    | InitL
    | AtomRtoL
    | DisjRtoL
    | TopRtoL
    | DisjL
    | AtomShift

  datatype derivation =
      Goal of sequent
    | ZeroInf of rule
    | OneInf of rule * derivation
    | TwoInf of rule * derivation * derivation
    | Switch of rule * derivation

  infixr 5 mem
  fun x mem xs = List.exists (fn y => x = y) xs

  local
    fun rightInv ctx (p CONJ q) = TwoInf (ConjR, rightInv ctx p, rightInv ctx q)
      | rightInv _ TOP = ZeroInf TopR
      | rightInv (G || O) (p IMPL q) =
          OneInf (ImplR, rightInv $ G || (p::O) $ q)
      | rightInv _ _ = raise Fail "impossible case in `rightEnv`"
    fun leftInv (G || ((p CONJ q)::O)) r = leftInv $ G || (p::q::O) $ r
      | leftInv (G || ((p DISJ q)::O)) r =
          let
            val subgoal1 = leftInv $ G || (p::O) $ r
            val subgoal2 = leftInv $ G || (q::O) $ r
          in
            TwoInf (DisjL, subgoal1, subgoal2) end
      | leftInv (G || (TOP::O)) r = leftInv $ G || O $ r
      | leftInv _ _ = raise Fail "impossible case in `leftInv`"
    fun handleRightAtomic (G || O) p =
      if p mem G then ZeroInf InitR else leftInv (G || O) p
    fun handleLeftAtomic (G || (p::O)) r =
      if p = r
      then ZeroInf InitL
      else OneInf (AtomShift, leftInv ((p::G) || O) r)
  in
    fun prove (Goal (ctx SeqR p CONJ q))= rightInv ctx (p CONJ q)
      | prove (Goal (ctx SeqR TOP)) = rightInv ctx TOP
      | prove (Goal (ctx SeqR p IMPL q)) = rightInv ctx $ p IMPL q
      | prove (Goal (ctx SeqR (ATOM p))) = handleRightAtomic ctx (ATOM p)
      | prove (Goal (ctx SeqR p DISJ q)) = leftInv ctx $ p DISJ q
      | prove (Goal (ctx SeqR BOT)) = leftInv ctx $ BOT
      | prove (Goal (ctx SeqL (ATOM p))) = handleLeftAtomic ctx (ATOM p)
  end

end
