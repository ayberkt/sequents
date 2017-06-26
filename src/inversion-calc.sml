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
    | DisjR1
    | DisjR2
    | AtomShift
    | ImplShift
    | TopL
    | BotL
    | ImplL

  datatype derivation =
      Goal of sequent
    | ZeroInf of rule
    | OneInf of rule * derivation
    | TwoInf of rule * derivation * derivation
    | Switch of rule * derivation

  infixr 5 mem
  fun x mem xs = List.exists (fn y => x = y) xs

  fun justified (Goal _) = false
    | justified (ZeroInf _) = true
    | justified (OneInf (_, d')) = justified d'
    | justified (TwoInf (_, d1, d2)) = justified d1 andalso justified d2
    | justified (Switch (_, d')) = justified d'

  local
    fun handleRightAtomic (G || O) p =
      if p mem G then ZeroInf InitR else leftInv (G || O) p
    and rightInv ctx (ATOM p) = handleRightAtomic ctx (ATOM p)
      | rightInv ctx (p CONJ q) = TwoInf (ConjR, rightInv ctx p, rightInv ctx q)
      | rightInv _ TOP = ZeroInf TopR
      | rightInv (G || O) (p IMPL q) =
          OneInf (ImplR, rightInv $ G || (p::O) $ q)
      | rightInv _ _ = raise Fail "impossible case in `rightEnv`"
    and handleLeftAtomic (G || (p::O)) r =
      if p = r
      then ZeroInf InitL
      else OneInf (AtomShift, leftInv ((p::G) || O) r)
    and leftInv ctx (ATOM p) = handleLeftAtomic ctx (ATOM p)
      | leftInv (G || ((p CONJ q)::O)) r = leftInv $ G || (p::q::O) $ r
      | leftInv (G || ((p DISJ q)::O)) r =
          let
            val subgoal1 = leftInv $ G || (p::O) $ r
            val subgoal2 = leftInv $ G || (q::O) $ r
          in
            TwoInf (DisjL, subgoal1, subgoal2) end
      | leftInv (G || (TOP::O)) r =
          OneInf (TopL, leftInv $ G || O $ r)
      | leftInv (G || (BOT::O)) r = ZeroInf BotL
      | leftInv (G || ((A IMPL B)::O)) r =
          OneInf (ImplShift, leftInv $ ((A IMPL B)::G) || O $ r)
      | leftInv _ _ = raise Fail "impossible case in `leftInv`"
    fun tryImplL [] r = NONE
      | tryImplL ((p IMPL q)::G) r =
          let
            val d1 = rightInv $ ((p IMPL q)::G) || [] $ r
            val d2 = rightInv $ G || [q] $ r
            val candidate = TwoInf (ImplL, d1, d2)
          in
            if justified candidate
            then SOME candidate
            else tryImplL G r
          end
    fun tryImplR1 G p =
      let
        val candidate = OneInf (DisjR1, rightInv (G || []) p)
      in
        if justified candidate then SOME candidate else NONE
      end
    fun tryImplR2 G p =
      let
        val candidate = OneInf (DisjR2, rightInv (G || []) p)
      in
        if justified candidate then SOME candidate else NONE
      end
  in
    fun prove (Goal ((G || []) SeqL r)) =
          (case (tryImplR1 G r, tryImplR2 G r, tryImplL G r) of
              (SOME d1, _,             _) => d1
            | (_,       SOME d2,       _) => d2
            | (_,       _,       SOME d3) => d3
            | (_, _, _) => raise Fail "no derivation found (which should not have been the case)")
      | prove (Goal (ctx SeqR p)) = rightInv ctx p
      | prove (Goal (ctx SeqL p)) = leftInv ctx p
  end

end
