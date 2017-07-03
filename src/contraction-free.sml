structure ContFree = struct local open Proofs in

  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>

  fun isRightSync (ATOM P) = true
    | isRightSync (A DISJ B) = true
    | isRightSync BOT = true
    | isRightSync _ = false

  fun isLeftSync (ATOM P) = true
    | isLeftSync ((ATOM P) IMPL B) = true
    | isLeftSync ((D IMPL E) IMPL B) = true
    | isLeftSync _ = false

  exception NoProof

  fun updateCtx (G || O) [] = G || O
    | updateCtx (G || O) (P::Ps) =
        if isLeftSync P
        then updateCtx (G || (P::O)) Ps
        else updateCtx ((P::G) || O) Ps

  fun concByTopR ctx = ZeroInf (TopR, ctx ===> TOP)

  fun concByInit (O : prop list) P =
    if List.exists (fn x => x = P) O
    then ZeroInf (Init, ([] || O) ===> P)
    else raise NoProof

  fun concByBotL ctx C = ZeroInf (BotL, ctx ===> C)

  fun search (G  || O) TOP          = concByTopR (G || O)
    | search (G  || O) (A CONJ B)   = prvConjR (G || O) A B
    | search (G  || O) (A IMPL B)   = prvImplR (G || O) A B
    | search ((A CONJ B::G) || O) C = prvConjL (G || O) A B C
    | search ((TOP::G) || O) C      = prvTopL ((TOP::G) || O) C
    | search ((A DISJ B::G) || O) C = raise Fail "TODO"
    | search ((BOT::G) || O) C      = concByBotL ((BOT::G) || O) C
    | search ([] || O) (ATOM X)     = concByInit O (ATOM X)
    | search ([] || O) _            = raise Fail "TODO"
    | search (_  || _) _            = raise Fail "TODO"
  and prvConjR ctx A B =
    TwoInf (ConjR, search ctx A, search ctx B, ctx ===> A CONJ B)
  and prvImplR (G || O) A B =
    let val (G' || O') = updateCtx (G || O) [A]
    in search (G' || O') B end
  and prvConjL ctx A B C =
    let val ctx' = updateCtx ctx [A, B]
    in search ctx' C end
  and prvTopL ctx C = raise Fail "TODO"
  fun prove P =
    SOME (search ([] || []) P)
    handle NoProof => NONE

end end
