structure ContFree = struct
  open Syntax
  infixr 9 CONJ infixr 8 DISJ infixr 7 IMPL infix 5 || infixr 4 ===>
  open Proofs


  datatype derivation =
      ZeroInf of rule * sequent
    | OneInf  of rule * derivation * sequent
    | TwoInf  of rule * derivation * derivation * sequent

  fun isAtom (ATOM _) = true
    | isAtom _        = false

  exception NoProof

  fun appConjR G A B = ((G ===> A, G ===> B), G ===> A CONJ B)

  fun appTopR G TOP = G ===> TOP

  fun appImplR G A B = ((A::G) ===> B, G ===> (A IMPL B))

  fun appConjL A B G C = (A::B::G ===> C, ((A CONJ B)::G) ===> C)

  fun appTopL G C = (G ===> C, (TOP::G) ===> C)

  fun appBotL G C = (BOT::G) ===> C

  fun appTopImplL B G C = ((B::G) ===> C, ((TOP IMPL B)::G) ===> C)

  fun disjImplL D E B G C = (((D IMPL B)::(E IMPL B)::G) ===> C, ((D DISJ E IMPL B)::G) ===> C)

  fun botImplL B G C = (G ===> C, (BOT IMPL B)::G ===> C)

  fun appInit G P =
    if List.exists (fn x => x = P) G
    then true
    else false

  fun appDisjL G A B C =
    ((A::G ===> C, B::G ===> C), (A DISJ B::G) ===> C)

  fun prove (G || []) (ATOM P)   =
        if appInit G (ATOM P)
        then ZeroInf (Init, G || [] ===> P)
        else raise NoProof
    | prove (G || []) (A DISJ B) =
        (OneInf (DisjR1, prove (G || []) A, G || A ===> (A DISJ B))
        handle NoProof =>
          OneInf (DisjR2, prove (G || []) B, G || A ===> (A DISJ B)))
    | prove (G || []) BOT = raise Fail "TODO"
    | prove ( || []) C = raise Fail "TODO"
    | prove ((ATOM P) IMPL B) = raise Fail "TODO"

end
