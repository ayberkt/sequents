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

  val mapi =
    fn (f : int * 'a -> 'b) => fn (xs : 'a list) =>
      let
        fun mapi' f [] _ = []
          | mapi' f (x::xs) n = (f (n, x))::(mapi' f xs (n+1))
      in mapi' f xs 0 end

  fun splitAt (xs, n) =
    let
      fun splitAt' (pre, post, i : int) ([], n : int) = (pre, post)
        | splitAt' (pre, post, i : int) (y::ys, n) =
            if i < n
            then splitAt' (pre@[y], post    , i+1) (ys, n)
            else splitAt' (pre    , post@[y], i+1) (ys, n)
    in splitAt' ([], [], 0) (xs, n) end

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

  (* If an atomic formula is encountered in a right-decomposition sequent we
     simply need to verify that it occurs in Γ. *)
  (*fun tryDisjR rule G P =
    ( (*print "Called tryDisjR...\n";*)
    (case rightInv $ G || [] $ P of
      SOME D' => SOME $ OneInf (rule, D', G || [] ===> P)
    | NONE => NONE))*)
(*
  and tryImplL [] _ = NONE
    | tryImplL G C =
        let
          fun try (A IMPL B, G') =
                (let
                  val MD1 = rightInv $ (A IMPL B::G') || [] $ A
                  val MD2 = leftInv  $ G || [B] $ C
                in
                  case (MD1, MD2) of
                    (SOME D1, SOME D2) => SOME (D1, D2)
                  | _ => NONE
                end)
            | try (_, _) = NONE
          val indices : int list = valOf <$> L.filter isSome (mapi (fn (i, x) => if isImpl x then SOME i else NONE) G)
          fun mkCtx i = (fn (xs, ys) => (hd ys, xs @ (tl ys))) o splitAt $ (G, i)
        in
          case L.filter isSome (try <$> (mkCtx <$> indices)) of
            d::_ => d
          | [] => NONE
        end
*)

  fun rightInv (G || O) (ATOM P) =
        if List.exists (fn (ATOM x) => P = x) G
        then ZeroInf (InitR, G || O ===> (ATOM P))
        else leftInv $ G || O $ (ATOM P)
    | rightInv ctx (A CONJ B) =
        let val (D1, D2) = (rightInv ctx A, rightInv ctx B)
        in TwoInf (ConjR, D1, D2, ctx ===> (A CONJ B)) end
    | rightInv ctx TOP = ZeroInf (TopR, ctx ===> TOP)
    | rightInv (G || O) (A IMPL B) =
        let val D1 = rightInv $ G || (A::O) $ B
        in OneInf (ImplR, D1, G || O ===> A IMPL B) end
    | rightInv (G || O) (A DISJ B) = leftInv $ G || O $ A DISJ B
    | rightInv (G || O) BOT = leftInv $ G || O $ BOT

  and leftInv (G || ((ATOM P)::O)) C =
        if (ATOM P) = C
        then ZeroInf (InitL, G || ((ATOM P)::O) ===> (ATOM P))
        else leftInv (((ATOM P)::G) || O) C
    | leftInv (G || (A CONJ B::O)) C =
        let val D1 = leftInv $ G || (A::B::O) $ C
        in OneInf (ConjL, D1, G || (A CONJ B::O) ===> C) end
    | leftInv (G || (A DISJ B::O)) C =
        let val (D1, D2) = (leftInv $ G || (A::O) $ C, leftInv $ G || (B::O) $ C)
        in TwoInf (DisjL, D1, D2, (G || (A DISJ B::O)) ===> C) end
    | leftInv (G || (TOP::O)) C =
        let val D1 = leftInv $ G || O $ C
        in OneInf (TopL, D1, G || (TOP::O) ===> C) end
    | leftInv (G || (BOT::O)) _ = ZeroInf (BotL, G || (BOT::O) ===> BOT)
    | leftInv (G || (A IMPL B::O)) C = leftInv $ (A IMPL B::G) || O $ C
(*
  and leftInvTry (G || []) (A DISJ B) =
        case tryDisjR DisjR1 G A of
          SOME D1 => SOME $ OneInf (DisjR1, D', G || [] ===> A DISJ B)
        | NONE =>
            (case tryDisjR DisjR2 G B of
               SOME D1 => SOME $ OneInf (DisjR2, D1, G || [] ===> A DISJ B)
             | NONE => NONE)
    | leftInv (G || []) C =
        if L.exists isImpl G
        then
          (case tryImplL G C of
             SOME (D1, D2) => SOME $ TwoInf (ImplL, D1, D2, G || [] ===> C)
           | NONE => NONE)
        else NONE
*)
  val prove = rightInv $ [] || []

end
