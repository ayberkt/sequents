structure InvCalc = struct
  structure L = List
  structure O = Option
  open Syntax

  fun printLn s = print (s ^ "\n")

  fun $ (f, x) = f x
  infix 0 $

  fun <$> (f, xs) = L.map f xs
  infixr 1 <$>

  val mapi =
    fn f => fn (xs : 'a list) =>
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

  exception NoProof

  fun getImpl (i, _ IMPL _) = SOME i
    | getImpl (_, _) = NONE

  fun catOpts [] = []
    | catOpts (SOME x::os) = x::(catOpts os)
    | catOpts (NONE::os) = catOpts os

  fun prProps' [] = ""
    | prProps' [p] = Syntax.pretty p
    | prProps' (p::ps) = Syntax.pretty p ^ ", " ^ (prProps' ps)

  fun prProps ps = "[" ^ prProps' ps ^ "]"

  fun prCtxs' [] = ""
    | prCtxs' [(p, ps)] = "<" ^ (Syntax.pretty p) ^ " | " ^ (prProps ps) ^ ">"
    | prCtxs' ((p, ps)::cs) = "<" ^ (Syntax.pretty p ^ " | " ^ prProps ps) ^ ">" ^ ", " ^ (prCtxs' cs)

  fun prCtxs cs = "[" ^ prCtxs' cs ^ "]"

  fun allCtxs G =
    let
      val implindxs : int list = catOpts (mapi getImpl G)
      fun rm i xs = catOpts (mapi (fn (j, x) => if not (i = j) then SOME x else NONE) xs)
      val res : (prop * prop list) list = map (fn i => (L.nth (G, i), rm i G)) implindxs
    in
      res
    end

  fun tryImplL G C : (derivation * derivation) list =
    let
      fun foo (A IMPL B, G') =
            (SOME (rightInv ((A IMPL B::G') || []) A, leftInv (G' || [B]) C)
            handle NoProof => NONE)
        | foo (_, _) = NONE
    in
      catOpts (List.map foo $ allCtxs G)
    end

  and rightInv (G || O) (ATOM P) =
        if L.exists (fn x => x = (ATOM P)) (G @ O)
        then
          let
            val _ = printLn "Right inversion (init)..."
            val _ = printLn $ "  |  " ^ (prProps G) ^ "; " ^ (prProps O)
          in
            ZeroInf (InitR, G || O ===> (ATOM P))
          end
        else
          let
            val _ = printLn "Right inversion (LR-P)...n"
            val _ = printLn $ "  |  " ^ (prProps G) ^ "; " ^ (prProps O)
          in
            leftInv $ G || O $ (ATOM P)
          end
    | rightInv (G || O) (A CONJ B) =
        let
          val _ = printLn "Right inversion (∧R)..."
          val _ = printLn $ "  |  " ^ (prProps G) ^ "; " ^ (prProps O)
        in
          let val (D1, D2) = (rightInv (G || O) A, rightInv (G || O) B)
          in TwoInf (ConjR, D1, D2, (G || O) ===> (A CONJ B)) end
        end
    | rightInv ctx TOP =
        let val _ = printLn "Right inversion (⊤R)..." in
          ZeroInf (TopR, ctx ===> TOP)
        end
    | rightInv (G || O) (A IMPL B) =
        let val _ = printLn "Right inversion (⊃R)..."
            val _ = printLn $ "  |  " ^ (prProps G) ^ "; " ^ (prProps O)
        in
          let val D1 = rightInv $ G || (A::O) $ B
          in OneInf (ImplR, D1, G || O ===> A IMPL B) end
        end
    | rightInv (G || O) (A DISJ B) =
        let
          val _ = printLn "Right inversion (LR-∨)..."
          val _ = printLn $ "  |  " ^ (prProps G) ^ "; " ^ (prProps O)
        in
          leftInv (G || O) $ A DISJ B
        end
    | rightInv ctx BOT =
        let val _ = printLn "Right inversion (LR-⊥)..." in
          leftInv ctx BOT
        end

  and leftInv (G || ((ATOM P)::O)) C =
        if (ATOM P) = C
        then
          let val _ = printLn "Left inversion (init)..." in
            ZeroInf (InitL, G || ((ATOM P)::O) ===> (ATOM P))
          end
        else
          let val _ = printLn "Left inversion (shift-P)..." in
            leftInv (((ATOM P)::G) || O) C
          end
    | leftInv (G || (A CONJ B::O)) C =
        let val _ = printLn "Left inversion (∧L)..." in
          let val D1 = leftInv $ G || (A::B::O) $ C
          in OneInf (ConjL, D1, G || (A CONJ B::O) ===> C) end
        end
    | leftInv (G || (A DISJ B::O)) C =
        let
          val _ = printLn "Left inversion (∨L)..."
          val _ = printLn $ "  |  " ^ (prProps G) ^ "; " ^ (prProps O)
          val (D1, D2) = (leftInv $ G || (A::O) $ C, leftInv $ G || (B::O) $ C)
        in
          TwoInf (DisjL, D1, D2, (G || (A DISJ B::O)) ===> C)
        end
    | leftInv (G || (TOP::O)) C =
        let val _ = printLn "Left inversion (⊤L)..." in
          let val D1 = leftInv $ G || O $ C
          in OneInf (TopL, D1, G || (TOP::O) ===> C) end
        end
    | leftInv (G || (BOT::O)) _ =
        let val _ = printLn "Left inversion (⊥L)..." in
          ZeroInf (BotL, G || (BOT::O) ===> BOT)
        end
    | leftInv (G || (A IMPL B::O)) C =
        let val _ = printLn "Left inversion (shift-⊃)..." in
          leftInv $ (A IMPL B::G) || O $ C
        end
    | leftInv (G || []) C = O.getOpt (search G C, raise NoProof)

  and search G (A DISJ B) =
        let
          val _  = printLn "Search (∨R1)..."
          val _ = printLn $ prProps G
        in
          SOME (rightInv (G || []) A)
          handle NoProof =>
            let
              val _  = printLn "Search (∨R2)..."
              val _  = printLn $ prProps G
            in (SOME $ rightInv (G || []) B handle NoProof => NONE) end
        end
    | search G C =
        let
          val _ = printLn "search (⊃L)"
          val _ = printLn $ prProps G
        in
          if L.exists isImpl G
          then (case tryImplL G C of
                  (D1, D2)::_ => SOME (TwoInf (ImplL, D1, D2, G || [] ===> C))
                | [] => NONE)
          else
            (printLn "impossible case happened\n"; raise Fail "impossible case")
        end

    fun prove P = SOME (rightInv $ [] || [] $ P) handle NoProof => NONE

  (*val prove =
    fn (ATOM P)   => NONE
     | (A CONJ B) => SOME (rightInv $ [] || [] $ A CONJ B)
     | (A DISJ B) => SOME (leftInv  $ [] || [] $ A DISJ B)
     | (A IMPL B) => SOME (rightInv $ [] || [] $ A IMPL B)
     | TOP        => SOME (rightInv $ [] || [] $ TOP)
     | BOT        => SOME (leftInv  $ [] || [] $ BOT)
    handle NoProf => NONE*)

end
