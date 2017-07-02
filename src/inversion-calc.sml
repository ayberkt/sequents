structure InvCalc = struct
  structure L = List
  structure O = Option
  structure SP = SearchReport
  open Syntax

  fun printLn s = ()
  (*fun printLn s = print (s ^ "\n")*)

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

  fun isImpl (_ IMPL _) = true
    | isImpl _ = false

  exception NoProof

  fun noProofFound () = (printLn "NoProof found.\n"; raise NoProof)

  fun getImpl (i, _ IMPL _) = SOME i
    | getImpl (_, _) = NONE

  fun catOpts [] = []
    | catOpts (SOME x::os) = x::(catOpts os)
    | catOpts (NONE::os) = catOpts os

  fun prCtxs' [] = ""
    | prCtxs' [(p, ps)] = "<" ^ (Syntax.pretty p) ^ " | " ^ (SP.prProps ps) ^ ">"
    | prCtxs' ((p, ps)::cs) = "<" ^ (Syntax.pretty p ^ " | " ^ SP.prProps ps) ^ ">" ^ ", " ^ (prCtxs' cs)

  fun prCtxs cs = "[" ^ prCtxs' cs ^ "]"

  fun allCtxs G =
    let
      val implindxs : int list = catOpts (mapi getImpl G)
      fun rm i xs = catOpts (mapi (fn (j, x) => if not (i = j) then SOME x else NONE) xs)
      val res : (prop * prop list) list = map (fn i => (L.nth (G, i), rm i G)) implindxs
    in
      if List.all (fn (p, _) => isImpl p) res
      then res
      else raise Fail "internal error"
    end

  fun wait () =
    (TextIO.inputLine TextIO.stdIn)

  fun rightInv (G || O) (ATOM P) bt =
        let
          val _ = printLn "Right inversion (atom)..."
        in
          if L.exists (fn x => x = (ATOM P)) G
          then
            let val _ = printLn $ "  |  This shows: " ^ SP.prSequent G O (ATOM P)
            in ZeroInf (InitR, G || O ===> (ATOM P)) end
          else
            (if bt
             then raise NoProof
             else
               let val _ = printLn "Right inversion (LR-P)..."
                   val _ = printLn $ "  |  NTS: " ^ SP.prSequent G O (ATOM P)
               in (leftInv $ G || O $ (ATOM P)
                  handle NoProof => (printLn $ "!!! Proof attempt failed."; noProofFound ()))
               end)
        end
    | rightInv (G || O) (A CONJ B) bt =
        let
          val _ = printLn "Right inversion (∧R)..."
          val _ = printLn $ "  |  " ^ (SP.prProps G) ^ "; " ^ (SP.prProps O)
        in
          let val (D1, D2) = (rightInv (G || O) A bt, rightInv (G || O) B bt)
          in TwoInf (ConjR, D1, D2, (G || O) ===> (A CONJ B)) end
        end
    | rightInv ctx TOP bt =
        let
          val _ = printLn "Right inversion (⊤R)..."
          val _ = printLn "Proof found for ⊤."
        in
          ZeroInf (TopR, ctx ===> TOP)
        end
    | rightInv (G || O) (A IMPL B) bt =
        let val _ = printLn "Right inversion (⊃R)..."
            val _ = printLn $ "  |  NTS: " ^ SP.prSequent G O (A IMPL B)
            val _ = printLn $ "  |  - New subgoal: " ^ SP.prSequent G (A::O) B
            val D1 = rightInv $ G || (A::O) $ B $ bt
        in OneInf (ImplR, D1, G || O ===> A IMPL B) end
    | rightInv (G || O) (A DISJ B) bt =
        let
          val _ = printLn "Right inversion (LR-∨)..."
          val _ = printLn $ "  |  NTS: " ^ (SP.prSequent G O (A DISJ B))
        in
          leftInv (G || O) (A DISJ B)
        end
    | rightInv ctx BOT bt =
        let val _ = printLn "Right inversion (LR-⊥)..." in
          leftInv ctx BOT
        end

  and leftInv (G || ((ATOM P)::O)) C =
        if (ATOM P) = C
        then
          let
            val _ = printLn "Left inversion (init)..."
            val _ = printLn $ "  |  " ^ (SP.prProps G) ^ "; " ^ (SP.prProps ((ATOM P)::O))
            val _ = printLn $ "  |  This proves " ^ (SP.prSequent (G) ((ATOM P)::O) C)
          in
            ZeroInf (InitL, G || ((ATOM P)::O) ===> (ATOM P))
          end
        else
          let
            val _ = printLn "Left inversion (shift-P)..."
            val _ = printLn $ "  |  NTS: " ^ (SP.prSequent ((ATOM P)::G) O C)
            val _ = printLn $ "  |  ---> shift " ^ P ^ " to the unordered context..."
          in
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
          val _ = printLn $ "  |  " ^ (SP.prProps G) ^ "; " ^ (SP.prProps (A DISJ B::O))
          val _ = printLn $ "  |  NTS: " ^ (Syntax.pretty $ C)
          val _ = printLn $ "  |  --> we will left invert " ^ (Syntax.pretty A)
          val _ = printLn $ "  |  --> we will left invert " ^ (Syntax.pretty B)
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
        let
          val _ = printLn "Left inversion (shift-⊃)..."
          val _ = printLn $ "  |  Shift " ^ Syntax.pretty (A IMPL B) ^ " to the unordered context"
          val _ = printLn $ "  |  NTS: " ^ SP.prSequent (A IMPL B::G) O C
        in
          leftInv $ (A IMPL B::G) || O $ C
        end
    | leftInv (G || []) C =
        case search G C of
          SOME D => D
        | NONE => (printLn "Raising NoProof\n"; noProofFound ())

  and search G (A DISJ B) =
        let
          val _ = printLn "Search (∨R1)..."
          val _ = printLn $ "  |  NTS: " ^ SP.prSequent G [] (A DISJ B)
          val _ = printLn $ "  |  - Subgoal 1: " ^ SP.prSequent G [] A
          val _ = printLn $ "!!! Beginning attempt at proof using (∨R1)"
        in
          SOME (OneInf (DisjR1, rightInv (G || []) A true, G || [] ===> A DISJ B))
          handle NoProof =>
            (let
              val _ = printLn "!!! Could not find proof."
              val _ = printLn "Search (∨R2)..."
              val _ = printLn $ "  |  " ^ (SP.prProps G) ^ "; " ^ (SP.prProps [])
              val _ = printLn $ "  |  Subgoal of " ^ (Syntax.pretty $ A DISJ B)
              val _ = printLn $ "  |  ---> will do right inversion on " ^ (Syntax.pretty B)
            in
              (SOME (OneInf (DisjR2, rightInv (G || []) B true, G || [] ===> A DISJ B)) handle NoProof => NONE)
            end)
        end
    | search G C =
        let
          val _ = printLn "Search (⊃L)"
          val _ = printLn $ "  |  NTS: " ^ (SP.prSequent G [] C)
        in
          if L.exists isImpl G
          then (case tryImplL G C of
                  D1::_ => (SOME D1)
                | [] => NONE)
          else NONE
        end

  and tryImplL (gamma : prop list) (C : prop) : derivation list =
    let
      val ctxs = allCtxs gamma
      val _ = printLn $ "  |  CONTEXTS:  " ^ prCtxs ctxs
      fun baz ((P DISJ Q) IMPL B, G) =
            let
              val _  = printLn $ "  |  ⊃L subgoal 1: " ^ SP.prSequent ((P DISJ Q) IMPL B::G) [] (P DISJ Q)
              val _  = printLn $ "  |  ⊃L subgoal 2: " ^ SP.prSequent G [B] C
              val D1 = rightInv (((P DISJ Q) IMPL B::G) || []) (P DISJ Q) true
              val D2 = leftInv (G || [B]) C
            in SOME (TwoInf (ImplL, D1, D2, gamma || [] ===> C)) handle NoProof => NONE end
        | baz (_, _) = (printLn "INTERNAL INCONSISTENCY!"; raise Fail "impossible case")
    in
      if List.exists isImpl gamma
      then catOpts (List.map baz (allCtxs gamma))
      else raise Fail "BUG"
    end

    fun prove P =
      SOME (rightInv $ [] || [] $ P $ false)
      handle NoProof => NONE

  (*val prove =
    fn (ATOM P)   => NONE
     | (A CONJ B) => SOME (rightInv $ [] || [] $ A CONJ B)
     | (A DISJ B) => SOME (leftInv  $ [] || [] $ A DISJ B)
     | (A IMPL B) => SOME (rightInv $ [] || [] $ A IMPL B)
     | TOP        => SOME (rightInv $ [] || [] $ TOP)
     | BOT        => SOME (leftInv  $ [] || [] $ BOT)
    handle NoProf => NONE*)

end
