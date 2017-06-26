structure SeqCalc = struct
  open List
  open Syntax
  infixr 0 $

  fun <$> (f, xs) = List.map f xs
  infixr 1 <$>

  type sequent = prop list * prop

  datatype rule =
      ConjR
    | ConjL
    | DisjR1
    | DisjR2
    | DisjL
    | ImplR
    | ImplL
    | TopR
    | TopL

  datatype derivation =
      Goal of sequent
    | ZeroInf of rule
    | OneInf of rule * derivation
    | TwoInf of rule * derivation * derivation

  infixr 5 CONJ
  infixr 5 DISJ
  infixr 5 IMPL

  infixr 2 ==>
  fun ctx ==> p = Goal (ctx, p)

  fun justified (Goal _) = false
    | justified (ZeroInf _)  = true
    | justified (OneInf (_, d)) = justified d
    | justified (TwoInf (_, d1, d2)) = justified d1 andalso justified d2

  val right =
    fn Goal (ctx, p CONJ q) => TwoInf (ConjR, ctx ==> p, ctx ==> p)
     | Goal (ctx, TOP) => ZeroInf TopR
     | Goal (ctx, p DISJ q) =>
         if justified $ OneInf (DisjR1, ctx ==> p)
         then OneInf (DisjR1, ctx ==> p)
         else OneInf (DisjR2, ctx ==> q)
     | Goal (ctx, p IMPL q) => OneInf (ImplR, p :: ctx ==> q)
     | Goal (_, BOT) => raise Fail "no ⊥R rule"
     | _ => raise Fail "right rule internal error"

  infixr 5 mem
  fun x mem xs = exists (fn y => x = y) xs

  fun prod _  [] = []
    | prod [] _  = []
    | prod (x::xs) ys = ((fn y => (x, y)) <$> ys) @ (prod xs ys)

end
