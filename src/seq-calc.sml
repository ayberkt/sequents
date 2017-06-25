structure SeqCalc = struct
  open List
  open Syntax
  infixr 0 $

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
  infixr 5 IMPLIES

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
     | Goal (ctx, p IMPLIES q) => OneInf (ImplR, p :: ctx ==> q)
     | Goal (_, BOT) = failwith "no ⊥R rule"

end
