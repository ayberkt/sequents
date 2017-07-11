 structure Proofs = struct
  open Syntax

  datatype context =
      || of (prop list) * (prop list)

  datatype sequent = ===> of context * prop

  datatype rule =
      ConjR | ConjL  | TopR
    | ImplR | ImplL
    | Init
    | DisjL | DisjR1 | DisjR2
    | TopL  | BotL
    | AtomImplL
    | ConjImplL
    | TopImplL
    | DisjImplL
    | BotImplL
    | ImplImplL

  datatype derivation =
      ZeroInf of rule * sequent
    | OneInf  of rule * derivation * sequent
    | TwoInf  of rule * derivation * derivation * sequent

  fun getConc (ZeroInf (_, c)) = c
    | getConc (OneInf (_, _, c)) = c
    | getConc (TwoInf (_, _, _, c)) = c

 end
