structure Syntax = struct
  structure S = String
  structure U = Unparse

  infixr 0 $
  fun f $ x = f x

  datatype prop =
      ATOM of S.string
    | IMPL of prop * prop
    | CONJ of prop * prop
    | DISJ of prop * prop
    | TOP
    | BOT

  fun parens s = "(" ^ s ^ ")"

  (*fun pretty (ATOM x) = x
    | pretty (IMPL (p1, p2)) = parens $ (pretty p1) ^ " ⊃ " ^ (pretty p2)
    | pretty (CONJ (p1, p2)) = parens $ (pretty p1) ^ " ∧ " ^ (pretty p2)
    | pretty (DISJ (p1, p2)) = parens $ (pretty p1) ^ " ∨ " ^ (pretty p2)
    | pretty TOP = "⊤"
    | pretty BOT = "⊥"*)
  fun unparse (ATOM X)       = U.atom X
    | unparse (CONJ(A, B))   = U.infix' (U.Right, 4, "∧") (unparse A, unparse B)
    | unparse (DISJ(A, B))   = U.infix' (U.Non,   3, "∨") (unparse A, unparse B)
    | unparse (IMPL(A, B))   = U.infix' (U.Non,   2, "⊃") (unparse A, unparse B)
    | unparse TOP            = U.atom "⊤"
    | unparse BOT            = U.atom "⊥"
  val pretty = U.parens o U.done o unparse

end
