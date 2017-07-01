structure Syntax = struct
  structure S = String

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

  fun pretty (ATOM x) = x
    | pretty (IMPL (p1, p2)) = parens $ (pretty p1) ^ " => " ^ (pretty p2)
    | pretty (CONJ (p1, p2)) = parens $ (pretty p1) ^ " /\\ " ^ (pretty p2)
    | pretty (DISJ (p1, p2)) = parens $ (pretty p1) ^ " \\/ " ^ (pretty p2)
    | pretty TOP = "T"
    | pretty BOT = "F"

end
