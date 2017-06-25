structure Syntax = struct

  datatype prop =
      VAR of string
    | IMPLIES of prop * prop
    | CONJ of prop * prop
    | DISJ of prop * prop
    | TOP
    | BOT

end
