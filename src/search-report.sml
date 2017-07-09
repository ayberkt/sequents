structure SearchReport = struct
  open Syntax
  open Utils
  open Color

  fun prProps' [] = ""
    | prProps' [p] = Syntax.pretty p
    | prProps' (p::ps) = Syntax.pretty p ^ ", " ^ (prProps' ps)

  fun prProps ps = "[" ^ prProps' (List.rev ps) ^ "]"

  fun prSequent G O C =
    format (Bright, White) ((prProps G) ^ "; " ^ (prProps O) ^ "  ---->  " ^ (Syntax.pretty C))

end
