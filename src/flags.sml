structure Flags : FLAGS = struct
  val flgShouldGenLaTeX = ref false
  val flgOutFile : (string option) ref = ref NONE

  fun shouldGenLaTeX () = !flgShouldGenLaTeX

  fun outFile () =
    case !flgOutFile of
      SOME file => file
    | NONE => raise Fail "outFile called before initialization"

  fun parseArgs [] = ()
    | parseArgs ("--latex"::rest) =
        (flgShouldGenLaTeX := true; parseArgs rest)
    | parseArgs ("--steps"::rest) = parseArgs rest
    | parseArgs ("--out"::file::rest) =
        (flgOutFile := SOME file; parseArgs rest)
end
