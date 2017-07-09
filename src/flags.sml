structure Flags = struct

  val shouldGenLaTeX = ref false
  val outFile : (string option) ref = ref NONE

  fun parseArgs [] = ()
    | parseArgs ("--latex"::rest) =
        (shouldGenLaTeX := true; parseArgs rest)
    | parseArgs ("--steps"::rest) = parseArgs rest
    | parseArgs ("--out"::file::rest) =
        (outFile := SOME file; parseArgs rest)

end
