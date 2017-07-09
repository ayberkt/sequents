structure Flags = struct

  val shouldGenLaTeX = ref false

  fun parseArgs [] = ()
    | parseArgs ("--latex"::rest) =
        (shouldGenLaTeX := true; parseArgs rest)
    | parseArgs ("--steps"::rest) = parseArgs rest
    | parseArgs ("--out"::file::rest) = parseArgs rest

end
