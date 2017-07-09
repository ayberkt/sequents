structure Flags = struct

  type flags = {
    genLaTeX : bool,
    steps          : bool,
    outFile        : string option
  }

  val defaultFlgs = {
    genLaTeX = false,
    steps          = false,
    outFile        = NONE
  }

  fun mustGenLaTeX (flgs : flags) : flags =
    { genLaTeX = true
    , steps    = #steps flgs
    , outFile  = #outFile flgs }


  fun parseArgs flgs [] = flgs
    | parseArgs flgs ("--latex"::rest) = parseArgs (mustGenLaTeX flgs) rest
    | parseArgs flgs ("--steps"::rest) =
        let val flgs' = {
          genLaTeX = #genLaTeX flgs,
          steps = true,
          outFile = #outFile flgs
        }
        in parseArgs flgs' rest end
    | parseArgs flgs ("--out"::file::rest) =
        let
          val flgs' = {
            genLaTeX = #genLaTeX flgs,
            steps = #steps flgs,
            outFile = SOME file
          }
        in parseArgs flgs' rest end
    | parseArgs flgs (_::rest) = parseArgs flgs rest

end
