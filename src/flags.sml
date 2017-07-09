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

end
