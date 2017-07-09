structure Flags = struct

  type flags = {
    genLaTeX : bool,
    steps          : bool,
    outfile        : string option
  }

  val defaultFlgs = {
    genLaTeX = false,
    steps          = false,
    outFile        = NONE
  }

end
