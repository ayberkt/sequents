signature FLAGS = sig
  val shouldGenLaTeX : unit -> bool
  val outFile : unit -> string
  val parseArgs : string list -> unit
end
