structure Flags : FLAGS = struct
  val flgShouldGenLaTeX = ref false
  val flgShouldGenTutch = ref false
  val flgOutFile : (string option) ref = ref NONE

  fun shouldGenLaTeX () = !flgShouldGenLaTeX
  fun shouldGenTutch () = !flgShouldGenTutch

  fun outFile () =
    case !flgOutFile of
      SOME file => file
    | NONE => raise Fail "outFile called before initialization"

  fun parseArgs [] = ()
    | parseArgs ("--latex"::rest) =
        (flgShouldGenLaTeX := true; parseArgs rest)
    | parseArgs ("--tutch"::rest) =
        (flgShouldGenTutch := true; parseArgs rest)
    | parseArgs ("--out"::file::rest) =
        (flgOutFile := SOME file; parseArgs rest)
    | parseArgs (arg::_) =
        (print ("Unrecognized argument: " ^ arg ^ "\n");
         OS.Process.exit OS.Process.failure)
end
