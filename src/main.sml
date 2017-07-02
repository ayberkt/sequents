structure Main = struct
  open Parser
  open Syntax
  open InvCalc
  open LaTeXGen

  infixr 0 $
  infixr 4 ===>
  infix  5 ||

  type flags = {
    shouldGenLaTeX : bool,
    steps          : bool,
    outfile        : string option
  }

  val defaultFlgs = {
    shouldGenLaTeX = false,
    steps          = false,
    outFile        = NONE
  }

  fun parseArgs flgs [] = flgs
    | parseArgs flgs ("--latex"::rest) =
        let val flgs' = {
          shouldGenLaTeX = true,
          steps = #steps flgs,
          outFile = #outFile flgs
        }
        in parseArgs flgs' rest end
    | parseArgs flgs ("--steps"::rest) =
        let val flgs' = {
          shouldGenLaTeX = #shouldGenLaTeX flgs,
          steps = true,
          outFile = #outFile flgs
        }
        in parseArgs flgs' rest end
    | parseArgs flgs ("--out"::file::rest) =
        let
          val flgs' = {
            shouldGenLaTeX = #shouldGenLaTeX flgs,
            steps = #steps flgs,
            outFile = SOME file
          }
        in parseArgs flgs' rest end
    | parseArgs flgs (_::rest) = parseArgs flgs rest


  local
    fun printLn s = print (s ^ "\n")
    open PropLrVals
  in
    fun main (arg0, argv) =
      let
        val prop = Parser.parse o valOf $ TextIO.inputLine TextIO.stdIn
        val flgs = parseArgs defaultFlgs argv
      in
        (case prove prop of
          SOME drv =>
            (if #shouldGenLaTeX flgs
             then generate drv
             else printLn "Proof found!"; 0)
         | NONE => 1)
      end
  end

  val _ = SMLofNJ.exportFn ("sequent",  main)

end
