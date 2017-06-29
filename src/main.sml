structure Main = struct
  open Parser
  open Syntax
  open InvCalc
  open LaTeXGen

  infixr 0 $
  infixr 4 SeqL
  infixr 4 SeqR
  infix 5 ||

  datatype flags =
    Flags of { shouldGenLaTeX : bool }

  val defaultFlgs = Flags { shouldGenLaTeX = false }

  fun parseArgs flgs [] = flgs
    | parseArgs flgs ("--latex"::rest) = parseArgs (Flags { shouldGenLaTeX = true} ) rest
    | parseArgs flgs (_::rest) = parseArgs flgs rest


  local
    fun printLn s = print (s ^ "\n")
    open PropLrVals
  in
    fun main (arg0, argv) =
      let
        val prop = Parser.parse o valOf $ TextIO.inputLine TextIO.stdIn
        val Flags { shouldGenLaTeX } = parseArgs defaultFlgs argv
      in
        case prove prop of
          SOME drv =>
            (if shouldGenLaTeX
             then generate drv
             else printLn "Proof found!"; 0)
        | NONE => (printLn "No proof found"; 1)
      end
  end

  val _ = SMLofNJ.exportFn ("sequent",  main)

end
