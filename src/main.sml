structure Main = struct
  open Parser
  open Syntax
  open InvCalc
  open LaTeXGen

  infixr 0 $
  infixr 4 SeqL
  infixr 4 SeqR
  infix 5 ||

  local
    fun printLn s = print (s ^ "\n")
    open PropLrVals
  in
    fun main (arg0, argv) =
      let
        val prop = Parser.parse o valOf $ TextIO.inputLine TextIO.stdIn
      in
        case prove prop of
          SOME drv => (generate drv; 0)
        | NONE => (printLn "No proof found"; 1)
      end
  end

  val _ = SMLofNJ.exportFn ("sequent",  main)

end
