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
    fun loop f =
      let val dummyEOF = Tokens.EOF(0, 0)
          val input = valOf ( TextIO.output(TextIO.stdOut, "> ")
                            ; TextIO.flushOut(TextIO.stdOut)
                            ; TextIO.inputLine TextIO.stdIn)
          val prop = f input
      in
        printLn $ pretty prop;
        printLn "Searching...";
        (prove prop; printLn "Found derivation!");
        loop f
      end
      handle
        Fail s => (printLn $ "\027[31m" ^ s ^ "\027[0m"; loop f)
      | NoProof => (printLn "Could not find derivation"; loop f)
    end


  fun parseLoop () = loop Parser.parse

  fun main (arg0, argv) = (parseLoop (); 0)

  val _ = SMLofNJ.exportFn ("sequent",  main)

end
