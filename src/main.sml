structure Main = struct
  open Parser
  open Syntax

  infixr 0 $

  local
    fun printLn s = print (s ^ "\n")
    open PropLrVals
  in
    fun loop f =
      let val dummyEOF = Tokens.EOF(0, 0)
          val input = valOf ( TextIO.output(TextIO.stdOut, "> ")
                            ; TextIO.flushOut(TextIO.stdOut)
                            ; TextIO.inputLine TextIO.stdIn)
          val result = f input
      in
        printLn $ pretty result;
        loop f
      end
    end


  fun parseLoop () = loop Parser.parse

  fun main (arg0, argv) = (parseLoop (); 0)

  val _ = SMLofNJ.exportFn ("sequent",  main)

end
