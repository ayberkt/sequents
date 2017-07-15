structure Main = struct
  open Parser
  open Syntax
  open Flags
  open LaTeXGen
  structure F = Flags
  structure PE = PlainExplication
  structure P = Pos

  infixr 0 $ infixr 4 ===> infix  5 ||

  local
    fun printLn s = print (s ^ "\n")
    open PropLrVals
  in
    fun main (arg0, argv) =
      let
        val _ = Flags.parseArgs argv
        val prop =
          Parser.parse o valOf $ TextIO.inputLine TextIO.stdIn
          handle
            ParseError (p, s) => (print ("Error: " ^ P.toString p ^ "\n"); raise Fail "foo")
        val result =
          LJT.prove prop
          handle Fail s =>
            (printLn ("Internal error: " ^ s);
             OS.Process.exit OS.Process.failure)
      in
        (case result of
          SOME drv =>
            ((case (F.shouldGenLaTeX (), F.shouldGenTutch ()) of
                (true, _) => LaTeXGen.generate drv
              |  (_, true) => TutchGen.genTutch drv
              |  (_, _) => PE.explain prop drv); 0)
         | NONE => (PE.reportNotProvable prop; 1)
         handle _ => (print "Error\n"; 1))
      end
  end

  val _ = SMLofNJ.exportFn ("sequent",  main)

end
