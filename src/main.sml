structure Main = struct
  open Parser

  fun main (arg0, argv) = (print "Hi!\n"; 0)

  val _ = SMLofNJ.exportFn ("sequent",  main)

end
