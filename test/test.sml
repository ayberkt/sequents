structure Test = struct
  open InvCalc
  open TextIO

  fun $ (f, x) = f x
  infix 0 $

  val failCount : int ref = ref 0

  val inputs =
    [
      ("A /\\ B => B /\\ A", true)
    , ("T", true)
    , ("A => T", true)
    , ("A => B => C => (A => B)", true)
    , ("T /\\ T", true)
    , ("T /\\ (T /\\ T)", true)
    , ("(T /\\ T) /\\ T", true)
    (*, ("(A \\/ B) => (B \\/ A)", true)*)

    , ("F", false)
    , ("A => F", false)
    , ("A /\\ B => A /\\ B /\\ C", false)
    ]

  fun test [] = ()
    | test ((i, r)::ts) =
        let
          val prop = Parser.parse i
        in
          (case (prove prop, r) of
            (SOME _, true) => print "SUCCESS.\n"
          | (NONE, false) => print "SUCCESS.\n"
          | (_, _) => (failCount := !failCount + 1; print "FAILURE.\n"));
          test ts
        end

  fun main (arg0, argv) =
    (test inputs;
     if !failCount = 0
     then 0
     else (print $ Int.toString (!failCount) ^ " tests failed.\n"; 1))

  val _ = SMLofNJ.exportFn ("test",  main)

end
