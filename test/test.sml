structure Test = struct
  open InvCalc
  open TextIO

  fun $ (f, x) = f x
  infix 0 $

  val failCount : int ref = ref 0

  val inputs =
    [
      ("A /\\ B => B /\\ A", true)
    , ("((A /\\ B) => (B /\\ A)) /\\ ((B /\\ A) => (A /\\ B))", true)
    , ("T", true)
    , ("A => T", true)
    , ("A => B => C => (A => B)", true)
    , ("T /\\ T", true)
    , ("T /\\ (T /\\ T)", true)
    , ("(T /\\ T) /\\ T", true)
    , ("(A \\/ B) => (B \\/ A)", true)
    , ("((A \\/ B) => (B \\/ A)) /\\ ((B \\/ A) => (A \\/ B))", true)
    , ("(A \\/ B) => (B \\/ A)", true)
    , ("(A => (B => (C => A)))", true)
    (*, ("((A \\/ B) => C) => ((A => C) /\\ (B => C))", true)*)

    , ("F", false)
    , ("A => F", false)
    , ("A /\\ B => A /\\ B /\\ C", false)
    ]

  fun test [] _ = ()
    | test ((i, r)::ts) n =
        (let val _ = print $ (Int.toString n) ^ "  "
             val prop = Parser.parse i
         in
           (case (prove prop, r) of
              (SOME _, true) => print "SUCCESS.\n"
            | (NONE, false) => print "SUCCESS.\n"
            | (_, _) => (failCount := !failCount + 1; print "FAILURE.\n"));
            test ts (n+1)
          end)
        handle _ => (failCount := !failCount + 1; print "FAILURE.\n"; test ts (n+1))

  fun main (arg0, argv) =
    (test inputs 0;
     if !failCount = 0
     then 0
     else (print $ Int.toString (!failCount) ^ " tests failed.\n"; 1))

  val _ = SMLofNJ.exportFn ("test",  main)

end
