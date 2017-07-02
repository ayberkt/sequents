structure Test = struct
  open InvCalc
  open TextIO

  fun $ (f, x) = f x
  infix 0 $

  val failCount : int ref = ref 0
  fun mustBe (x, y) = (x, y)
  infixr 3 mustBe

  fun unitTests () =
    [
      (*allCtxs [ATOM "A", IMPL (ATOM "P", ATOM "Q")]
        mustBe
      [(IMPL (ATOM "P", ATOM "Q"), [ATOM "A"])]
    , allCtxs [ATOM "A", DISJ (ATOM "X", ATOM "Y"), IMPL (ATOM "P", ATOM "Q")]
      mustBe
      [(IMPL (ATOM "P", ATOM "Q"), [ATOM "A", DISJ (ATOM "X", ATOM "Y")])]
    , allCtxs [IMPL (ATOM "A", ATOM "B"), IMPL (ATOM "P", ATOM "Q"), ATOM "A", ATOM "Q"]
      mustBe
      [ (IMPL (ATOM "A", ATOM "B"), [IMPL (ATOM "P", ATOM "Q"), ATOM "A", ATOM "Q"])
      , (IMPL (ATOM "P", ATOM "Q"), [IMPL (ATOM "A", ATOM "B"), ATOM "A", ATOM "Q"])
      ]*)
    ]

  val isProvable = isSome o prove o Parser.parse

  val conjAssoc = "A /\\ (B /\\ C) => (A /\\ B) /\\ C"
  val conjComm  = "A /\\ B => B /\\ A"
  val random1   = "(A \\/ B => C) => ((A => C) /\\ (B => C))"
  val random2   = "((A \\/ B \\/ C) => D) => ((A => D) /\\ (B => D) /\\ (C => D))"

  val proofTests =
    [
      (conjComm            , isProvable conjComm               mustBe true)
    , ("A /\\ B => A"      , isProvable ("A /\\ B => A")       mustBe true)
    , ("A /\\ B => B"      , isProvable ("A /\\ B => B")       mustBe true)
    , (conjAssoc           , isProvable conjAssoc              mustBe true)
    , ("A \\/ B => B \\/ A", isProvable ("A \\/ B => B \\/ A") mustBe true)
    , ("A => (B => A)"     , isProvable ("A => (B => A)")      mustBe true)
    , ("A => (B => A)"     , isProvable ("A => (B => A)")      mustBe true)
    , ("A => A"            , isProvable ("A => (B => A)")      mustBe true)
    , ("random1", isProvable random1 mustBe true)
    , ("random2", isProvable random2 mustBe true)
    , ("(A => B => C) => (B => A => C)", isProvable "(A => B => C) => (B => A => C)" mustBe true)
    , ("currying", isProvable "(A /\\ B => C) => (A => B => C)" mustBe true)
    , ("uncurrying", isProvable "(A => B => C) => (A /\\ B => C)" mustBe true)
    (*, ("triple negation", isProvable tripleNeg mustBe true)*)

    , ("F"                 , isProvable "F"                    mustBe false)
    , ("A => B"            , isProvable ("A => B")             mustBe false)
    , ("A /\\ A"           , isProvable ("A /\\ A")            mustBe false)
    , ("A /\\ B"           , isProvable ("A /\\ B")            mustBe false)
    , ("A \\/ B"           , isProvable ("A \\/ B")            mustBe false)
    ]

  fun prBool true  = "SUCCESS"
    | prBool false = "FAILURE"

  fun printDots 0 = ()
    | printDots n = (print "."; printDots (n-1))

  fun mkSpace 0 = ""
    | mkSpace n = (" " ^ mkSpace (n-1))

  val digits = S.size o Int.toString

  fun prLineNum n =
    print $  (Int.toString n) ^ (mkSpace $ 4 - (digits n))

  fun testSuccessful (i, (dsc, (inp, out))) =
  (
    print $ (prLineNum (i+1); "| ");
    print $ "Testing " ^ dsc ^ " ";
    printDots (60 - (String.size dsc));
    print $ " " ^ (prBool $ inp = out) ^ "\n";
    inp = out
  )

  fun allSuccessful ts = List.foldr (fn (p, q) => p andalso q) true (mapi testSuccessful ts)

  fun main (arg0, argv) =
    (if allSuccessful (unitTests ())
     then
       (if allSuccessful proofTests
        then (print "\n--  All tests have passed.\n"; 0)
        else (print "Some of the proof tests have failed.\n"; 1))
     else (print "Some of the unit tests have failed.\n"; 1))

  val _ = SMLofNJ.exportFn ("test",  main)

end
