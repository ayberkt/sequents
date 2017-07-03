structure Test = struct
  open InvCalc
  structure CF = ContFree
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
  val isCFProvable = isSome o CF.prove o Parser.parse

  val conjAssoc = "A /\\ (B /\\ C) => (A /\\ B) /\\ C"
  val conjComm  = "A /\\ B => B /\\ A"
  val random1   = "(A \\/ B => C) => ((A => C) /\\ (B => C))"
  val random2   = "((A \\/ B \\/ C) => D) => ((A => D) /\\ (B => D) /\\ (C => D))"
  val curry     = "(A /\\ B => C) => (A => B => C)"
  val projConjL = "A /\\ B => A"
  val projConjR = "A /\\ B => B"

  val proofTests =
    [
      ("[Inversion] /\\-commutative"   , isProvable conjComm    mustBe true)
    , ("[Inversion] A /\\ B => A"      , isProvable projConjL   mustBe true)
    , ("[Inversion] A /\\ B => B"      , isProvable projConjR   mustBe true)
    , ("[Inversion] /\\-associative"   , isProvable conjAssoc   mustBe true)
    , ("[Inversion] A \\/ B => B \\/ A", isProvable ("A \\/ B => B \\/ A") mustBe true)
    , ("[Inversion] A => (B => A)"     , isProvable ("A => (B => A)")      mustBe true)
    , ("[Inversion] A => (B => A)"     , isProvable ("A => (B => A)")      mustBe true)
    , ("[Inversion] A => A"            , isProvable ("A => (B => A)")      mustBe true)
    , ("[Inversion] random1", isProvable random1 mustBe true)
    , ("[Inversion] random2", isProvable random2 mustBe true)
    , ("[Inversion] (A => B => C) => (B => A => C)", isProvable "(A => B => C) => (B => A => C)" mustBe true)
    , ("[Inversion] currying"          , isProvable curry         mustBe true)
    , ("[Inversion] uncurrying"        , isProvable "(A => B => C) => (A /\\ B => C)" mustBe true)
    , ("[Inversion] F"                 , isProvable "F"         mustBe false)
    , ("[Inversion] A => B"            , isProvable ("A => B")  mustBe false)
    , ("[Inversion] A /\\ A"           , isProvable ("A /\\ A") mustBe false)
    , ("[Inversion] A /\\ B"           , isProvable ("A /\\ B") mustBe false)
    , ("[Inversion] A \\/ B"           , isProvable ("A \\/ B") mustBe false)

    , ("[Cont-free] /\\-commutative"   , isCFProvable projConjL  mustBe true)
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
    print $ dsc ^ " ";
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
