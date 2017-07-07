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
  val isCFProvable = isSome o LJT.prove o Parser.parse

  val conjAssoc = "A /\\ (B /\\ C) => (A /\\ B) /\\ C"
  val conjComm  = "A /\\ B => B /\\ A"
  val disjComm  = "A \\/ B => B \\/ A"
  val random1   = "(A \\/ B => C) => ((A => C) /\\ (B => C))"
  val random2   = "((A \\/ B \\/ C) => D) => ((A => D) /\\ (B => D) /\\ (C => D))"
  val currying     = "(A /\\ B => C) => (A => B => C)"
  val projConjL = "A /\\ B => A"
  val projConjR = "A /\\ B => B"
  val impFst    = "A => (B => A)"
  val impSnd    = "A => (B => A)"
  val premisesComm = "(A => B => C) => (B => A => C)"

  val proofTests =
    [
      ("[Inv] /\\-commutative"   , isProvable conjComm      mustBe true)
    , ("[Inv] A /\\ B => A"      , isProvable projConjL     mustBe true)
    , ("[Inv] A /\\ B => B"      , isProvable projConjR     mustBe true)
    , ("[Inv] /\\-associative"   , isProvable conjAssoc     mustBe true)
    , ("[Inv] A \\/ B => B \\/ A", isProvable disjComm      mustBe true)
    , ("[Inv] A => (B => A)"     , isProvable impFst        mustBe true)
    , ("[Inv] A => A"            , isProvable "A  => A"     mustBe true)
    , ("[Inv] random1"           , isProvable random1       mustBe true)
    , ("[Inv] random2"           , isProvable random2       mustBe true)
    , ("[Inv] "                  , isProvable premisesComm  mustBe true)
    , ("[Inv] currying"          , isProvable currying      mustBe true)
    , ("[Inv] uncurrying"        , isProvable "(A => B => C) => (A /\\ B => C)" mustBe true)
    , ("[Inv] F"                 , isProvable "F"         mustBe false)
    , ("[Inv] A => B"            , isProvable ("A => B")  mustBe false)
    , ("[Inv] A /\\ A"           , isProvable ("A /\\ A") mustBe false)
    , ("[Inv] A /\\ B"           , isProvable ("A /\\ B") mustBe false)
    , ("[Inv] A \\/ B"           , isProvable ("A \\/ B") mustBe false)

    , ("[LJT] T provable"            , isCFProvable "T" mustBe true)
    , ("[LJT] /\\ left elimination"  , isCFProvable projConjL mustBe true)
    , ("[LJT] /\\-commutative"       , isCFProvable conjComm mustBe true)
    , ("[LJT] \\/-commutative"       , isCFProvable disjComm mustBe true)
    , ("[LJT] /\\-elimination (left)", isCFProvable projConjL mustBe true)
    , ("[LJT] /\\-elimination (right)", isCFProvable projConjR mustBe true)
    (*, ("[LJT] currying"              , isCFProvable currying mustBe true)*)
    , ("[LJT] falsum not provable"   , isCFProvable "F" mustBe false)
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
        else (print "\n-- Some of the tests have failed.\n"; 1))
     else (print "Some of the unit tests have failed.\n"; 1))

  val _ = SMLofNJ.exportFn ("test",  main)

end
