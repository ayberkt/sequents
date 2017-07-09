structure Test = struct
  open Utils
  open Color
  structure S = String
  open TextIO

  fun $ (f, x) = f x
  infix 0 $

  val failCount : int ref = ref 0
  fun mustBe (x, y) = (x, y)
  infixr 3 mustBe

  (*val isProvable = isSome o prove o Parser.parse*)
  val provable = isSome o LJT.prove o Parser.parse

  val conjAssoc = "A /\\ (B /\\ C) => (A /\\ B) /\\ C"
  val conjComm  = "A /\\ B => B /\\ A"
  val implTrans = "(A => B) => (B => C) => (A => C)"
  val disjComm  = "A \\/ B => B \\/ A"
  val random1   = "(A \\/ B => C) => ((A => C) /\\ (B => C))"
  val random2   = "((A \\/ B \\/ C) => D) => ((A => D) /\\ (B => D) /\\ (C => D))"
  val random3   = "((A => B) => C) => D => D \\/ D"
  val curry     = "(A /\\ B => C) => (A => B => C)"
  val uncurry   = "(A => B => C) => (A /\\ B => C)"
  val projConjL = "A /\\ B => A"
  val projConjR = "A /\\ B => B"
  val impFst    = "A => (B => A)"
  val impSnd    = "A => (B => A)"
  val flip = "(A => B => C) => (B => A => C)"
  val tripleNeg = "(((A => F) => F) => F) => (A => F)"
  val long = "(((A => B) => C) => D) => (((A => B) => C) => D)"
  val long2 = "(((((A => B) => C) => D) => E) => F) => ((((A => B) => C) => D) => E) => F"
  val verylong = "(((((A => B) => C) => D) => E) => F) => (((((A => B) => C) => D) => E) => F) \\/ (((((A => B) => C) => D) => E) => F)"
  val glivenko = "((((A => B) => A) => A) => F) => F"
  val duality1 = "(A => F) \\/ (B => F) => (A /\\ B => F)"
  val duality2 = "((T => F) => F) /\\ (F => T => F)"
  val exFalsoQuodlibet = "F => A"

  fun simpleCase (s : string) true  = ("[LJT] " ^ s, provable s mustBe true)
    | simpleCase (s : string) false = ("[LJT] " ^ s ^ " not provable", provable s mustBe false)

  val testCases =
    [
      simpleCase "A => B => A" true
    , simpleCase "T" true

    , ("[LJT] Reflexivity of =>"        , provable "A => A"   mustBe true)
    , ("[LJT] A /\\ B => A"             , provable projConjL  mustBe true)
    , ("[LJT] A /\\ B => B"             , provable projConjR  mustBe true)
    , ("[LJT] Commutativity of /\\"     , provable conjComm   mustBe true)
    , ("[LJT] Transitivity of =>"       , provable implTrans  mustBe true)
    , ("[LJT] Commutativity \\/"        , provable disjComm   mustBe true)
    , ("[LJT] A => B => B"              , provable impSnd     mustBe true)
    , ("[LJT] Flip"                     , provable flip       mustBe true)
    , ("[LJT] Random (1)"               , provable random1    mustBe true)
    , ("[LJT] Random (2)"               , provable random2    mustBe true)
    , ("[LJT] Random (3)"               , provable random3    mustBe true)
    , ("[LJT] Duality (1)"              , provable duality1   mustBe true)
    , ("[LJT] Duality (2)"              , provable duality2   mustBe true)
    , ("[LJT] A => B => B"              , provable flip       mustBe true)
    , ("[LJT] Currying"                 , provable curry      mustBe true)
    , ("[LJT] Uncurrying"               , provable uncurry    mustBe true)
    , ("[LJT] Triple negation"          , provable tripleNeg  mustBe true)
    , ("[LJT] Long implication (1)"     , provable long       mustBe true)
    , ("[LJT] Long implication (2)"     , provable long2      mustBe true)
    , ("[LJT] Longer implication"       , provable verylong   mustBe true)
    , ("[LJT] Glivenko's theorem"       , provable glivenko   mustBe true)
    , ("[LJT] F => F"                   , provable "F => F"   mustBe true)
    , ("[LJT] Ex falso quodlibet"       , provable exFalsoQuodlibet  mustBe true)

    , simpleCase "F" false
    , simpleCase "T => F" false
    , simpleCase "A" false
    , simpleCase "A /\\ B" false
    , simpleCase "A \\/ B" false
    ]

  fun prBool true  = format (Bright, Green) "SUCCESS"
    | prBool false = format (Bright, Red) "FAILURE"

  fun printDots 0 = ()
    | printDots n = (print "."; printDots (n-1))

  fun mkSpace 0 = ""
    | mkSpace n = (" " ^ mkSpace (n-1))

  val digits = S.size o Int.toString

  fun prLineNum n =
    print $ (colorize LightBlue (Int.toString n)) ^ (mkSpace $ 4 - (digits n))

  fun testSuccessful (i, (dsc, (inp, out))) =
    (print $ (prLineNum (i+1); "| ");
     print $ format (Bright, White) (dsc ^ " ");
     printDots (60 - (String.size dsc));
     print $ " " ^ (prBool $ inp = out) ^ "\n";
     inp = out)

  fun allSuccessful ts =
    List.foldr (fn (p, q) => p andalso q) true (mapi testSuccessful ts)

  fun main (arg0, argv) =
    (if allSuccessful testCases
     then (print "\n--  All tests have passed.\n"; 0)
     else (print "\n-- Some of the tests have failed.\n"; 1))

  val _ = SMLofNJ.exportFn ("test",  main)

end
