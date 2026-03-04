import Algorithms.MeTTa.Simple.Session
import Algorithms.MeTTa.Simple.Parser

namespace Algorithms.MeTTa.Simple.RuntimeRegression

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Engine
open MeTTailCore.MeTTaIL.Profile
open Algorithms.MeTTa.Simple

private def emptyLanguage : LanguageDef := {
  name := "RuntimeRegression"
  types := []
  terms := []
  equations := []
  rewrites := []
  congruenceCollections := []
}

private def emptyBundle : SpecBundle := {
  language := emptyLanguage
  relationEnv := RelationEnv.empty
  builtins := coreIntrinsicBuiltins
  policy := {
    maxFuel := 128
    normalizeToFixedPoint := false
  }
}

private def parsePattern (text : String) : Pattern :=
  match Algorithms.MeTTa.Simple.Parser.parseExpr text with
  | Except.ok p => p
  | Except.error _ => .apply "__ParseError__" []

private def parsePatterns (xs : List String) : List Pattern :=
  xs.map parsePattern

private def runFixture (text : String) : Diagnostics × List (Nat × List Pattern) :=
  let s0 := Session.new emptyBundle
  let (s1, out) := Session.runText s0 text
  (Session.diagnostics s1, out)

private def queryOutputs (out : List (Nat × List Pattern)) : List (List Pattern) :=
  out.map Prod.snd

private def fixtureMatchesExpected (text : String) (expected : List (List Pattern)) : Bool :=
  let (diag, out) := runFixture text
  diag.errors = 0 && queryOutputs out = expected

def onceFixture : String :=
  String.intercalate "\n"
    [ "(foo 1)"
    , "(foo 2)"
    , ""
    , "(= (match-single $space $pat $ret)"
    , "   (once (match $space $pat $ret)))"
    , ""
    , "!(let $x (match-single &self (foo $1) $1) (add-atom &self (bar $x)))"
    , "!(test (collapse (match &self (bar $1) (bar $1)))"
    , "       ((bar 1)))"
    , ""
    ]

def cutFixture : String :=
  String.intercalate "\n"
    [ "(foo 1)"
    , "(foo 2)"
    , ""
    , "(= (match-single $space $pat $ret)"
    , "   (let* (($x (match $space $pat $ret))"
    , "          ($temp (cut)))"
    , "         $x))"
    , ""
    , "!(let $x (match-single &self (foo $1) $1) (add-atom &self (bar $x)))"
    , "!(test (collapse (match &self (bar $1) (bar $1)))"
    , "       ((bar 1)))"
    , ""
    ]

def spaceFixture : String :=
  String.intercalate "\n"
    [ "(foo 1)"
    , "(foo 2)"
    , "(foo 42 42)"
    , "(foo (42 42))"
    , ""
    , "!(bar 42)"
    , "!(bar 43)"
    , ""
    , "(= (answer) 42)"
    , ""
    , "!(test (space (msort (collapse (superpose ((match &self (foo $1) (foo $1))"
    , "                                           (match &self (foo $1 $2) (foo $1 $2))"
    , "                                           (match &self (bar $1) (bar $1)))))) (answer))"
    , "       (space ((foo 1) (foo 2) (foo 42 42) (foo (42 42))) 42))"
    , ""
    ]

def supercollapseFixture : String :=
  String.intercalate "\n"
    [ "(= (TupleConcat $Ev1 $Ev2) (collapse (superpose ((superpose $Ev1) (superpose $Ev2)))))"
    , ""
    , "(= (range $K $N)"
    , "   (if (< $K $N)"
    , "       (TupleConcat ($K) (range (+ $K 1) $N))"
    , "       ()))"
    , ""
    , "!(test (range 1 10)"
    , "       (1 2 3 4 5 6 7 8 9))"
    , ""
    ]

def superposeNestedFixture : String :=
  String.intercalate "\n"
    [ "(= (progme)"
    , "   ((collapse (superpose ((superpose (a b c)) (superpose (x y z)))))"
    , "    (collapse (superpose (a b c)))"
    , "    (collapse (superpose ((superpose (a b c)))))"
    , "    (collapse (superpose ((superpose (a b c)) x y z )))))"
    , ""
    , "!(test (progme)"
    , "       ((a x y z b c) (a b c) (a b c) (a x y z b c)))"
    , ""
    ]

def findFixture : String :=
  String.intercalate "\n"
    [ "(friend a b)"
    , "(friend b c)"
    , ""
    , "!(test (collapse (if (find &self (friend $a $b))"
    , "                     (if (find &self (friend $b $c))"
    , "                         (FoundChain $a $b $c)"
    , "                         (MissedSecondPiece))"
    , "                     (MissedAllPieces)))"
    , "       ((FoundChain a b c) (MissedSecondPiece)))"
    , ""
    ]

def succeedsPredicateFixture : String :=
  String.intercalate "\n"
    [ "!(test (succeedsPredicate (&self friend tim tom))"
    , "       False)"
    , ""
    , "(friend a b)"
    , "!(test (if (succeedsPredicate (&self friend $a $b))"
    , "           ($a $b)"
    , "           NotFound)"
    , "       (a b))"
    , ""
    ]

def spaceMatchSharingFixture : String :=
  String.intercalate "\n"
    [ "(link a a)"
    , "(link a b)"
    , "(link b c)"
    , "(link c c)"
    , ""
    , "!(msort (collapse (match &self (link $x $x) (same $x))))"
    , "!(msort (collapse (match (link $x $x) (same-default $x))))"
    , "!(msort (collapse (match &self (, (link $x $y) (link $y $z))"
    , "                        (chain $x $y $z))))"
    , "!(msort (collapse (match &self (, (link $x $x) (link $x $z))"
    , "                        (reuse $x $z))))"
    , ""
    ]

def predicateControlFixture : String :=
  String.intercalate "\n"
    [ "(friend a b)"
    , "(friend b c)"
    , ""
    , "!(collapse (translatePredicate (Predicate (&self friend $x $y))))"
    , "!(translatePredicate (catch (Predicate (&self friend tim tom)) $_ fail))"
    , "!(translatePredicate (catch (Predicate (&self friend a b)) $_ fail))"
    , "!(succeedsPredicate (&self friend a b))"
    , "!(succeedsPredicate (&self friend tim tom))"
    , ""
    ]

def nestedMatchHideFixture : String :=
  String.intercalate "\n"
    [ "(= (hide $1) (empty))"
    , ""
    , "!(hide ((add-atom &self (friend tim tom))"
    , "        (add-atom &self (friend tom tam))"
    , "        (add-atom &self (friend sim som))"
    , "        (add-atom &self (friend som sam))))"
    , ""
    , "!(hide (match &self (, (friend $1 $2) (friend $2 $3))"
    , "                    ((add-atom &self (transitive $1 $2 $3))"
    , "                     (remove-atom &self (friend $1 $2))"
    , "                     (remove-atom &self (friend $2 $3)))))"
    , ""
    , "!(test (msort (collapse (match &self (transitive $1 $2 $3) (transitive $1 $2 $3))))"
    , "       ((transitive sim som sam) (transitive tim tom tam)))"
    , ""
    ]

def translatePredicatePrognFixture : String :=
  String.intercalate "\n"
    [ "!(test (progn (translatePredicate (is $x 2))"
    , "              (translatePredicate (+ $x 40 $z)) $z)"
    , "       42)"
    , ""
    ]

def caseFocusedFixture : String :=
  String.intercalate "\n"
    [ "(= (classify $x) (case $x ((1 one) (2 two) (empty other))))"
    , "!(test (classify 1) one)"
    , "!(test (classify 3) other)"
    , "!(test (case 2 ((2 two) (empty miss))) two)"
    , ""
    ]

def foldallForallFocusedFixture : String :=
  String.intercalate "\n"
    [ "(= (f) 1)"
    , "(= (f) 2)"
    , "(= (merge $A $B) (+ $A $B))"
    , "(= (lt3 $X) (< $X 3))"
    , "!(test (foldall merge (f) 0) 3)"
    , "!(test (forall (f) lt3) True)"
    , "!(test (forall (f) (|-> ($v) (< $v 2))) False)"
    , ""
    ]

def predicateControlFocusedFixture : String :=
  String.intercalate "\n"
    [ "(friend a b)"
    , "(friend b c)"
    , "!(test (progn (translatePredicate (Predicate (&self friend $x $y)))"
    , "              ($x $y))"
    , "       (a b))"
    , "!(test (translatePredicate (catch (Predicate (&self friend tim tom)) $_ fail)) fail)"
    , "!(test (translatePredicate (catch (Predicate (&self friend a b)) $_ fail)) (friend a b))"
    , ""
    ]

def atomOpsFocusedFixture : String :=
  String.intercalate "\n"
    [ "!(test (cons-atom 1 (2 3)) (1 2 3))"
    , "!(test (car-atom (1 2 3)) 1)"
    , "!(test (cdr-atom (1 2 3)) (2 3))"
    , "!(test (index-atom (a b c) 1) b)"
    , "!(test (=alpha (foo $x) (foo $x)) True)"
    , "!(test (is-var $x) True)"
    , "!(test (is-var x) False)"
    , "(= (inc $x) (+ $x 1))"
    , "!(test (map-atom (1 2 3) inc) (2 3 4))"
    , ""
    ]

def metaEvalFocusedFixture : String :=
  String.intercalate "\n"
    [ "(= (inc $x) (+ $x 1))"
    , "!(test (call (quote (inc 1))) 2)"
    , "!(test (eval (quote (inc 2))) 3)"
    , "!(test (reduce (quote (inc 3))) 4)"
    , "!(test (chain (+ 2 4) $n (* 3 $n)) 18)"
    , ""
    ]

def typeImportFocusedFixture : String :=
  String.intercalate "\n"
    [ "(: foo Number)"
    , "!(test (get-type foo) Number)"
    , "!(test (is-var $x) True)"
    , "!(test (is-var foo) False)"
    , "!(test (import! &self \"dummy\") True)"
    , "!(test (add-translator-rule! (dummy-rule)) True)"
    , "!(test (remove-translator-rule! (dummy-rule)) True)"
    , ""
    ]

def partialApplyFocusedFixture : String :=
  String.intercalate "\n"
    [ "(= (add3 $a $b $c) (+ (+ $a $b) $c))"
    , "!(add3 1)"
    , "!(repr (add3 1))"
    , "!(test (add3 1 2 3) 6)"
    , "!(test (map-atom (1 2) (add3 10 20)) (31 32))"
    , ""
    ]

private def onceExpected : List (List Pattern) :=
  [ parsePatterns ["(bar 1)"]
  , parsePatterns ["True"]
  ]

private def cutExpected : List (List Pattern) :=
  [ parsePatterns ["(bar 1)"]
  , parsePatterns ["True"]
  ]

private def spaceExpected : List (List Pattern) :=
  [ parsePatterns ["(bar 42)"]
  , parsePatterns ["(bar 43)"]
  , parsePatterns ["True"]
  ]

private def supercollapseExpected : List (List Pattern) :=
  [ parsePatterns ["True"] ]

private def superposeNestedExpected : List (List Pattern) :=
  [ parsePatterns ["True"] ]

private def findExpected : List (List Pattern) :=
  [ parsePatterns ["True"] ]

private def succeedsPredicateExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

private def spaceMatchSharingExpected : List (List Pattern) :=
  [ parsePatterns ["((same a) (same c))"]
  , parsePatterns ["((same-default a) (same-default c))"]
  , parsePatterns ["((chain a a a) (chain a a b) (chain a b c) (chain b c c) (chain c c c))"]
  , parsePatterns ["((reuse a a) (reuse a b) (reuse c c))"]
  ]

private def predicateControlExpected : List (List Pattern) :=
  [ parsePatterns ["((friend a b) (friend b c))"]
  , parsePatterns ["fail"]
  , parsePatterns ["(friend a b)"]
  , parsePatterns ["True"]
  , parsePatterns ["False"]
  ]

private def nestedMatchHideExpected : List (List Pattern) :=
  [ parsePatterns ["empty"]
  , parsePatterns ["empty"]
  , parsePatterns ["True"]
  ]

private def translatePredicatePrognExpected : List (List Pattern) :=
  [ parsePatterns ["True"] ]

private def caseFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

private def foldallForallFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

private def predicateControlFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

private def atomOpsFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

private def metaEvalFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

private def typeImportFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

private def partialApplyFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["(partial add3 (1))"]
  , parsePatterns ["\"(partial add3 (1))\""]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

def checkOnceFixture : Bool := fixtureMatchesExpected onceFixture onceExpected
def checkCutFixture : Bool := fixtureMatchesExpected cutFixture cutExpected
def checkSpaceFixture : Bool := fixtureMatchesExpected spaceFixture spaceExpected
def checkSupercollapseFixture : Bool := fixtureMatchesExpected supercollapseFixture supercollapseExpected
def checkSuperposeNestedFixture : Bool := fixtureMatchesExpected superposeNestedFixture superposeNestedExpected
def checkFindFixture : Bool := fixtureMatchesExpected findFixture findExpected
def checkSucceedsPredicateFixture : Bool := fixtureMatchesExpected succeedsPredicateFixture succeedsPredicateExpected
def checkSpaceMatchSharingFixture : Bool := fixtureMatchesExpected spaceMatchSharingFixture spaceMatchSharingExpected
def checkPredicateControlFixture : Bool := fixtureMatchesExpected predicateControlFixture predicateControlExpected
def checkNestedMatchHideFixture : Bool := fixtureMatchesExpected nestedMatchHideFixture nestedMatchHideExpected
def checkTranslatePredicatePrognFixture : Bool := fixtureMatchesExpected translatePredicatePrognFixture translatePredicatePrognExpected
def checkCaseFocusedFixture : Bool := fixtureMatchesExpected caseFocusedFixture caseFocusedExpected
def checkFoldallForallFocusedFixture : Bool :=
  fixtureMatchesExpected foldallForallFocusedFixture foldallForallFocusedExpected
def checkPredicateControlFocusedFixture : Bool :=
  fixtureMatchesExpected predicateControlFocusedFixture predicateControlFocusedExpected
def checkAtomOpsFocusedFixture : Bool :=
  fixtureMatchesExpected atomOpsFocusedFixture atomOpsFocusedExpected
def checkMetaEvalFocusedFixture : Bool :=
  fixtureMatchesExpected metaEvalFocusedFixture metaEvalFocusedExpected
def checkTypeImportFocusedFixture : Bool :=
  fixtureMatchesExpected typeImportFocusedFixture typeImportFocusedExpected
def checkPartialApplyFocusedFixture : Bool :=
  fixtureMatchesExpected partialApplyFocusedFixture partialApplyFocusedExpected

def allRuntimeChecks : List (String × Bool) :=
  [ ("onceFixture", checkOnceFixture)
  , ("cutFixture", checkCutFixture)
  , ("spaceFixture", checkSpaceFixture)
  , ("supercollapseFixture", checkSupercollapseFixture)
  , ("superposeNestedFixture", checkSuperposeNestedFixture)
  , ("findFixture", checkFindFixture)
  , ("succeedsPredicateFixture", checkSucceedsPredicateFixture)
  , ("spaceMatchSharingFixture", checkSpaceMatchSharingFixture)
  , ("predicateControlFixture", checkPredicateControlFixture)
  , ("nestedMatchHideFixture", checkNestedMatchHideFixture)
  , ("translatePredicatePrognFixture", checkTranslatePredicatePrognFixture)
  , ("caseFocusedFixture", checkCaseFocusedFixture)
  , ("foldallForallFocusedFixture", checkFoldallForallFocusedFixture)
  , ("predicateControlFocusedFixture", checkPredicateControlFocusedFixture)
  , ("atomOpsFocusedFixture", checkAtomOpsFocusedFixture)
  , ("metaEvalFocusedFixture", checkMetaEvalFocusedFixture)
  , ("typeImportFocusedFixture", checkTypeImportFocusedFixture)
  , ("partialApplyFocusedFixture", checkPartialApplyFocusedFixture)
  ]

def allRuntimeChecksPass : Bool :=
  allRuntimeChecks.all (fun x => x.2)

#guard checkOnceFixture = true
#guard checkCutFixture = true
#guard checkSpaceFixture = true
#guard checkSupercollapseFixture = true
#guard checkSuperposeNestedFixture = true
#guard checkFindFixture = true
#guard checkSucceedsPredicateFixture = true
#guard checkSpaceMatchSharingFixture = true
#guard checkPredicateControlFixture = true
#guard checkNestedMatchHideFixture = true
#guard checkTranslatePredicatePrognFixture = true
#guard checkCaseFocusedFixture = true
#guard checkFoldallForallFocusedFixture = true
#guard checkPredicateControlFocusedFixture = true
#guard checkAtomOpsFocusedFixture = true
#guard checkMetaEvalFocusedFixture = true
#guard checkTypeImportFocusedFixture = true
#guard checkPartialApplyFocusedFixture = true
#guard allRuntimeChecksPass = true

#eval allRuntimeChecks
#eval ("allRuntimeChecksPass", allRuntimeChecksPass)

end Algorithms.MeTTa.Simple.RuntimeRegression
