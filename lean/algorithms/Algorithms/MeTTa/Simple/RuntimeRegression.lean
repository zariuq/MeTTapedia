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

private def runFixtureWithSyntax
    (syntaxSpec : MeTTailCore.MeTTaSyntax.SyntaxSpec)
    (text : String) : Diagnostics × List (Nat × List Pattern) :=
  let s0 := Session.withSyntax (Session.new emptyBundle) syntaxSpec
  let (s1, out) := Session.runText s0 text
  (Session.diagnostics s1, out)

private def queryOutputs (out : List (Nat × List Pattern)) : List (List Pattern) :=
  out.map Prod.snd

private def fixtureMatchesExpected (text : String) (expected : List (List Pattern)) : Bool :=
  let (diag, out) := runFixture text
  diag.errors = 0 && queryOutputs out = expected

private def fixtureMatchesExpectedWithSyntax
    (syntaxSpec : MeTTailCore.MeTTaSyntax.SyntaxSpec)
    (text : String) (expected : List (List Pattern)) : Bool :=
  let (diag, out) := runFixtureWithSyntax syntaxSpec text
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

def booleanSolverFocusedFixture : String :=
  String.intercalate "\n"
    [ "!(test (if (and (or $x True) $y) ($x $y))"
    , "       ((True True) (False True)))"
    , ""
    ]

def booleanNestedFocusedFixture : String :=
  String.intercalate "\n"
    [ "!(test (if (and (or $x True) $y) ($x $y) miss)"
    , "       ((True True) (False True)))"
    , "!(test (if (or (and $x $y) (and (not $x) $y)) ($x $y) miss)"
    , "       ((True True) (False True)))"
    , "!(test (if (and (< 1 2) $x) $x fallback)"
    , "       True)"
    , "!(test (if (and (> 1 2) $x) then else)"
    , "       else)"
    , "!(test (if (or (and $x (not $x)) (and (not $x) True)) $x bad)"
    , "       False)"
    , "!(test (if (and (== (+ 1 1) 2) (or $x False)) $x nope)"
    , "       True)"
    , "!(test (if (and (or $x False) (or (not $x) False)) branch else)"
    , "       else)"
    , "!(test (if (or $x (not $x)) (if $x T F) bad)"
    , "       (T F))"
    , "!(test (if (xor True False) ok bad)"
    , "       ok)"
    , "!(test (if (xor True True) ok bad)"
    , "       bad)"
    , "!(test (if (xor (== 2 2) (> 2 3)) ok bad)"
    , "       ok)"
    , "!(test (if (xor (== 2 2) (> 3 2)) ok bad)"
    , "       bad)"
    , "!(test (if (and (xor True False) (< 1 2)) pass fail)"
    , "       pass)"
    , "!(test (if (and (xor True False) (> 1 2)) pass fail)"
    , "       fail)"
    , "!(test (if (or (xor True True) (== (+ 1 1) 2)) yes no)"
    , "       yes)"
    , "!(test (if (xor (<= 2 2) (>= 3 3)) yes no)"
    , "       no)"
    , "!(test (if (xor (< 1 2) (> 1 2)) yes no)"
    , "       yes)"
    , "!(test (if (xor $x (not $x)) (if $x T F) bad)"
    , "       (T F))"
    , "!(test (if (and (xor $x $x) True) then else)"
    , "       else)"
    , "!(test (if (and (xor $x False) (xor $x True)) then else)"
    , "       else)"
    , ""
    ]

def stateFocusedFixture : String :=
  String.intercalate "\n"
    [ "!(bind! state (new-state rest))"
    , "!(get-state state)"
    , "!(change-state! state active)"
    , "!(get-state state)"
    , ""
    ]

def streamOpsFocusedFixture : String :=
  String.intercalate "\n"
    [ "!(collapse (unique (superpose (a b c d d))))"
    , "!(collapse (union (superpose (a b b c)) (superpose (b c c d))))"
    , "!(collapse (intersection (superpose (a b c c)) (superpose (b c c c d))))"
    , "!(collapse (subtraction (superpose (a b b c)) (superpose (b c c d))))"
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

def heSymRewriteFallbackFixture : String :=
  String.intercalate "\n"
    [ "(= (Expr (Sym f) (Sym a)) (Sym b))"
    , "(= (Expr (Sym wrap) $x) (Expr (Sym boxed) $x))"
    , "!(test (Expr (Sym f) (Sym a)) (Sym b))"
    , "!(test (Expr (Sym wrap) (Sym hi)) (Expr (Sym boxed) (Sym hi)))"
    , ""
    ]

def heAssertCommandsFixture : String :=
  String.intercalate "\n"
    [ "(= (coin) heads)"
    , "(= (coin) tails)"
    , "!(assertEqual (+ 1 2) 3)"
    , "!(assertEqualToResult (unknown arg) ((unknown arg)))"
    , "!(assertEqual (coin) (superpose (heads tails)))"
    , ""
    ]

def heMatchNormalizedFixture : String :=
  String.intercalate "\n"
    [ "(Expr (Sym f) (Sym a))"
    , "(Expr (Sym f) (Sym b))"
    , "!(msort (collapse (match &self (f $x) (hit $x))))"
    , "!(msort (collapse (match &self (Expr (Sym f) $x) (hit2 $x))))"
    , ""
    ]

def dispatchSharedOutputVarFixture : String :=
  String.intercalate "\n"
    [ "(= (id $v) $v)"
    , "(= (f (id (pair $x $x))) $x)"
    , "!(f (pair a a))"
    , "!(f (pair a b))"
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

private def booleanSolverFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["True"] ]

private def booleanNestedFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

private def stateFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["rest"]
  , parsePatterns ["True"]
  , parsePatterns ["active"]
  ]

private def streamOpsFocusedExpected : List (List Pattern) :=
  [ parsePatterns ["(a b c d)"]
  , parsePatterns ["(a b b c b c c d)"]
  , parsePatterns ["(b c c)"]
  , parsePatterns ["(a b)"]
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

private def heSymRewriteFallbackExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

private def heAssertCommandsExpected : List (List Pattern) :=
  [ parsePatterns ["True"]
  , parsePatterns ["True"]
  , parsePatterns ["True"]
  ]

private def heMatchNormalizedExpected : List (List Pattern) :=
  [ parsePatterns ["(Expr (hit a) (hit b))"]
  , parsePatterns ["(Expr (hit2 a) (hit2 b))"]
  ]

private def dispatchSharedOutputVarExpected : List (List Pattern) :=
  [ parsePatterns ["a"]
  , parsePatterns ["(f (pair a b))"]
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
def checkBooleanSolverFocusedFixture : Bool :=
  fixtureMatchesExpected booleanSolverFocusedFixture booleanSolverFocusedExpected
def checkBooleanNestedFocusedFixture : Bool :=
  fixtureMatchesExpected booleanNestedFocusedFixture booleanNestedFocusedExpected
def checkStateFocusedFixture : Bool :=
  fixtureMatchesExpected stateFocusedFixture stateFocusedExpected
def checkStreamOpsFocusedFixture : Bool :=
  fixtureMatchesExpected streamOpsFocusedFixture streamOpsFocusedExpected
def checkAtomOpsFocusedFixture : Bool :=
  fixtureMatchesExpected atomOpsFocusedFixture atomOpsFocusedExpected
def checkMetaEvalFocusedFixture : Bool :=
  fixtureMatchesExpected metaEvalFocusedFixture metaEvalFocusedExpected
def checkTypeImportFocusedFixture : Bool :=
  fixtureMatchesExpected typeImportFocusedFixture typeImportFocusedExpected
def checkPartialApplyFocusedFixture : Bool :=
  fixtureMatchesExpected partialApplyFocusedFixture partialApplyFocusedExpected
def checkHeSymRewriteFallbackFixture : Bool :=
  fixtureMatchesExpected heSymRewriteFallbackFixture heSymRewriteFallbackExpected
def checkHeAssertCommandsFixture : Bool :=
  fixtureMatchesExpected heAssertCommandsFixture heAssertCommandsExpected
def checkHeMatchNormalizedFixture : Bool :=
  fixtureMatchesExpectedWithSyntax
    MeTTailCore.MeTTaSyntax.he
    heMatchNormalizedFixture
    heMatchNormalizedExpected
def checkDispatchSharedOutputVarFixture : Bool :=
  fixtureMatchesExpected dispatchSharedOutputVarFixture dispatchSharedOutputVarExpected

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
  , ("booleanSolverFocusedFixture", checkBooleanSolverFocusedFixture)
  , ("booleanNestedFocusedFixture", checkBooleanNestedFocusedFixture)
  , ("stateFocusedFixture", checkStateFocusedFixture)
  , ("streamOpsFocusedFixture", checkStreamOpsFocusedFixture)
  , ("atomOpsFocusedFixture", checkAtomOpsFocusedFixture)
  , ("metaEvalFocusedFixture", checkMetaEvalFocusedFixture)
  , ("typeImportFocusedFixture", checkTypeImportFocusedFixture)
  , ("partialApplyFocusedFixture", checkPartialApplyFocusedFixture)
  , ("heSymRewriteFallbackFixture", checkHeSymRewriteFallbackFixture)
  , ("heAssertCommandsFixture", checkHeAssertCommandsFixture)
  , ("heMatchNormalizedFixture", checkHeMatchNormalizedFixture)
  , ("dispatchSharedOutputVarFixture", checkDispatchSharedOutputVarFixture)
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
#guard checkBooleanSolverFocusedFixture = true
#guard checkBooleanNestedFocusedFixture = true
#guard checkStateFocusedFixture = true
#guard checkStreamOpsFocusedFixture = true
#guard checkAtomOpsFocusedFixture = true
#guard checkMetaEvalFocusedFixture = true
#guard checkTypeImportFocusedFixture = true
#guard checkPartialApplyFocusedFixture = true
#guard checkHeSymRewriteFallbackFixture = true
#guard checkHeAssertCommandsFixture = true
#guard checkHeMatchNormalizedFixture = true
#guard checkDispatchSharedOutputVarFixture = true
#guard allRuntimeChecksPass = true

#eval allRuntimeChecks
#eval ("allRuntimeChecksPass", allRuntimeChecksPass)

end Algorithms.MeTTa.Simple.RuntimeRegression
