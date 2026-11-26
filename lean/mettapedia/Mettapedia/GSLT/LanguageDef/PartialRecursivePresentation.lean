import Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
import Mathlib.Computability.Halting

/-!
# Partial recursive functions as a rule presentation

One fixed sorted first-order rule presentation, without binders and without
equations, derives the graph of every partial recursive function. Its sorts
are numerals, codes and judgments. Numerals are built from zero and
successor, and codes from the eight constructors of `Nat.Partrec.Code`.
Judgments state addition, multiplication, the two orders, the pairing
function `Nat.pair`, evaluation of a code, the stages of primitive
recursion, the stages of unbounded search, and halting. Each rule is a
Horn clause over these judgments.

`derives_iff` proves that a closed judgment is derivable exactly when it is
true. In particular `derives_eval_iff`: the presentation derives that code
`c` sends `n` to `m` exactly when `m ∈ c.eval n`, and `derives_halts_iff`:
it derives that `c` halts on `n` exactly when `c.eval n` is defined.

Soundness is proved by interpretation. Every pattern denotes a number and
a code, with every other pattern read as zero, and every rule preserves
truth under that reading. No typing information is needed for it.
Completeness builds a derivation from the evaluation of the code.

With the halting theorems of Mathlib this fixes where derivability in the
presentation lies. For every recursively enumerable predicate on numbers
some code represents it by its halting judgments
(`every_re_represented`). The halting judgments of a fixed input are
recursively enumerable and not computable (`halts_re`,
`halts_undecidable`), and their complement is not recursively enumerable
(`not_derivable_not_re`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PartialRecursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Nat.Partrec (Code)

/-! ## The language -/

abbrev natSort : TypeExpr := .base "nat"
abbrev codeSort : TypeExpr := .base "code"

/-- Parameter names of a term former; no former has more than five arguments. -/
def parameterNames : List String := ["p0", "p1", "p2", "p3", "p4"]

/-- A term former of a category, with simple parameters of the given sorts. -/
def former (label category : String) (sorts : List TypeExpr) : GrammarRule :=
  { label := label, category := category
    params := (parameterNames.zip sorts).map fun entry => .simple entry.1 entry.2
    syntaxPattern := [] }

/-- Numerals, codes, and one sort of judgments. -/
def language : LanguageDef :=
  { name := "PartialRecursive"
    types := [TypeDecl.plain "nat", TypeDecl.plain "code", TypeDecl.plain "wff"]
    terms := [
      former "zero" "nat" [],
      former "succ" "nat" [natSort],
      former "czero" "code" [],
      former "csucc" "code" [],
      former "cleft" "code" [],
      former "cright" "code" [],
      former "cpair" "code" [codeSort, codeSort],
      former "ccomp" "code" [codeSort, codeSort],
      former "cprec" "code" [codeSort, codeSort],
      former "crfind" "code" [codeSort],
      former "add" "wff" [natSort, natSort, natSort],
      former "mul" "wff" [natSort, natSort, natSort],
      former "lt" "wff" [natSort, natSort],
      former "le" "wff" [natSort, natSort],
      former "pair" "wff" [natSort, natSort, natSort],
      former "eval" "wff" [codeSort, natSort, natSort],
      former "prec" "wff" [codeSort, codeSort, natSort, natSort, natSort],
      former "search" "wff" [codeSort, natSort, natSort, natSort],
      former "halts" "wff" [codeSort, natSort]]
    equations := []
    rewrites := [] }

theorem former_notBare (label category : String) (sorts : List TypeExpr)
    (simple : ∀ sort ∈ sorts, ∃ name, sort = .base name) :
    ¬ UsesBareCollection (former label category sorts) := by
  rintro ⟨parameterName, collectionType, elementType, shape⟩
  cases sorts with
  | nil => simp [former] at shape
  | cons sort rest =>
      obtain ⟨name, rfl⟩ := simple sort (by simp)
      simp [former, parameterNames] at shape

/-! ## Patterns -/

/-- A metavariable of a rule. -/
def mv (name : String) : Pattern := .fvar name

def zeroP : Pattern := .apply "zero" []
def succP (n : Pattern) : Pattern := .apply "succ" [n]
def czeroP : Pattern := .apply "czero" []
def csuccP : Pattern := .apply "csucc" []
def cleftP : Pattern := .apply "cleft" []
def crightP : Pattern := .apply "cright" []
def cpairP (f g : Pattern) : Pattern := .apply "cpair" [f, g]
def ccompP (f g : Pattern) : Pattern := .apply "ccomp" [f, g]
def cprecP (f g : Pattern) : Pattern := .apply "cprec" [f, g]
def crfindP (f : Pattern) : Pattern := .apply "crfind" [f]
def addP (a b c : Pattern) : Pattern := .apply "add" [a, b, c]
def mulP (a b c : Pattern) : Pattern := .apply "mul" [a, b, c]
def ltP (a b : Pattern) : Pattern := .apply "lt" [a, b]
def leP (a b : Pattern) : Pattern := .apply "le" [a, b]
def pairP (a b c : Pattern) : Pattern := .apply "pair" [a, b, c]
def evalP (f n m : Pattern) : Pattern := .apply "eval" [f, n, m]
def precP (f g a k m : Pattern) : Pattern := .apply "prec" [f, g, a, k, m]
def searchP (f a s j : Pattern) : Pattern := .apply "search" [f, a, s, j]
def haltsP (c n : Pattern) : Pattern := .apply "halts" [c, n]

/-- The numeral of a number. -/
def num : ℕ → Pattern
  | 0 => zeroP
  | n + 1 => succP (num n)

/-- The pattern of a code. -/
def codePattern : Code → Pattern
  | .zero => czeroP
  | .succ => csuccP
  | .left => cleftP
  | .right => crightP
  | .pair f g => cpairP (codePattern f) (codePattern g)
  | .comp f g => ccompP (codePattern f) (codePattern g)
  | .prec f g => cprecP (codePattern f) (codePattern g)
  | .rfind' f => crfindP (codePattern f)

/-! ## The rules -/

/-- A rule with typed metavariables. -/
def inference (id : String) (formals : List (String × TypeExpr)) (premises : List Pattern)
    (conclusion : Pattern) : SortedFirstOrderRules.Rule where
  row := { id := id, vars := formals.map Prod.fst, premises := premises, conclusion := conclusion }
  variableTypes := formals.map Prod.snd

def addZero := inference "addZero" [("a", natSort)] []
  (addP (mv "a") zeroP (mv "a"))
def addSucc := inference "addSucc" [("a", natSort), ("b", natSort), ("c", natSort)]
  [addP (mv "a") (mv "b") (mv "c")]
  (addP (mv "a") (succP (mv "b")) (succP (mv "c")))
def mulZero := inference "mulZero" [("a", natSort)] []
  (mulP (mv "a") zeroP zeroP)
def mulSucc := inference "mulSucc"
  [("a", natSort), ("b", natSort), ("c", natSort), ("d", natSort)]
  [mulP (mv "a") (mv "b") (mv "c"), addP (mv "c") (mv "a") (mv "d")]
  (mulP (mv "a") (succP (mv "b")) (mv "d"))
def ltZero := inference "ltZero" [("b", natSort)] []
  (ltP zeroP (succP (mv "b")))
def ltSucc := inference "ltSucc" [("a", natSort), ("b", natSort)]
  [ltP (mv "a") (mv "b")]
  (ltP (succP (mv "a")) (succP (mv "b")))
def leZero := inference "leZero" [("b", natSort)] []
  (leP zeroP (mv "b"))
def leSucc := inference "leSucc" [("a", natSort), ("b", natSort)]
  [leP (mv "a") (mv "b")]
  (leP (succP (mv "a")) (succP (mv "b")))
/-- `Nat.pair a b = b * b + a` when `a < b`. -/
def pairBelow := inference "pairBelow"
  [("a", natSort), ("b", natSort), ("s", natSort), ("c", natSort)]
  [ltP (mv "a") (mv "b"), mulP (mv "b") (mv "b") (mv "s"), addP (mv "s") (mv "a") (mv "c")]
  (pairP (mv "a") (mv "b") (mv "c"))
/-- `Nat.pair a b = a * a + a + b` when `b ≤ a`. -/
def pairAbove := inference "pairAbove"
  [("a", natSort), ("b", natSort), ("s", natSort), ("t", natSort), ("c", natSort)]
  [leP (mv "b") (mv "a"), mulP (mv "a") (mv "a") (mv "s"), addP (mv "s") (mv "a") (mv "t"),
    addP (mv "t") (mv "b") (mv "c")]
  (pairP (mv "a") (mv "b") (mv "c"))
def evalZero := inference "evalZero" [("n", natSort)] []
  (evalP czeroP (mv "n") zeroP)
def evalSucc := inference "evalSucc" [("n", natSort)] []
  (evalP csuccP (mv "n") (succP (mv "n")))
def evalLeft := inference "evalLeft" [("n", natSort), ("a", natSort), ("b", natSort)]
  [pairP (mv "a") (mv "b") (mv "n")]
  (evalP cleftP (mv "n") (mv "a"))
def evalRight := inference "evalRight" [("n", natSort), ("a", natSort), ("b", natSort)]
  [pairP (mv "a") (mv "b") (mv "n")]
  (evalP crightP (mv "n") (mv "b"))
def evalPair := inference "evalPair"
  [("f", codeSort), ("g", codeSort), ("n", natSort), ("a", natSort), ("b", natSort),
    ("m", natSort)]
  [evalP (mv "f") (mv "n") (mv "a"), evalP (mv "g") (mv "n") (mv "b"),
    pairP (mv "a") (mv "b") (mv "m")]
  (evalP (cpairP (mv "f") (mv "g")) (mv "n") (mv "m"))
def evalComp := inference "evalComp"
  [("f", codeSort), ("g", codeSort), ("n", natSort), ("k", natSort), ("m", natSort)]
  [evalP (mv "g") (mv "n") (mv "k"), evalP (mv "f") (mv "k") (mv "m")]
  (evalP (ccompP (mv "f") (mv "g")) (mv "n") (mv "m"))
def precZero := inference "precZero"
  [("f", codeSort), ("g", codeSort), ("a", natSort), ("m", natSort)]
  [evalP (mv "f") (mv "a") (mv "m")]
  (precP (mv "f") (mv "g") (mv "a") zeroP (mv "m"))
def precSucc := inference "precSucc"
  [("f", codeSort), ("g", codeSort), ("a", natSort), ("k", natSort), ("i", natSort),
    ("p", natSort), ("q", natSort), ("m", natSort)]
  [precP (mv "f") (mv "g") (mv "a") (mv "k") (mv "i"), pairP (mv "k") (mv "i") (mv "p"),
    pairP (mv "a") (mv "p") (mv "q"), evalP (mv "g") (mv "q") (mv "m")]
  (precP (mv "f") (mv "g") (mv "a") (succP (mv "k")) (mv "m"))
def evalPrec := inference "evalPrec"
  [("f", codeSort), ("g", codeSort), ("a", natSort), ("k", natSort), ("n", natSort),
    ("m", natSort)]
  [pairP (mv "a") (mv "k") (mv "n"), precP (mv "f") (mv "g") (mv "a") (mv "k") (mv "m")]
  (evalP (cprecP (mv "f") (mv "g")) (mv "n") (mv "m"))
def searchZero := inference "searchZero" [("f", codeSort), ("a", natSort), ("s", natSort)] []
  (searchP (mv "f") (mv "a") (mv "s") zeroP)
def searchSucc := inference "searchSucc"
  [("f", codeSort), ("a", natSort), ("s", natSort), ("j", natSort), ("t", natSort),
    ("q", natSort), ("w", natSort)]
  [searchP (mv "f") (mv "a") (mv "s") (mv "j"), addP (mv "j") (mv "s") (mv "t"),
    pairP (mv "a") (mv "t") (mv "q"), evalP (mv "f") (mv "q") (succP (mv "w"))]
  (searchP (mv "f") (mv "a") (mv "s") (succP (mv "j")))
def evalSearch := inference "evalSearch"
  [("f", codeSort), ("a", natSort), ("s", natSort), ("j", natSort), ("t", natSort),
    ("q", natSort), ("n", natSort)]
  [searchP (mv "f") (mv "a") (mv "s") (mv "j"), addP (mv "j") (mv "s") (mv "t"),
    pairP (mv "a") (mv "t") (mv "q"), evalP (mv "f") (mv "q") zeroP,
    pairP (mv "a") (mv "s") (mv "n")]
  (evalP (crfindP (mv "f")) (mv "n") (mv "t"))
def halting := inference "halting" [("c", codeSort), ("n", natSort), ("m", natSort)]
  [evalP (mv "c") (mv "n") (mv "m")]
  (haltsP (mv "c") (mv "n"))

/-- Arithmetic, pairing, evaluation of every code constructor, and halting. -/
def rules : List SortedFirstOrderRules.Rule :=
  [addZero, addSucc, mulZero, mulSucc, ltZero, ltSucc, leZero, leSucc, pairBelow, pairAbove,
    evalZero, evalSucc, evalLeft, evalRight, evalPair, evalComp, precZero, precSucc, evalPrec,
    searchZero, searchSucc, evalSearch, halting]

/-! ## Rule instances -/

section Instances

variable (a b c d e f g h : Pattern)

theorem addZero_conclusion : addZero.row.instConclusion [a] = addP a zeroP a := by
  simp [addZero, inference, FORule.instConclusion, FORule.bindings, applyBindings, addP, zeroP,
    mv]

theorem addSucc_premises : addSucc.row.instPremises [a, b, c] = [addP a b c] := by
  simp [addSucc, inference, FORule.instPremises, FORule.bindings, applyBindings, addP, mv]

theorem addSucc_conclusion :
    addSucc.row.instConclusion [a, b, c] = addP a (succP b) (succP c) := by
  simp [addSucc, inference, FORule.instConclusion, FORule.bindings, applyBindings, addP, succP,
    mv]

theorem mulZero_conclusion : mulZero.row.instConclusion [a] = mulP a zeroP zeroP := by
  simp [mulZero, inference, FORule.instConclusion, FORule.bindings, applyBindings, mulP, zeroP,
    mv]

theorem mulSucc_premises :
    mulSucc.row.instPremises [a, b, c, d] = [mulP a b c, addP c a d] := by
  simp [mulSucc, inference, FORule.instPremises, FORule.bindings, applyBindings, mulP, addP, mv]

theorem mulSucc_conclusion : mulSucc.row.instConclusion [a, b, c, d] = mulP a (succP b) d := by
  simp [mulSucc, inference, FORule.instConclusion, FORule.bindings, applyBindings, mulP, succP,
    mv]

theorem ltZero_conclusion : ltZero.row.instConclusion [a] = ltP zeroP (succP a) := by
  simp [ltZero, inference, FORule.instConclusion, FORule.bindings, applyBindings, ltP, zeroP,
    succP, mv]

theorem ltSucc_premises : ltSucc.row.instPremises [a, b] = [ltP a b] := by
  simp [ltSucc, inference, FORule.instPremises, FORule.bindings, applyBindings, ltP, mv]

theorem ltSucc_conclusion : ltSucc.row.instConclusion [a, b] = ltP (succP a) (succP b) := by
  simp [ltSucc, inference, FORule.instConclusion, FORule.bindings, applyBindings, ltP, succP, mv]

theorem leZero_conclusion : leZero.row.instConclusion [a] = leP zeroP a := by
  simp [leZero, inference, FORule.instConclusion, FORule.bindings, applyBindings, leP, zeroP, mv]

theorem leSucc_premises : leSucc.row.instPremises [a, b] = [leP a b] := by
  simp [leSucc, inference, FORule.instPremises, FORule.bindings, applyBindings, leP, mv]

theorem leSucc_conclusion : leSucc.row.instConclusion [a, b] = leP (succP a) (succP b) := by
  simp [leSucc, inference, FORule.instConclusion, FORule.bindings, applyBindings, leP, succP, mv]

theorem pairBelow_premises :
    pairBelow.row.instPremises [a, b, c, d] = [ltP a b, mulP b b c, addP c a d] := by
  simp [pairBelow, inference, FORule.instPremises, FORule.bindings, applyBindings, ltP, mulP,
    addP, mv]

theorem pairBelow_conclusion : pairBelow.row.instConclusion [a, b, c, d] = pairP a b d := by
  simp [pairBelow, inference, FORule.instConclusion, FORule.bindings, applyBindings, pairP, mv]

theorem pairAbove_premises :
    pairAbove.row.instPremises [a, b, c, d, e] =
      [leP b a, mulP a a c, addP c a d, addP d b e] := by
  simp [pairAbove, inference, FORule.instPremises, FORule.bindings, applyBindings, leP, mulP,
    addP, mv]

theorem pairAbove_conclusion : pairAbove.row.instConclusion [a, b, c, d, e] = pairP a b e := by
  simp [pairAbove, inference, FORule.instConclusion, FORule.bindings, applyBindings, pairP, mv]

theorem evalZero_conclusion : evalZero.row.instConclusion [a] = evalP czeroP a zeroP := by
  simp [evalZero, inference, FORule.instConclusion, FORule.bindings, applyBindings, evalP,
    czeroP, zeroP, mv]

theorem evalSucc_conclusion : evalSucc.row.instConclusion [a] = evalP csuccP a (succP a) := by
  simp [evalSucc, inference, FORule.instConclusion, FORule.bindings, applyBindings, evalP,
    csuccP, succP, mv]

theorem evalLeft_premises : evalLeft.row.instPremises [a, b, c] = [pairP b c a] := by
  simp [evalLeft, inference, FORule.instPremises, FORule.bindings, applyBindings, pairP, mv]

theorem evalLeft_conclusion : evalLeft.row.instConclusion [a, b, c] = evalP cleftP a b := by
  simp [evalLeft, inference, FORule.instConclusion, FORule.bindings, applyBindings, evalP,
    cleftP, mv]

theorem evalRight_premises : evalRight.row.instPremises [a, b, c] = [pairP b c a] := by
  simp [evalRight, inference, FORule.instPremises, FORule.bindings, applyBindings, pairP, mv]

theorem evalRight_conclusion : evalRight.row.instConclusion [a, b, c] = evalP crightP a c := by
  simp [evalRight, inference, FORule.instConclusion, FORule.bindings, applyBindings, evalP,
    crightP, mv]

theorem evalPair_premises :
    evalPair.row.instPremises [a, b, c, d, e, f] = [evalP a c d, evalP b c e, pairP d e f] := by
  simp [evalPair, inference, FORule.instPremises, FORule.bindings, applyBindings, evalP, pairP,
    mv]

theorem evalPair_conclusion :
    evalPair.row.instConclusion [a, b, c, d, e, f] = evalP (cpairP a b) c f := by
  simp [evalPair, inference, FORule.instConclusion, FORule.bindings, applyBindings, evalP,
    cpairP, mv]

theorem evalComp_premises :
    evalComp.row.instPremises [a, b, c, d, e] = [evalP b c d, evalP a d e] := by
  simp [evalComp, inference, FORule.instPremises, FORule.bindings, applyBindings, evalP, mv]

theorem evalComp_conclusion :
    evalComp.row.instConclusion [a, b, c, d, e] = evalP (ccompP a b) c e := by
  simp [evalComp, inference, FORule.instConclusion, FORule.bindings, applyBindings, evalP,
    ccompP, mv]

theorem precZero_premises : precZero.row.instPremises [a, b, c, d] = [evalP a c d] := by
  simp [precZero, inference, FORule.instPremises, FORule.bindings, applyBindings, evalP, mv]

theorem precZero_conclusion :
    precZero.row.instConclusion [a, b, c, d] = precP a b c zeroP d := by
  simp [precZero, inference, FORule.instConclusion, FORule.bindings, applyBindings, precP,
    zeroP, mv]

theorem precSucc_premises :
    precSucc.row.instPremises [a, b, c, d, e, f, g, h] =
      [precP a b c d e, pairP d e f, pairP c f g, evalP b g h] := by
  simp [precSucc, inference, FORule.instPremises, FORule.bindings, applyBindings, precP, pairP,
    evalP, mv]

theorem precSucc_conclusion :
    precSucc.row.instConclusion [a, b, c, d, e, f, g, h] = precP a b c (succP d) h := by
  simp [precSucc, inference, FORule.instConclusion, FORule.bindings, applyBindings, precP,
    succP, mv]

theorem evalPrec_premises :
    evalPrec.row.instPremises [a, b, c, d, e, f] = [pairP c d e, precP a b c d f] := by
  simp [evalPrec, inference, FORule.instPremises, FORule.bindings, applyBindings, pairP, precP,
    mv]

theorem evalPrec_conclusion :
    evalPrec.row.instConclusion [a, b, c, d, e, f] = evalP (cprecP a b) e f := by
  simp [evalPrec, inference, FORule.instConclusion, FORule.bindings, applyBindings, evalP,
    cprecP, mv]

theorem searchZero_conclusion :
    searchZero.row.instConclusion [a, b, c] = searchP a b c zeroP := by
  simp [searchZero, inference, FORule.instConclusion, FORule.bindings, applyBindings, searchP,
    zeroP, mv]

theorem searchSucc_premises :
    searchSucc.row.instPremises [a, b, c, d, e, f, g] =
      [searchP a b c d, addP d c e, pairP b e f, evalP a f (succP g)] := by
  simp [searchSucc, inference, FORule.instPremises, FORule.bindings, applyBindings, searchP,
    addP, pairP, evalP, succP, mv]

theorem searchSucc_conclusion :
    searchSucc.row.instConclusion [a, b, c, d, e, f, g] = searchP a b c (succP d) := by
  simp [searchSucc, inference, FORule.instConclusion, FORule.bindings, applyBindings, searchP,
    succP, mv]

theorem evalSearch_premises :
    evalSearch.row.instPremises [a, b, c, d, e, f, g] =
      [searchP a b c d, addP d c e, pairP b e f, evalP a f zeroP, pairP b c g] := by
  simp [evalSearch, inference, FORule.instPremises, FORule.bindings, applyBindings, searchP,
    addP, pairP, evalP, zeroP, mv]

theorem evalSearch_conclusion :
    evalSearch.row.instConclusion [a, b, c, d, e, f, g] = evalP (crfindP a) g e := by
  simp [evalSearch, inference, FORule.instConclusion, FORule.bindings, applyBindings, evalP,
    crfindP, mv]

theorem halting_premises : halting.row.instPremises [a, b, c] = [evalP a b c] := by
  simp [halting, inference, FORule.instPremises, FORule.bindings, applyBindings, evalP, mv]

theorem halting_conclusion : halting.row.instConclusion [a, b, c] = haltsP a b := by
  simp [halting, inference, FORule.instConclusion, FORule.bindings, applyBindings, haltsP, mv]

end Instances

/-! ## Meaning -/

/-- The number a pattern denotes; every pattern that is not a successor
denotes zero. -/
def natValue : Pattern → ℕ
  | .apply "succ" [n] => natValue n + 1
  | _ => 0
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- The code a pattern denotes; unrecognized patterns denote `Code.zero`. -/
def codeValue : Pattern → Code
  | .apply "csucc" [] => .succ
  | .apply "cleft" [] => .left
  | .apply "cright" [] => .right
  | .apply "cpair" [f, g] => .pair (codeValue f) (codeValue g)
  | .apply "ccomp" [f, g] => .comp (codeValue f) (codeValue g)
  | .apply "cprec" [f, g] => .prec (codeValue f) (codeValue g)
  | .apply "crfind" [f] => .rfind' (codeValue f)
  | _ => .zero
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

@[simp] theorem natValue_zero : natValue zeroP = 0 := by simp [natValue, zeroP]

@[simp] theorem natValue_succ (n : Pattern) : natValue (succP n) = natValue n + 1 := by
  simp [natValue, succP]

@[simp] theorem natValue_num : ∀ n : ℕ, natValue (num n) = n
  | 0 => natValue_zero
  | n + 1 => by rw [num, natValue_succ, natValue_num n]

@[simp] theorem codeValue_czero : codeValue czeroP = .zero := by simp [codeValue, czeroP]
@[simp] theorem codeValue_csucc : codeValue csuccP = .succ := by simp [codeValue, csuccP]
@[simp] theorem codeValue_cleft : codeValue cleftP = .left := by simp [codeValue, cleftP]
@[simp] theorem codeValue_cright : codeValue crightP = .right := by simp [codeValue, crightP]

@[simp] theorem codeValue_cpair (f g : Pattern) :
    codeValue (cpairP f g) = .pair (codeValue f) (codeValue g) := by simp [codeValue, cpairP]

@[simp] theorem codeValue_ccomp (f g : Pattern) :
    codeValue (ccompP f g) = .comp (codeValue f) (codeValue g) := by simp [codeValue, ccompP]

@[simp] theorem codeValue_cprec (f g : Pattern) :
    codeValue (cprecP f g) = .prec (codeValue f) (codeValue g) := by simp [codeValue, cprecP]

@[simp] theorem codeValue_crfind (f : Pattern) :
    codeValue (crfindP f) = .rfind' (codeValue f) := by simp [codeValue, crfindP]

@[simp] theorem codeValue_codePattern : ∀ c : Code, codeValue (codePattern c) = c
  | .zero => codeValue_czero
  | .succ => codeValue_csucc
  | .left => codeValue_cleft
  | .right => codeValue_cright
  | .pair f g => by rw [codePattern, codeValue_cpair, codeValue_codePattern f,
      codeValue_codePattern g]
  | .comp f g => by rw [codePattern, codeValue_ccomp, codeValue_codePattern f,
      codeValue_codePattern g]
  | .prec f g => by rw [codePattern, codeValue_cprec, codeValue_codePattern f,
      codeValue_codePattern g]
  | .rfind' f => by rw [codePattern, codeValue_crfind, codeValue_codePattern f]

/-- The stages of primitive recursion. -/
def precValue (f g : Code) (a : ℕ) : ℕ → Part ℕ
  | 0 => f.eval a
  | k + 1 => precValue f g a k >>= fun i => g.eval (Nat.pair a (Nat.pair k i))

theorem prec_eval (f g : Code) (a k : ℕ) :
    (Code.prec f g).eval (Nat.pair a k) = precValue f g a k := by
  induction k with
  | zero => simp [precValue]
  | succ k ih => rw [Code.eval_prec_succ, ih]; rfl

/-! ## Evaluation, one code constructor at a time -/

theorem mem_eval_zero {n m : ℕ} : m ∈ Code.zero.eval n ↔ m = 0 := by
  show m ∈ (Part.some 0 : Part ℕ) ↔ m = 0
  exact Part.mem_some_iff

theorem mem_eval_succ {n m : ℕ} : m ∈ Code.succ.eval n ↔ m = n + 1 := by
  show m ∈ (Part.some (n + 1) : Part ℕ) ↔ m = n + 1
  exact Part.mem_some_iff

theorem mem_eval_left {n m : ℕ} : m ∈ Code.left.eval n ↔ m = n.unpair.1 := by
  show m ∈ (Part.some n.unpair.1 : Part ℕ) ↔ m = n.unpair.1
  exact Part.mem_some_iff

theorem mem_eval_right {n m : ℕ} : m ∈ Code.right.eval n ↔ m = n.unpair.2 := by
  show m ∈ (Part.some n.unpair.2 : Part ℕ) ↔ m = n.unpair.2
  exact Part.mem_some_iff

theorem mem_eval_pair {f g : Code} {n m : ℕ} :
    m ∈ (Code.pair f g).eval n ↔ ∃ a ∈ f.eval n, ∃ b ∈ g.eval n, Nat.pair a b = m := by
  show m ∈ (Nat.pair <$> f.eval n <*> g.eval n) ↔ _
  simp only [Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨_, ⟨a, left, rfl⟩, b, right, rfl⟩
    exact ⟨a, left, b, right, rfl⟩
  · rintro ⟨a, left, b, right, rfl⟩
    exact ⟨_, ⟨a, left, rfl⟩, b, right, rfl⟩

theorem mem_eval_comp {f g : Code} {n m : ℕ} :
    m ∈ (Code.comp f g).eval n ↔ ∃ k ∈ g.eval n, m ∈ f.eval k := by
  show m ∈ (g.eval n).bind f.eval ↔ _
  exact Part.mem_bind_iff

theorem mem_precValue_succ {f g : Code} {a k m : ℕ} :
    m ∈ precValue f g a (k + 1) ↔
      ∃ i ∈ precValue f g a k, m ∈ g.eval (Nat.pair a (Nat.pair k i)) := by
  rw [precValue, Part.bind_eq_bind, Part.mem_bind_iff]

/-- Unbounded search from `n.unpair.2` with parameter `n.unpair.1`. -/
theorem mem_eval_rfind {f : Code} {n m : ℕ} :
    m ∈ (Code.rfind' f).eval n ↔ ∃ j, j + n.unpair.2 = m ∧
      0 ∈ f.eval (Nat.pair n.unpair.1 (j + n.unpair.2)) ∧
      ∀ i < j, ∃ w, w + 1 ∈ f.eval (Nat.pair n.unpair.1 (i + n.unpair.2)) := by
  simp only [Code.eval, Nat.unpaired, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨j, found, rfl⟩
    obtain ⟨zero, earlier⟩ := Nat.mem_rfind.mp found
    obtain ⟨v, value, isZero⟩ := (Part.mem_map_iff _).mp zero
    refine ⟨j, rfl, ?_, fun i below => ?_⟩
    · rwa [of_decide_eq_true isZero] at value
    · obtain ⟨v, value, positive⟩ := (Part.mem_map_iff _).mp (earlier below)
      cases v with
      | zero => simp at positive
      | succ w => exact ⟨w, value⟩
  · rintro ⟨j, rfl, zero, earlier⟩
    refine ⟨j, Nat.mem_rfind.mpr ⟨(Part.mem_map_iff _).mpr ⟨0, zero, by simp⟩,
      fun {i} below => ?_⟩, rfl⟩
    obtain ⟨w, value⟩ := earlier i below
    exact (Part.mem_map_iff _).mpr ⟨w + 1, value, by simp⟩

/-- The truth of a judgment pattern under the denotation. -/
def Valid : Pattern → Prop
  | .apply "add" [a, b, c] => natValue a + natValue b = natValue c
  | .apply "mul" [a, b, c] => natValue a * natValue b = natValue c
  | .apply "lt" [a, b] => natValue a < natValue b
  | .apply "le" [a, b] => natValue a ≤ natValue b
  | .apply "pair" [a, b, c] => Nat.pair (natValue a) (natValue b) = natValue c
  | .apply "eval" [f, n, m] => natValue m ∈ (codeValue f).eval (natValue n)
  | .apply "prec" [f, g, a, k, m] =>
      natValue m ∈ precValue (codeValue f) (codeValue g) (natValue a) (natValue k)
  | .apply "search" [f, a, s, j] =>
      ∀ i < natValue j,
        ∃ w, w + 1 ∈ (codeValue f).eval (Nat.pair (natValue a) (i + natValue s))
  | .apply "halts" [c, n] => ((codeValue c).eval (natValue n)).Dom
  | _ => False

@[simp] theorem valid_add (a b c : Pattern) :
    Valid (addP a b c) ↔ natValue a + natValue b = natValue c := by simp [Valid, addP]
@[simp] theorem valid_mul (a b c : Pattern) :
    Valid (mulP a b c) ↔ natValue a * natValue b = natValue c := by simp [Valid, mulP]
@[simp] theorem valid_lt (a b : Pattern) : Valid (ltP a b) ↔ natValue a < natValue b := by
  simp [Valid, ltP]
@[simp] theorem valid_le (a b : Pattern) : Valid (leP a b) ↔ natValue a ≤ natValue b := by
  simp [Valid, leP]
@[simp] theorem valid_pair (a b c : Pattern) :
    Valid (pairP a b c) ↔ Nat.pair (natValue a) (natValue b) = natValue c := by
  simp [Valid, pairP]
@[simp] theorem valid_eval (f n m : Pattern) :
    Valid (evalP f n m) ↔ natValue m ∈ (codeValue f).eval (natValue n) := by simp [Valid, evalP]
@[simp] theorem valid_prec (f g a k m : Pattern) :
    Valid (precP f g a k m) ↔
      natValue m ∈ precValue (codeValue f) (codeValue g) (natValue a) (natValue k) := by
  simp [Valid, precP]
@[simp] theorem valid_search (f a s j : Pattern) :
    Valid (searchP f a s j) ↔ ∀ i < natValue j,
      ∃ w, w + 1 ∈ (codeValue f).eval (Nat.pair (natValue a) (i + natValue s)) := by
  simp [Valid, searchP]
@[simp] theorem valid_halts (c n : Pattern) :
    Valid (haltsP c n) ↔ ((codeValue c).eval (natValue n)).Dom := by simp [Valid, haltsP]

/-! ## Soundness -/

theorem list_one {α : Type} : ∀ {items : List α}, items.length = 1 → ∃ a, items = [a]
  | [a], _ => ⟨a, rfl⟩

theorem list_two {α : Type} : ∀ {items : List α}, items.length = 2 → ∃ a b, items = [a, b]
  | [a, b], _ => ⟨a, b, rfl⟩

theorem list_three {α : Type} :
    ∀ {items : List α}, items.length = 3 → ∃ a b c, items = [a, b, c]
  | [a, b, c], _ => ⟨a, b, c, rfl⟩

theorem list_four {α : Type} :
    ∀ {items : List α}, items.length = 4 → ∃ a b c d, items = [a, b, c, d]
  | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem list_five {α : Type} :
    ∀ {items : List α}, items.length = 5 → ∃ a b c d e, items = [a, b, c, d, e]
  | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem list_six {α : Type} :
    ∀ {items : List α}, items.length = 6 → ∃ a b c d e f, items = [a, b, c, d, e, f]
  | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

theorem list_seven {α : Type} :
    ∀ {items : List α}, items.length = 7 → ∃ a b c d e f g, items = [a, b, c, d, e, f, g]
  | [a, b, c, d, e, f, g], _ => ⟨a, b, c, d, e, f, g, rfl⟩

theorem list_eight {α : Type} :
    ∀ {items : List α}, items.length = 8 →
      ∃ a b c d e f g h, items = [a, b, c, d, e, f, g, h]
  | [a, b, c, d, e, f, g, h], _ => ⟨a, b, c, d, e, f, g, h, rfl⟩

/-- **Each rule is sound**: an instance with true premises has a true conclusion. -/
theorem rule_sound {rule : SortedFirstOrderRules.Rule} (member : rule ∈ rules) (arguments : List Pattern)
    (arity : arguments.length = rule.row.vars.length)
    (ih : ∀ premise ∈ rule.row.instPremises arguments, Valid premise) :
    Valid (rule.row.instConclusion arguments) := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, rfl⟩ := list_one arity
    simp [addZero_conclusion]
  · obtain ⟨a, b, c, rfl⟩ := list_three arity
    have sum := ih (addP a b c) (by simp [addSucc_premises])
    simp only [addSucc_conclusion, valid_add, natValue_succ] at sum ⊢
    omega
  · obtain ⟨a, rfl⟩ := list_one arity
    simp [mulZero_conclusion]
  · obtain ⟨a, b, c, d, rfl⟩ := list_four arity
    have product := ih (mulP a b c) (by simp [mulSucc_premises])
    have sum := ih (addP c a d) (by simp [mulSucc_premises])
    simp only [mulSucc_conclusion, valid_mul, valid_add, natValue_succ] at product sum ⊢
    rw [Nat.mul_succ, product, sum]
  · obtain ⟨a, rfl⟩ := list_one arity
    simp [ltZero_conclusion]
  · obtain ⟨a, b, rfl⟩ := list_two arity
    have below := ih (ltP a b) (by simp [ltSucc_premises])
    simp only [ltSucc_conclusion, valid_lt, natValue_succ] at below ⊢
    omega
  · obtain ⟨a, rfl⟩ := list_one arity
    simp [leZero_conclusion]
  · obtain ⟨a, b, rfl⟩ := list_two arity
    have below := ih (leP a b) (by simp [leSucc_premises])
    simp only [leSucc_conclusion, valid_le, natValue_succ] at below ⊢
    omega
  · obtain ⟨a, b, s, c, rfl⟩ := list_four arity
    have below := ih (ltP a b) (by simp [pairBelow_premises])
    have square := ih (mulP b b s) (by simp [pairBelow_premises])
    have sum := ih (addP s a c) (by simp [pairBelow_premises])
    simp only [pairBelow_conclusion, valid_lt, valid_mul, valid_add,
      valid_pair] at below square sum ⊢
    rw [Nat.pair, if_pos below, square, sum]
  · obtain ⟨a, b, s, t, c, rfl⟩ := list_five arity
    have below := ih (leP b a) (by simp [pairAbove_premises])
    have square := ih (mulP a a s) (by simp [pairAbove_premises])
    have lower := ih (addP s a t) (by simp [pairAbove_premises])
    have upper := ih (addP t b c) (by simp [pairAbove_premises])
    simp only [pairAbove_conclusion, valid_le, valid_mul, valid_add,
      valid_pair] at below square lower upper ⊢
    rw [Nat.pair, if_neg (Nat.not_lt.mpr below), square, lower, upper]
  · obtain ⟨n, rfl⟩ := list_one arity
    simp only [evalZero_conclusion, valid_eval, codeValue_czero, natValue_zero]
    exact mem_eval_zero.mpr rfl
  · obtain ⟨n, rfl⟩ := list_one arity
    simp only [evalSucc_conclusion, valid_eval, codeValue_csucc, natValue_succ]
    exact mem_eval_succ.mpr rfl
  · obtain ⟨n, a, b, rfl⟩ := list_three arity
    have paired := ih (pairP a b n) (by simp [evalLeft_premises])
    simp only [evalLeft_conclusion, valid_pair, valid_eval, codeValue_cleft] at paired ⊢
    rw [mem_eval_left, ← paired, Nat.unpair_pair]
  · obtain ⟨n, a, b, rfl⟩ := list_three arity
    have paired := ih (pairP a b n) (by simp [evalRight_premises])
    simp only [evalRight_conclusion, valid_pair, valid_eval, codeValue_cright] at paired ⊢
    rw [mem_eval_right, ← paired, Nat.unpair_pair]
  · obtain ⟨f, g, n, a, b, m, rfl⟩ := list_six arity
    have left := ih (evalP f n a) (by simp [evalPair_premises])
    have right := ih (evalP g n b) (by simp [evalPair_premises])
    have paired := ih (pairP a b m) (by simp [evalPair_premises])
    simp only [evalPair_conclusion, valid_eval, valid_pair,
      codeValue_cpair] at left right paired ⊢
    exact mem_eval_pair.mpr ⟨_, left, _, right, paired⟩
  · obtain ⟨f, g, n, k, m, rfl⟩ := list_five arity
    have inner := ih (evalP g n k) (by simp [evalComp_premises])
    have outer := ih (evalP f k m) (by simp [evalComp_premises])
    simp only [evalComp_conclusion, valid_eval, codeValue_ccomp] at inner outer ⊢
    exact mem_eval_comp.mpr ⟨_, inner, outer⟩
  · obtain ⟨f, g, a, m, rfl⟩ := list_four arity
    have base := ih (evalP f a m) (by simp [precZero_premises])
    simp only [precZero_conclusion, valid_eval, valid_prec, natValue_zero] at base ⊢
    exact base
  · obtain ⟨f, g, a, k, i, p, q, m, rfl⟩ := list_eight arity
    have previous := ih (precP f g a k i) (by simp [precSucc_premises])
    have inner := ih (pairP k i p) (by simp [precSucc_premises])
    have outer := ih (pairP a p q) (by simp [precSucc_premises])
    have step := ih (evalP g q m) (by simp [precSucc_premises])
    simp only [precSucc_conclusion, valid_prec, valid_pair, valid_eval,
      natValue_succ] at previous inner outer step ⊢
    rw [mem_precValue_succ]
    exact ⟨_, previous, by rw [inner, outer]; exact step⟩
  · obtain ⟨f, g, a, k, n, m, rfl⟩ := list_six arity
    have paired := ih (pairP a k n) (by simp [evalPrec_premises])
    have value := ih (precP f g a k m) (by simp [evalPrec_premises])
    simp only [evalPrec_conclusion, valid_pair, valid_prec, valid_eval,
      codeValue_cprec] at paired value ⊢
    rw [← paired, prec_eval]
    exact value
  · obtain ⟨f, a, s, rfl⟩ := list_three arity
    simp [searchZero_conclusion]
  · obtain ⟨f, a, s, j, t, q, w, rfl⟩ := list_seven arity
    have earlier := ih (searchP f a s j) (by simp [searchSucc_premises])
    have sum := ih (addP j s t) (by simp [searchSucc_premises])
    have paired := ih (pairP a t q) (by simp [searchSucc_premises])
    have step := ih (evalP f q (succP w)) (by simp [searchSucc_premises])
    simp only [searchSucc_conclusion, valid_search, valid_add, valid_pair, valid_eval,
      natValue_succ] at earlier sum paired step ⊢
    intro i below
    rcases Nat.lt_succ_iff_lt_or_eq.mp below with below | rfl
    · exact earlier i below
    · exact ⟨natValue w, by rw [sum, paired]; exact step⟩
  · obtain ⟨f, a, s, j, t, q, n, rfl⟩ := list_seven arity
    have earlier := ih (searchP f a s j) (by simp [evalSearch_premises])
    have sum := ih (addP j s t) (by simp [evalSearch_premises])
    have paired := ih (pairP a t q) (by simp [evalSearch_premises])
    have found := ih (evalP f q zeroP) (by simp [evalSearch_premises])
    have input := ih (pairP a s n) (by simp [evalSearch_premises])
    simp only [evalSearch_conclusion, valid_search, valid_add, valid_pair, valid_eval,
      natValue_zero, codeValue_crfind] at earlier sum paired found input ⊢
    rw [← input, mem_eval_rfind]
    simp only [Nat.unpair_pair]
    exact ⟨natValue j, sum, by rw [sum, paired]; exact found, earlier⟩
  · obtain ⟨c, n, m, rfl⟩ := list_three arity
    have value := ih (evalP c n m) (by simp [halting_premises])
    simp only [halting_conclusion, valid_eval, valid_halts] at value ⊢
    exact Part.dom_iff_mem.mpr ⟨_, value⟩

/-- **Soundness.** Every derivable pattern is true under the denotation. -/
theorem valid_of_derives {pattern : Pattern}
    (derived : Derives language rules [] [] pattern) : Valid pattern := by
  induction derived with
  | hypothesis member => simp at member
  | rule member arguments arity _ _ _ ih => exact rule_sound member arguments arity ih

/-! ## Typing of numerals and codes -/

theorem former_member {label category : String} {sorts : List TypeExpr}
    (member : former label category sorts ∈ language.terms) :
    former label category sorts ∈ language.terms := member

theorem hasType_num : ∀ n : ℕ, HasType language FreeTypeContext.empty [] (num n) natSort
  | 0 => HasType.constructor (rule := former "zero" "nat" []) (by simp [language])
      (former_notBare _ _ _ (by simp)) .nil
  | n + 1 => HasType.constructor (rule := former "succ" "nat" [natSort]) (by simp [language])
      (former_notBare _ _ _ (by simp)) (.cons trivial rfl (hasType_num n) .nil)

theorem hasType_code :
    ∀ c : Code, HasType language FreeTypeContext.empty [] (codePattern c) codeSort
  | .zero => HasType.constructor (rule := former "czero" "code" []) (by simp [language])
      (former_notBare _ _ _ (by simp)) .nil
  | .succ => HasType.constructor (rule := former "csucc" "code" []) (by simp [language])
      (former_notBare _ _ _ (by simp)) .nil
  | .left => HasType.constructor (rule := former "cleft" "code" []) (by simp [language])
      (former_notBare _ _ _ (by simp)) .nil
  | .right => HasType.constructor (rule := former "cright" "code" []) (by simp [language])
      (former_notBare _ _ _ (by simp)) .nil
  | .pair f g => HasType.constructor (rule := former "cpair" "code" [codeSort, codeSort])
      (by simp [language]) (former_notBare _ _ _ (by simp))
      (.cons trivial rfl (hasType_code f) (.cons trivial rfl (hasType_code g) .nil))
  | .comp f g => HasType.constructor (rule := former "ccomp" "code" [codeSort, codeSort])
      (by simp [language]) (former_notBare _ _ _ (by simp))
      (.cons trivial rfl (hasType_code f) (.cons trivial rfl (hasType_code g) .nil))
  | .prec f g => HasType.constructor (rule := former "cprec" "code" [codeSort, codeSort])
      (by simp [language]) (former_notBare _ _ _ (by simp))
      (.cons trivial rfl (hasType_code f) (.cons trivial rfl (hasType_code g) .nil))
  | .rfind' f => HasType.constructor (rule := former "crfind" "code" [codeSort])
      (by simp [language]) (former_notBare _ _ _ (by simp))
      (.cons trivial rfl (hasType_code f) .nil)

theorem matchCorrect_num : ∀ n : ℕ, isMatchCorrectAux (num n) = true
  | 0 => by simp [num, zeroP, isMatchCorrectAux, isMatchCorrectListAux]
  | n + 1 => by
      simp [num, succP, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_num n]

theorem matchCorrect_code : ∀ c : Code, isMatchCorrectAux (codePattern c) = true
  | .zero => by simp [codePattern, czeroP, isMatchCorrectAux, isMatchCorrectListAux]
  | .succ => by simp [codePattern, csuccP, isMatchCorrectAux, isMatchCorrectListAux]
  | .left => by simp [codePattern, cleftP, isMatchCorrectAux, isMatchCorrectListAux]
  | .right => by simp [codePattern, crightP, isMatchCorrectAux, isMatchCorrectListAux]
  | .pair f g => by
      simp [codePattern, cpairP, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_code f,
        matchCorrect_code g]
  | .comp f g => by
      simp [codePattern, ccompP, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_code f,
        matchCorrect_code g]
  | .prec f g => by
      simp [codePattern, cprecP, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_code f,
        matchCorrect_code g]
  | .rfind' f => by
      simp [codePattern, crfindP, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_code f]

/-! ## Completeness -/

/-- A closed value of a term sort. -/
inductive Value where
  | nat (n : ℕ)
  | code (c : Code)

def Value.pattern : Value → Pattern
  | .nat n => num n
  | .code c => codePattern c

def Value.sort : Value → TypeExpr
  | .nat _ => natSort
  | .code _ => codeSort

theorem values_typed : ∀ values : List Value,
    List.Forall₂ (fun argument type => HasType language FreeTypeContext.empty [] argument type)
      (values.map Value.pattern) (values.map Value.sort)
  | [] => .nil
  | .nat n :: values => .cons (hasType_num n) (values_typed values)
  | .code c :: values => .cons (hasType_code c) (values_typed values)

theorem value_matchCorrect : ∀ value : Value, isMatchCorrectAux value.pattern = true
  | .nat n => matchCorrect_num n
  | .code c => matchCorrect_code c

/-- One rule instance at closed values. -/
theorem derives_instance {rule : SortedFirstOrderRules.Rule} (member : rule ∈ rules)
    (values : List Value) (sorts : values.map Value.sort = rule.variableTypes)
    (arity : values.length = rule.row.vars.length)
    (premises : ∀ premise ∈ rule.row.instPremises (values.map Value.pattern),
      Derives language rules [] [] premise) :
    Derives language rules [] [] (rule.row.instConclusion (values.map Value.pattern)) :=
  Derives.rule member (values.map Value.pattern) (by simpa using arity)
    (sorts ▸ values_typed values)
    (fun argument inArguments => by
      obtain ⟨value, -, rfl⟩ := List.mem_map.mp inArguments
      exact value_matchCorrect value)
    premises

/-- A predicate on patterns closed under the instances of every rule at closed values. -/
abbrev ClosedUnderValues (P : Pattern → Prop) : Prop :=
  ∀ {rule : SortedFirstOrderRules.Rule}, rule ∈ rules → ∀ (values : List Value),
    values.map Value.sort = rule.variableTypes → values.length = rule.row.vars.length →
    (∀ premise ∈ rule.row.instPremises (values.map Value.pattern), P premise) →
    P (rule.row.instConclusion (values.map Value.pattern))

/-- Derivability is closed under the instances of every rule at closed values. -/
theorem derives_closed : ClosedUnderValues (Derives language rules [] []) :=
  fun member values sorts arity premises => derives_instance member values sorts arity premises

/-! Every predicate closed under the rule instances at closed values holds of the true judgments. -/

section Completeness

variable {P : Pattern → Prop} (closed : ClosedUnderValues P)
include closed

theorem closed_add (a : ℕ) : ∀ b : ℕ,
    P (addP (num a) (num b) (num (a + b)))
  | 0 => by
      have step := closed (rule := addZero) (by simp [rules]) [.nat a] rfl rfl
        (by simp [addZero, inference, FORule.instPremises])
      simpa [addZero_conclusion, Value.pattern, num] using step
  | b + 1 => by
      have step := closed (rule := addSucc) (by simp [rules])
        [.nat a, .nat b, .nat (a + b)] rfl rfl
        (by simpa [addSucc_premises, Value.pattern] using closed_add a b)
      simpa [addSucc_conclusion, Value.pattern, num, Nat.add_succ] using step

theorem closed_mul (a : ℕ) : ∀ b : ℕ,
    P (mulP (num a) (num b) (num (a * b)))
  | 0 => by
      have step := closed (rule := mulZero) (by simp [rules]) [.nat a] rfl rfl
        (by simp [mulZero, inference, FORule.instPremises])
      simpa [mulZero_conclusion, Value.pattern, num] using step
  | b + 1 => by
      have step := closed (rule := mulSucc) (by simp [rules])
        [.nat a, .nat b, .nat (a * b), .nat (a * b + a)] rfl rfl
        (by
          simp only [List.map_cons, List.map_nil, Value.pattern, mulSucc_premises,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨closed_mul a b, closed_add closed (a * b) a⟩)
      simpa [mulSucc_conclusion, Value.pattern, num, Nat.mul_succ] using step

theorem closed_lt : ∀ {a b : ℕ}, a < b → P (ltP (num a) (num b))
  | 0, b + 1, _ => by
      have step := closed (rule := ltZero) (by simp [rules]) [.nat b] rfl rfl
        (by simp [ltZero, inference, FORule.instPremises])
      simpa [ltZero_conclusion, Value.pattern, num] using step
  | a + 1, b + 1, below => by
      have step := closed (rule := ltSucc) (by simp [rules]) [.nat a, .nat b] rfl rfl
        (by simpa [ltSucc_premises, Value.pattern] using closed_lt (Nat.lt_of_succ_lt_succ below))
      simpa [ltSucc_conclusion, Value.pattern, num] using step
  | _, 0, below => absurd below (Nat.not_lt_zero _)

theorem closed_le : ∀ {a b : ℕ}, a ≤ b → P (leP (num a) (num b))
  | 0, b, _ => by
      have step := closed (rule := leZero) (by simp [rules]) [.nat b] rfl rfl
        (by simp [leZero, inference, FORule.instPremises])
      simpa [leZero_conclusion, Value.pattern, num] using step
  | a + 1, b + 1, below => by
      have step := closed (rule := leSucc) (by simp [rules]) [.nat a, .nat b] rfl rfl
        (by simpa [leSucc_premises, Value.pattern] using closed_le (Nat.le_of_succ_le_succ below))
      simpa [leSucc_conclusion, Value.pattern, num] using step
  | _ + 1, 0, below => absurd below (Nat.not_succ_le_zero _)

theorem closed_pair (a b : ℕ) :
    P (pairP (num a) (num b) (num (Nat.pair a b))) := by
  by_cases below : a < b
  · have step := closed (rule := pairBelow) (by simp [rules])
      [.nat a, .nat b, .nat (b * b), .nat (b * b + a)] rfl rfl
      (by
        simp only [List.map_cons, List.map_nil, Value.pattern, pairBelow_premises,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨closed_lt closed below, closed_mul closed b b, closed_add closed (b * b) a⟩)
    simpa [pairBelow_conclusion, Value.pattern, Nat.pair, below] using step
  · have step := closed (rule := pairAbove) (by simp [rules])
      [.nat a, .nat b, .nat (a * a), .nat (a * a + a), .nat (a * a + a + b)] rfl rfl
      (by
        simp only [List.map_cons, List.map_nil, Value.pattern, pairAbove_premises,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨closed_le closed (Nat.not_lt.mp below), closed_mul closed a a, closed_add closed (a * a) a,
          closed_add closed (a * a + a) b⟩)
    simpa [pairAbove_conclusion, Value.pattern, Nat.pair, below] using step

theorem closed_prec_of {f g : Code}
    (evalF : ∀ {n m : ℕ}, m ∈ f.eval n →
      P (evalP (codePattern f) (num n) (num m)))
    (evalG : ∀ {n m : ℕ}, m ∈ g.eval n →
      P (evalP (codePattern g) (num n) (num m)))
    (a : ℕ) : ∀ (k : ℕ) {m : ℕ}, m ∈ precValue f g a k →
      P (precP (codePattern f) (codePattern g) (num a) (num k) (num m))
  | 0, m, value => by
      have step := closed (rule := precZero) (by simp [rules])
        [.code f, .code g, .nat a, .nat m] rfl rfl
        (by simpa [precZero_premises, Value.pattern] using evalF (n := a) value)
      simpa [precZero_conclusion, Value.pattern, num] using step
  | k + 1, m, value => by
      obtain ⟨i, previous, step⟩ := Part.mem_bind_iff.mp value
      have derivation := closed (rule := precSucc) (by simp [rules])
        [.code f, .code g, .nat a, .nat k, .nat i, .nat (Nat.pair k i),
          .nat (Nat.pair a (Nat.pair k i)), .nat m] rfl rfl
        (by
          simp only [List.map_cons, List.map_nil, Value.pattern, precSucc_premises,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨closed_prec_of evalF evalG a k previous, closed_pair closed k i,
            closed_pair closed a (Nat.pair k i), evalG step⟩)
      simpa [precSucc_conclusion, Value.pattern, num] using derivation

theorem closed_search_of {f : Code}
    (evalF : ∀ {n m : ℕ}, m ∈ f.eval n →
      P (evalP (codePattern f) (num n) (num m)))
    (a s : ℕ) : ∀ j : ℕ, (∀ i < j, ∃ w, w + 1 ∈ f.eval (Nat.pair a (i + s))) →
      P (searchP (codePattern f) (num a) (num s) (num j))
  | 0, _ => by
      have step := closed (rule := searchZero) (by simp [rules])
        [.code f, .nat a, .nat s] rfl rfl
        (by simp [searchZero, inference, FORule.instPremises])
      simpa [searchZero_conclusion, Value.pattern, num] using step
  | j + 1, earlier => by
      obtain ⟨w, value⟩ := earlier j (Nat.lt_succ_self j)
      have step := closed (rule := searchSucc) (by simp [rules])
        [.code f, .nat a, .nat s, .nat j, .nat (j + s), .nat (Nat.pair a (j + s)), .nat w] rfl rfl
        (by
          simp only [List.map_cons, List.map_nil, Value.pattern, searchSucc_premises,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨closed_search_of evalF a s j
              (fun i below => earlier i (Nat.lt_succ_of_lt below)),
            closed_add closed j s, closed_pair closed a (j + s), evalF value⟩)
      simpa [searchSucc_conclusion, Value.pattern, num] using step

/-- **Completeness for evaluation.** -/
theorem closed_eval : ∀ (c : Code) {n m : ℕ}, m ∈ c.eval n →
    P (evalP (codePattern c) (num n) (num m))
  | .zero, n, m, value => by
      have zero : m = 0 := mem_eval_zero.mp value
      subst zero
      have step := closed (rule := evalZero) (by simp [rules]) [.nat n] rfl rfl
        (by simp [evalZero, inference, FORule.instPremises])
      simpa [evalZero_conclusion, Value.pattern, codePattern, num] using step
  | .succ, n, m, value => by
      have succ : m = n + 1 := mem_eval_succ.mp value
      subst succ
      have step := closed (rule := evalSucc) (by simp [rules]) [.nat n] rfl rfl
        (by simp [evalSucc, inference, FORule.instPremises])
      simpa [evalSucc_conclusion, Value.pattern, codePattern, num] using step
  | .left, n, m, value => by
      have left : m = n.unpair.1 := mem_eval_left.mp value
      subst left
      have step := closed (rule := evalLeft) (by simp [rules])
        [.nat n, .nat n.unpair.1, .nat n.unpair.2] rfl rfl
        (by simpa [evalLeft_premises, Value.pattern, Nat.pair_unpair] using
          closed_pair closed n.unpair.1 n.unpair.2)
      simpa [evalLeft_conclusion, Value.pattern, codePattern] using step
  | .right, n, m, value => by
      have right : m = n.unpair.2 := mem_eval_right.mp value
      subst right
      have step := closed (rule := evalRight) (by simp [rules])
        [.nat n, .nat n.unpair.1, .nat n.unpair.2] rfl rfl
        (by simpa [evalRight_premises, Value.pattern, Nat.pair_unpair] using
          closed_pair closed n.unpair.1 n.unpair.2)
      simpa [evalRight_conclusion, Value.pattern, codePattern] using step
  | .pair f g, n, m, value => by
      obtain ⟨a, left, b, right, rfl⟩ := mem_eval_pair.mp value
      have step := closed (rule := evalPair) (by simp [rules])
        [.code f, .code g, .nat n, .nat a, .nat b, .nat (Nat.pair a b)] rfl rfl
        (by
          simp only [List.map_cons, List.map_nil, Value.pattern, evalPair_premises,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨closed_eval f left, closed_eval g right, closed_pair closed a b⟩)
      simpa [evalPair_conclusion, Value.pattern, codePattern] using step
  | .comp f g, n, m, value => by
      obtain ⟨k, inner, outer⟩ := mem_eval_comp.mp value
      have step := closed (rule := evalComp) (by simp [rules])
        [.code f, .code g, .nat n, .nat k, .nat m] rfl rfl
        (by
          simp only [List.map_cons, List.map_nil, Value.pattern, evalComp_premises,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨closed_eval g inner, closed_eval f outer⟩)
      simpa [evalComp_conclusion, Value.pattern, codePattern] using step
  | .prec f g, n, m, value => by
      rw [← Nat.pair_unpair n, prec_eval] at value
      have recursion := closed_prec_of closed (fun found => closed_eval f found)
        (fun found => closed_eval g found) n.unpair.1 n.unpair.2 value
      have step := closed (rule := evalPrec) (by simp [rules])
        [.code f, .code g, .nat n.unpair.1, .nat n.unpair.2, .nat n, .nat m] rfl rfl
        (by
          simp only [List.map_cons, List.map_nil, Value.pattern, evalPrec_premises,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          refine ⟨?_, recursion⟩
          simpa [Nat.pair_unpair] using closed_pair closed n.unpair.1 n.unpair.2)
      simpa [evalPrec_conclusion, Value.pattern, codePattern] using step
  | .rfind' f, n, m, value => by
      obtain ⟨j, rfl, zero, earlier⟩ := mem_eval_rfind.mp value
      have search := closed_search_of closed (fun found => closed_eval f found) n.unpair.1 n.unpair.2
        j earlier
      have step := closed (rule := evalSearch) (by simp [rules])
        [.code f, .nat n.unpair.1, .nat n.unpair.2, .nat j, .nat (j + n.unpair.2),
          .nat (Nat.pair n.unpair.1 (j + n.unpair.2)), .nat n] rfl rfl
        (by
          simp only [List.map_cons, List.map_nil, Value.pattern, evalSearch_premises,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          refine ⟨search, closed_add closed j n.unpair.2, closed_pair closed n.unpair.1 (j + n.unpair.2),
            ?_, ?_⟩
          · simpa [num] using closed_eval f zero
          · simpa [Nat.pair_unpair] using closed_pair closed n.unpair.1 n.unpair.2)
      simpa [evalSearch_conclusion, Value.pattern, codePattern] using step

theorem closed_halts {c : Code} {n : ℕ} (defined : (c.eval n).Dom) :
    P (haltsP (codePattern c) (num n)) := by
  obtain ⟨m, value⟩ := Part.dom_iff_mem.mp defined
  have step := closed (rule := halting) (by simp [rules])
    [.code c, .nat n, .nat m] rfl rfl
    (by simpa [halting_premises, Value.pattern] using closed_eval closed c value)
  simpa [halting_conclusion, Value.pattern] using step

end Completeness

/-! ## Judgments -/

/-- A closed judgment of the presentation. -/
inductive Judgment where
  | add (a b c : ℕ)
  | mul (a b c : ℕ)
  | lt (a b : ℕ)
  | le (a b : ℕ)
  | pair (a b c : ℕ)
  | eval (c : Code) (n m : ℕ)
  | prec (f g : Code) (a k m : ℕ)
  | search (f : Code) (a s j : ℕ)
  | halts (c : Code) (n : ℕ)

def Judgment.pattern : Judgment → Pattern
  | .add a b c => addP (num a) (num b) (num c)
  | .mul a b c => mulP (num a) (num b) (num c)
  | .lt a b => ltP (num a) (num b)
  | .le a b => leP (num a) (num b)
  | .pair a b c => pairP (num a) (num b) (num c)
  | .eval c n m => evalP (codePattern c) (num n) (num m)
  | .prec f g a k m => precP (codePattern f) (codePattern g) (num a) (num k) (num m)
  | .search f a s j => searchP (codePattern f) (num a) (num s) (num j)
  | .halts c n => haltsP (codePattern c) (num n)

/-- What a judgment states. -/
def Judgment.Holds : Judgment → Prop
  | .add a b c => a + b = c
  | .mul a b c => a * b = c
  | .lt a b => a < b
  | .le a b => a ≤ b
  | .pair a b c => Nat.pair a b = c
  | .eval c n m => m ∈ c.eval n
  | .prec f g a k m => m ∈ precValue f g a k
  | .search f a s j => ∀ i < j, ∃ w, w + 1 ∈ f.eval (Nat.pair a (i + s))
  | .halts c n => (c.eval n).Dom

theorem valid_iff_holds (judgment : Judgment) : Valid judgment.pattern ↔ judgment.Holds := by
  cases judgment <;> simp [Judgment.pattern, Judgment.Holds]

/-- **Every predicate closed under the rule instances at closed values holds of every true judgment.** -/
theorem holds_closed {P : Pattern → Prop} (closed : ClosedUnderValues P) (judgment : Judgment)
    (holds : judgment.Holds) : P judgment.pattern := by
  cases judgment with
  | add a b c => subst holds; exact closed_add closed a b
  | mul a b c => subst holds; exact closed_mul closed a b
  | lt a b => exact closed_lt closed holds
  | le a b => exact closed_le closed holds
  | pair a b c => subst holds; exact closed_pair closed a b
  | eval c n m => exact closed_eval closed c holds
  | prec f g a k m =>
      exact closed_prec_of closed (fun found => closed_eval closed f found)
        (fun found => closed_eval closed g found) a k holds
  | search f a s j => exact closed_search_of closed (fun found => closed_eval closed f found) a s j holds
  | halts c n => exact closed_halts closed holds

/-- **A closed judgment is derivable exactly when it is true.** -/
theorem derives_iff (judgment : Judgment) :
    Derives language rules [] [] judgment.pattern ↔ judgment.Holds := by
  refine ⟨fun derived => (valid_iff_holds judgment).mp (valid_of_derives derived), ?_⟩
  intro holds
  exact holds_closed derives_closed judgment holds

/-- The presentation derives that `c` sends `n` to `m` exactly when it does. -/
theorem derives_eval_iff (c : Code) (n m : ℕ) :
    Derives language rules [] [] (evalP (codePattern c) (num n) (num m)) ↔ m ∈ c.eval n :=
  derives_iff (.eval c n m)

/-- The presentation derives that `c` halts on `n` exactly when it does. -/
theorem derives_halts_iff (c : Code) (n : ℕ) :
    Derives language rules [] [] (haltsP (codePattern c) (num n)) ↔ (c.eval n).Dom :=
  derives_iff (.halts c n)

/-! ## Where derivability lies -/

/-- **Every recursively enumerable predicate on numbers is represented**: it
holds of `n` exactly when the presentation derives that one fixed code
halts on `n`. -/
theorem every_re_represented {p : ℕ → Prop} (enumerable : REPred p) :
    ∃ c : Code, ∀ n, p n ↔ Derives language rules [] [] (haltsP (codePattern c) (num n)) := by
  have partial_ :
      Partrec fun n => (Part.assert (p n) fun _ => Part.some ()).map fun _ => (0 : ℕ) :=
    enumerable.map (Computable.const 0).to₂
  obtain ⟨c, same⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp partial_)
  refine ⟨c, fun n => ?_⟩
  rw [derives_halts_iff, same]
  exact ⟨fun holds => ⟨holds, trivial⟩, fun defined => defined.1⟩

/-- The halting judgments of one code are recursively enumerable. -/
theorem halts_re (c : Code) :
    REPred fun n => Derives language rules [] [] (haltsP (codePattern c) (num n)) :=
  (Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.id).dom_re.of_eq
    fun n => (derives_halts_iff c n).symm

/-- **Derivability is undecidable**: no computable procedure decides, for
every code, whether its halting judgment at one input is derivable. -/
theorem halts_undecidable (n : ℕ) :
    ¬ ComputablePred fun c : Code =>
      Derives language rules [] [] (haltsP (codePattern c) (num n)) :=
  fun decidable => ComputablePred.halting_problem n
    (decidable.of_eq fun c => derives_halts_iff c n)

/-- The judgments that are not derivable are not recursively enumerable. -/
theorem not_derivable_not_re (n : ℕ) :
    ¬ REPred fun c : Code =>
      ¬ Derives language rules [] [] (haltsP (codePattern c) (num n)) :=
  fun enumerable => ComputablePred.halting_problem_not_re n
    (enumerable.of_eq fun c => not_congr (derives_halts_iff c n))

/-! ## Controls -/

/-- Two successors send three to five. -/
example : Derives language rules [] []
    (evalP (codePattern (.comp .succ .succ)) (num 3) (num 5)) := by
  rw [derives_eval_iff, mem_eval_comp]
  exact ⟨4, mem_eval_succ.mpr rfl, mem_eval_succ.mpr rfl⟩

/-- The successor does not send three to three. -/
example : ¬ Derives language rules [] [] (evalP (codePattern .succ) (num 3) (num 3)) := by
  rw [derives_eval_iff, mem_eval_succ]
  omega

/-- Searching for a zero of the successor never ends, so its halting
judgment is not derivable. -/
example : ¬ Derives language rules [] [] (haltsP (codePattern (.rfind' .succ)) (num 0)) := by
  rw [derives_halts_iff, Part.dom_iff_mem]
  rintro ⟨m, value⟩
  obtain ⟨j, -, zero, -⟩ := mem_eval_rfind.mp value
  rw [mem_eval_succ] at zero
  omega

end Mettapedia.GSLT.LanguageDef.PartialRecursive
