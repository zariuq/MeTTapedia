import Mettapedia.Logic.TierZero.Adequacy.HOLPres

/-!
# HOL Light's kernel on small proofs: worlds and controls

`holWorld` admits `holRules`, the definition `T_DEF` (`T = ((\p. p) = (\p. p))`) and the type
definition of HOL Light's one-element type `1` (from `⊢ (\b. b) T`), then submits one claim per
primitive inference, HOL Light's `TRUTH` (`⊢ T`, by `SYM T_DEF` and `EQ_MP`), and one refused
control per side condition:

* accepted: `refl` (`⊢ x = x`), `assume` (`{p} ⊢ p`), `deduct` (`⊢ p = p` by
  DEDUCT_ANTISYM_RULE from two ASSUMEs), `trans` (`{p = q, q = r} ⊢ p = r`), `mk-comb`
  (`{f = g} ⊢ f x = g x`), `abs` (`⊢ (\x. x) = (\x. x)`), `beta` (`⊢ (\x. x) y = y`), `inst`
  (`{q} ⊢ q` from `{p} ⊢ p`), `inst-type` (`⊢ x:bool = x` from `⊢ x:A = x`), `eq-mp`
  (`{p = q, p} ⊢ q`), `truth` (`⊢ T`);
* refused: `symbol-name` (a variable named by a symbol, not a string), `trans-bad-union` (a
  hypothesis set that is not the union), `abs-free-in-hyp` (ABS over a variable free in a
  hypothesis), `inst-bad-image` (a hypothesis set that is not the image), `inst-type-key` (a type
  pair whose key is not a type variable).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOL.Controls

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Logic.TierZero.Kernel2.Examples (claim world accepted)
open Mettapedia.Logic.TierZero.Adequacy.HOL

/-- A variable named by a string. -/
def V (n : String) (ty : Pat) : Pat := varP (pstr n) ty

/-- `bool → bool`. -/
def bb : Pat := funP boolP boolP
/-- The type variable `A`. -/
def tA : Pat := tyvarP (pstr "A")

def X : Pat := V "x" boolP
def Y : Pat := V "y" boolP
def P : Pat := V "p" boolP
def Q : Pat := V "q" boolP
def R : Pat := V "r" boolP
def F : Pat := V "f" bb
def G : Pat := V "g" bb

/-- `p = q`, `q = r`, `x = y`, `f = g`. -/
def ePQ : Pat := eqP boolP P Q
def eQR : Pat := eqP boolP Q R
def eXY : Pat := eqP boolP X Y
def eFG : Pat := eqP bb F G

/-- `\x:bool. x`. -/
def idB : Pat := pbnd boolP (.idx 0)

/-- `T` and its definition's right side `(\p. p) = (\p. p)`. -/
def tC : Pat := constP "T" boolP
def rhsT : Pat := eqP bb idB idB

/-- `T_DEF`. -/
def tDefRules : List (String × Rule) := newBasicDefinitionRules "T" .bool rhsT

/-- HOL Light's type `1`, from `⊢ (\b. b) T`. -/
def oneRules : List (String × Rule) :=
  newBasicTypeDefinitionRules "1" "one_ABS" "one_REP" [] .bool idB tC

/-- The rules of the world. -/
def worldRules : List (String × Rule) := holRules ++ tDefRules ++ oneRules

def cRefl : Claim String :=
  claim "refl" 0 [] (thmJ emptyP (eqP boolP X X)) [(1, pstr "x")]
    [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]), (3, "hol:REFL", [.node 2])] (.node 3)

def cSymbolName : Claim String :=
  claim "symbol-name" 0 [] (thmJ emptyP (eqP boolP (varP (psym "x") boolP) (varP (psym "x") boolP)))
    [(1, psym "x")]
    [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]), (3, "hol:REFL", [.node 2])] (.node 3)

def cAssume : Claim String :=
  claim "assume" 0 [] (thmJ (setP [P]) P) [(1, pstr "p"), (2, setP [P])]
    [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]),
     (3, "hol:ASSUME", [.node 2, .term 2])] (.node 3)

def cDeduct : Claim String :=
  claim "deduct" 0 [] (thmJ emptyP (eqP boolP P P)) [(1, pstr "p"), (2, setP [P]), (3, emptyP)]
    [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]),
     (3, "hol:ASSUME", [.node 2, .term 2]),
     (4, "hol:DEDUCT_ANTISYM_RULE", [.node 3, .node 3, .term 3, .term 3, .term 3])] (.node 4)

/-- The typing of `p = q` and `q = r`, then TRANS; `u` is the cited hypothesis set of the
conclusion. -/
def transProof (u : ℕ) : List (ℕ × String × List CKid) :=
  [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]), (3, "hol:tm.var", [.term 2, .node 1]),
   (4, "hol:tm.var", [.term 3, .node 1]), (5, "hol:const.=", [.node 1]),
   (6, "hol:tm.comb", [.node 5, .node 2]), (7, "hol:tm.comb", [.node 6, .node 3]),
   (8, "hol:tm.comb", [.node 5, .node 3]), (9, "hol:tm.comb", [.node 8, .node 4]),
   (10, "hol:ASSUME", [.node 7, .term 4]), (11, "hol:ASSUME", [.node 9, .term 5]),
   (12, "hol:TRANS", [.node 10, .node 11, .term u])]

def transTerms : List (ℕ × Pat) :=
  [(1, pstr "p"), (2, pstr "q"), (3, pstr "r"), (4, setP [ePQ]), (5, setP [eQR]),
   (6, setP [ePQ, eQR])]

def cTrans : Claim String :=
  claim "trans" 0 [] (thmJ (setP [ePQ, eQR]) (eqP boolP P R)) transTerms (transProof 6) (.node 12)

def cTransBadUnion : Claim String :=
  claim "trans-bad-union" 0 [] (thmJ (setP [ePQ]) (eqP boolP P R)) transTerms (transProof 4) (.node 12)

def cMkComb : Claim String :=
  claim "mk-comb" 0 [] (thmJ (setP [eFG]) (eqP boolP (combP F X) (combP G X)))
    [(1, pstr "f"), (2, pstr "g"), (3, pstr "x"), (4, setP [eFG])]
    [(1, "hol:ty.bool", []), (2, "hol:ty.fun", [.node 1, .node 1]),
     (3, "hol:tm.var", [.term 1, .node 2]), (4, "hol:tm.var", [.term 2, .node 2]),
     (5, "hol:tm.var", [.term 3, .node 1]), (6, "hol:const.=", [.node 2]),
     (7, "hol:tm.comb", [.node 6, .node 3]), (8, "hol:tm.comb", [.node 7, .node 4]),
     (9, "hol:ASSUME", [.node 8, .term 4]), (10, "hol:REFL", [.node 5]),
     (11, "hol:MK_COMB", [.node 9, .node 10, .term 4])] (.node 11)

def cAbs : Claim String :=
  claim "abs" 0 [] (thmJ emptyP (eqP bb idB idB)) [(1, pstr "x")]
    [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]), (3, "hol:REFL", [.node 2]),
     (4, "hol:ABS", [.node 3, .node 2])] (.node 4)

def cAbsFreeInHyp : Claim String :=
  claim "abs-free-in-hyp" 0 [] (thmJ (setP [eXY]) (eqP bb idB (pbnd boolP Y)))
    [(1, pstr "x"), (2, pstr "y"), (3, setP [eXY])]
    [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]), (3, "hol:tm.var", [.term 2, .node 1]),
     (4, "hol:const.=", [.node 1]), (5, "hol:tm.comb", [.node 4, .node 2]),
     (6, "hol:tm.comb", [.node 5, .node 3]), (7, "hol:ASSUME", [.node 6, .term 3]),
     (8, "hol:ABS", [.node 7, .node 2])] (.node 8)

def cBeta : Claim String :=
  claim "beta" 0 [] (thmJ emptyP (eqP boolP (combP idB Y) Y)) [(1, pstr "x"), (2, pstr "y")]
    [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]), (3, "hol:tm.var", [.term 2, .node 1]),
     (4, "hol:tm.abs", [.node 2, .node 2]), (5, "hol:tm.comb", [.node 4, .node 3]),
     (6, "hol:BETA", [.node 5])] (.node 6)

/-- ASSUME `p`, then INST `[q/p]`; `g₂` is the cited hypothesis set of the conclusion. -/
def instProof (g₂ : ℕ) : List (ℕ × String × List CKid) :=
  [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]), (3, "hol:tm.var", [.term 2, .node 1]),
   (4, "hol:ASSUME", [.node 2, .term 3]), (5, "hol:inst-pair", [.node 2, .node 3]),
   (6, "hol:INST", [.node 4, .term 4, .node 5, .term g₂])]

def instTerms : List (ℕ × Pat) :=
  [(1, pstr "p"), (2, pstr "q"), (3, setP [P]), (4, pex [pex [P, Q]]), (5, setP [Q])]

def cInst : Claim String :=
  claim "inst" 0 [] (thmJ (setP [Q]) Q) instTerms (instProof 5) (.node 6)

def cInstBadImage : Claim String :=
  claim "inst-bad-image" 0 [] (thmJ (setP [P]) Q) instTerms (instProof 3) (.node 6)

/-- REFL at `x : A`, then INST_TYPE `[bool/A]`; `first`, `second` are the children of the type
pair. -/
def instTypeProof (first second : ℕ) : List (ℕ × String × List CKid) :=
  [(1, "hol:ty.var", [.term 1]), (2, "hol:tm.var", [.term 2, .node 1]), (3, "hol:REFL", [.node 2]),
   (4, "hol:ty.bool", []), (5, "hol:type-pair", [.node first, .node second]),
   (6, "hol:INST_TYPE", [.node 3, .term 3, .node 5, .term 4])]

def cInstType : Claim String :=
  claim "inst-type" 0 [] (thmJ emptyP (eqP boolP X X))
    [(1, pstr "A"), (2, pstr "x"), (3, pex [pex [tA, boolP]]), (4, emptyP)] (instTypeProof 1 4) (.node 6)

def cInstTypeKey : Claim String :=
  claim "inst-type-key" 0 [] (thmJ emptyP (eqP boolP X X))
    [(1, pstr "A"), (2, pstr "x"), (3, pex [pex [boolP, tA]]), (4, emptyP)] (instTypeProof 4 1) (.node 6)

def cEqMp : Claim String :=
  claim "eq-mp" 0 [] (thmJ (setP [ePQ, P]) Q)
    [(1, pstr "p"), (2, pstr "q"), (3, setP [ePQ]), (4, setP [P]), (5, setP [ePQ, P])]
    [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]), (3, "hol:tm.var", [.term 2, .node 1]),
     (4, "hol:const.=", [.node 1]), (5, "hol:tm.comb", [.node 4, .node 2]),
     (6, "hol:tm.comb", [.node 5, .node 3]), (7, "hol:ASSUME", [.node 6, .term 3]),
     (8, "hol:ASSUME", [.node 2, .term 4]), (9, "hol:EQ_MP", [.node 7, .node 8, .term 5])] (.node 9)

/-- HOL Light's `TRUTH`: `EQ_MP (SYM T_DEF) (REFL (\p. p))`, with
`SYM th = EQ_MP (MK_COMB (AP_TERM (=) th, REFL l)) (REFL l)` and `AP_TERM f th = MK_COMB (REFL f, th)`. -/
def cTruth : Claim String :=
  claim "truth" 0 [] (thmJ emptyP tC) [(1, pstr "p"), (2, emptyP)]
    [(1, "hol:ty.bool", []), (2, "hol:tm.var", [.term 1, .node 1]), (3, "hol:tm.abs", [.node 2, .node 2]),
     (4, "hol:def.T", []), (5, "hol:const.=", [.node 1]), (6, "hol:REFL", [.node 5]),
     (7, "hol:MK_COMB", [.node 6, .node 4, .term 2]), (8, "hol:const.T", []), (9, "hol:REFL", [.node 8]),
     (10, "hol:MK_COMB", [.node 7, .node 9, .term 2]), (11, "hol:EQ_MP", [.node 10, .node 9, .term 2]),
     (12, "hol:REFL", [.node 3]), (13, "hol:EQ_MP", [.node 11, .node 12, .term 2])] (.node 13)

/-- **The world**: HOL Light's kernel, `T_DEF`, the type `1`, and the claims. -/
def holWorld : World String :=
  world (admissions worldRules)
    [cRefl, cSymbolName, cAssume, cDeduct, cTrans, cTransBadUnion, cMkComb, cAbs, cAbsFreeInHyp,
     cBeta, cInst, cInstBadImage, cInstType, cInstTypeKey, cEqMp, cTruth]

/-- Every rule of the kernel and of the extensions is determined. -/
theorem worldRules_determined : worldRules.all (fun x => x.2.determinedB) = true := by decide

/-- **The verdicts**: the eleven proofs are accepted, the five controls refused. -/
theorem holWorld_accepted : (runWorld 10000 holWorld).T =
    ["refl", "assume", "deduct", "trans", "mk-comb", "abs", "beta", "inst", "inst-type", "eq-mp",
      "truth"] := by
  decide +kernel

/-- Every rule is admitted, and every accepted claim becomes a rule. -/
theorem holWorld_rules : ((runWorld 10000 holWorld).L.rules.map Prod.fst) =
    worldRules.map Prod.fst ++
      ["refl", "assume", "deduct", "trans", "mk-comb", "abs", "beta", "inst", "inst-type", "eq-mp",
        "truth"] := by
  decide +kernel

end Mettapedia.Logic.TierZero.Adequacy.HOL.Controls
