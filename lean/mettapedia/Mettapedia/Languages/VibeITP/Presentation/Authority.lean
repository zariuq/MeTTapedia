import Mettapedia.Languages.VibeITP.Presentation.Validation

/-!
# Vibe-ITP presentation: the admitted kernel authority

The validated kernel definition and the calibration article recorded with it
in the authority catalog: the kernel's literal theorem `litIsNat(1)`, derived
through the machine-word bound and the one-byte number literal of `1`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.VibeITP.Spec

private def node (id : String) (arguments : List Pattern) (children : List RawProof) :
    RawProof :=
  .node { ruleId := ⟨id⟩, arguments } children

/-- `PSucc(p, p + 1)` for a positive numeral `p` made of ones, by the carry chain. -/
private def succOfOnes : Nat → RawProof
  | 0 => node "vibe-psucc-1" [] []
  | k + 1 => node "vibe-psucc-i" [encPos (2 ^ (k + 1) - 1), encPos (2 ^ (k + 1))]
      [succOfOnes k]

/-- The calibration statement: `litIsNat(1)`. -/
def calibrationGoal : Pattern :=
  jThm (closedApp1 (patBuiltinSym .litIsNat) (cLit (cCons (encNat 1) cNil)))

/-- Its derivation: `1` is a machine word, and its literal is the byte `1`
because `1 + 255 = 256`. -/
def calibrationArticle : RawProof :=
  node "vibe-lit-isnat" [encNat 1, cCons (encNat 1) cNil]
    [ node "vibe-nword-p" [cP1] [node "vibe-pbits-1" [encUnary 63] []],
      node "vibe-natlit-small" [encNat 1, encPos 255]
        [node "vibe-nadd-pp" [cP1, encPos 255, encPos 256]
          [node "vibe-padd-1l" [encPos 255, encPos 256] [succOfOnes 7]]] ]

set_option maxRecDepth 100000 in
theorem calibration_article_accepted :
    checkRaw kernelFixedValidated calibrationGoal calibrationArticle = true := by
  decide +kernel

/-- The same article does not prove `litIsNat(2)`. -/
def calibrationWrongGoal : Pattern :=
  jThm (closedApp1 (patBuiltinSym .litIsNat) (cLit (cCons (encNat 2) cNil)))

set_option maxRecDepth 100000 in
theorem calibration_article_rejects_other_goal :
    checkRaw kernelFixedValidated calibrationWrongGoal calibrationArticle = false := by
  decide +kernel

end Mettapedia.Languages.VibeITP.Presentation
