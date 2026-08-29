import Mettapedia.GSLT.LanguageDef.HOLNativeGSLTSlice

/-!
# Independent source semantics for the native HOL anchor slices

This module gives the two checked anchor terms a semantics that is independent
of the generated inference presentation.  It models exactly the source
fragment exercised by the anchors:

* HOL Light `REFL`, `ASSUME`, and `EQ_MP`, with ordered hypothesis merging;
* HOL4 `ASSUME` and `DISCH`, with finite-set hypothesis removal.

The term fragment contains Boolean variables, equality, and implication.
Alpha-equivalence is structural equality in this fragment; binder-bearing
terms and the remaining primitive rules are outside the statement proved here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HOLNativeSourceAdequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.HOLSourceKernel
open Mettapedia.GSLT.LanguageDef.HOLNativeGSLTSlice
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Source terms -/

/-- The selected source fragment needs one abstract Boolean variable.  The
name remains abstract here; its canonical GSLT spelling belongs to the
encoding below. -/
inductive BoolVariable where
  | p
deriving Repr, DecidableEq, Ord

/-- The closed Boolean term fragment needed by the two anchors. -/
inductive BoolTerm where
  | variable (name : BoolVariable)
  | equality (left right : BoolTerm)
  | implication (antecedent consequent : BoolTerm)
deriving Repr, DecidableEq, Ord

namespace HOLLightSource

/-- HOL Light's hypothesis lists are ordered sets.  This is the merge shape
used by `fusion.ml`; the selected anchor exercises its empty-left branch. -/
def hypothesisUnion : List BoolTerm → List BoolTerm → List BoolTerm
  | [], right => right
  | left, [] => left
  | leftHead :: leftTail, rightHead :: rightTail =>
      match compare leftHead rightHead with
      | .eq => leftHead :: hypothesisUnion leftTail rightTail
      | .lt => leftHead :: hypothesisUnion leftTail (rightHead :: rightTail)
      | .gt => rightHead :: hypothesisUnion (leftHead :: leftTail) rightTail
termination_by left right => left.length + right.length

/-- Independent source-rule semantics for the selected HOL Light primitives.
The `EQ_MP` constructor records its two theorem premises directly. -/
inductive Derives : List BoolTerm → BoolTerm → Type where
  | refl (term : BoolTerm) :
      Derives [] (.equality term term)
  | assume (proposition : BoolTerm) :
      Derives [proposition] proposition
  | eqMp {leftHypotheses rightHypotheses : List BoolTerm}
      {left right : BoolTerm} :
      Derives leftHypotheses (.equality left right) →
      Derives rightHypotheses left →
      Derives (hypothesisUnion leftHypotheses rightHypotheses) right

end HOLLightSource

namespace HOL4Source

/-- Independent source-rule semantics for the selected HOL4 primitives.
HOL4 hypotheses are finite sets, and `DISCH` removes its antecedent. -/
inductive Derives : Finset BoolTerm → BoolTerm → Type where
  | assume (proposition : BoolTerm) :
      Derives {proposition} proposition
  | disch {hypotheses : Finset BoolTerm} {conclusion : BoolTerm}
      (antecedent : BoolTerm) :
      Derives hypotheses conclusion →
      Derives (hypotheses.erase antecedent)
        (.implication antecedent conclusion)

end HOL4Source

/-! ## Encoding into the admitted GSLT vocabulary -/

private def app (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

private def tyNil : Pattern := app "TyNil"
private def tyCons (head tail : Pattern) : Pattern := app "TyCons" [head, tail]
private def tyList (values : List Pattern) : Pattern := values.foldr tyCons tyNil
private def tyApp (name : Pattern) (arguments : List Pattern := []) : Pattern :=
  app "TyApp" [name, tyList arguments]

private def boolType : Pattern := app "$hol.type.bool"
private def functionType (domain codomain : Pattern) : Pattern :=
  tyApp (app "$hol.name.102.117.110") [domain, codomain]

private def encodeVariable : BoolVariable → Pattern
  | .p => app "$hol.name.112"

/-- Total encoding of the independent source term fragment. -/
def encodeTerm : BoolTerm → Pattern
  | .variable name => app "TmVar" [encodeVariable name, boolType]
  | .equality left right =>
      let equalityType := functionType boolType (functionType boolType boolType)
      let equality := app "TmConst" [app "$hol.name.61", equalityType]
      app "TmApp" [app "TmApp" [equality, encodeTerm left], encodeTerm right]
  | .implication antecedent consequent =>
      let implicationType := functionType boolType (functionType boolType boolType)
      let implication :=
        app "TmConst" [app "$hol.name.61.61.62", implicationType]
      app "TmApp"
        [app "TmApp" [implication, encodeTerm antecedent], encodeTerm consequent]

private def encodeHypotheses : List BoolTerm → Pattern
  | [] => app "HypsNil"
  | hypothesis :: hypotheses =>
      app "HypsCons" [encodeTerm hypothesis, encodeHypotheses hypotheses]

def encodeTheorem (hypotheses : List BoolTerm) (conclusion : BoolTerm) : Pattern :=
  app "Thm" [encodeHypotheses hypotheses, encodeTerm conclusion]

/-! ## Cross-semantics anchors -/

def propositionP : BoolTerm := .variable .p

/-- The source derivation uses both premises of `EQ_MP`; its result context is
the exact ordered union of the premise contexts. -/
def holLightSourceAnchor : HOLLightSource.Derives [propositionP] propositionP :=
  by
    simpa [HOLLightSource.hypothesisUnion] using
      HOLLightSource.Derives.eqMp
        (HOLLightSource.Derives.refl propositionP)
        (HOLLightSource.Derives.assume propositionP)

/-- The source derivation uses `DISCH` to remove the sole antecedent. -/
def hol4SourceAnchor :
    HOL4Source.Derives ∅ (.implication propositionP propositionP) := by
  simpa using
    HOL4Source.Derives.disch propositionP
      (HOL4Source.Derives.assume propositionP)

theorem holLight_goal_encodes_source_anchor :
    holLightGoal =
      holLightNativeProfile.derived
        (encodeTheorem [propositionP] propositionP) := by
  rfl

theorem hol4_goal_encodes_source_anchor :
    hol4Goal =
      hol4NativeProfile.derived
        (encodeTheorem [] (.implication propositionP propositionP)) := by
  rfl

/-- Exact source-semantics statement for the selected HOL Light anchor.  It
connects a source-rule derivation to the GSLT goal encoding without claiming
completeness for additional HOL terms or rules.  Executable native-term
acceptance remains the separate CeTTa/Lean gate in `HOLNativeGSLTSlice`. -/
theorem holLight_anchor_source_alignment :
    Nonempty (HOLLightSource.Derives [propositionP] propositionP) ∧
      holLightGoal =
        holLightNativeProfile.derived
          (encodeTheorem [propositionP] propositionP) :=
  ⟨⟨holLightSourceAnchor⟩, holLight_goal_encodes_source_anchor⟩

/-- Exact source-semantics statement for the selected HOL4 anchor. -/
theorem hol4_anchor_source_alignment :
    Nonempty
      (HOL4Source.Derives ∅ (.implication propositionP propositionP)) ∧
      hol4Goal =
        hol4NativeProfile.derived
          (encodeTheorem [] (.implication propositionP propositionP)) :=
  ⟨⟨hol4SourceAnchor⟩, hol4_goal_encodes_source_anchor⟩

/-! ## Checked native-anchor certificates -/

/-- The selected HOL Light fragment has one certificate that keeps all four
load-bearing facts together: an independent source-rule derivation, admission
of the exact GSLT package, a native derivation in the generated presentation,
and exact recovery of the submitted proof term. -/
structure HOLLightAnchorCertificate
    (derivation : Derivation holLightAdmittedSource.definition holLightGoal) :
    Prop where
  sourceDerivation :
    Nonempty (HOLLightSource.Derives [propositionP] propositionP)
  admission : holLightNativeSource.validate = .ok holLightAdmittedSource
  erasure : derivation.erase = holLightEqMpProof
  goalEncoding :
    holLightGoal =
      holLightNativeProfile.derived
        (encodeTheorem [propositionP] propositionP)

/-- Exact checked anchor for the selected HOL Light source fragment. -/
theorem holLight_checked_native_anchor :
    ∃ derivation : Derivation holLightAdmittedSource.definition holLightGoal,
      HOLLightAnchorCertificate derivation := by
  rcases holLightEqMpProof_exact_derivation with ⟨derivation, herasure⟩
  exact
    ⟨derivation,
      { sourceDerivation := ⟨holLightSourceAnchor⟩
        admission := holLightNativeSource_validate
        erasure := herasure
        goalEncoding := holLight_goal_encodes_source_anchor }⟩

/-- HOL4 receives its own certificate because its hypothesis discipline and
primitive rules are not identified with HOL Light's without a bridge theorem. -/
structure HOL4AnchorCertificate
    (derivation : Derivation hol4AdmittedSource.definition hol4Goal) : Prop where
  sourceDerivation :
    Nonempty
      (HOL4Source.Derives ∅ (.implication propositionP propositionP))
  admission : hol4NativeSource.validate = .ok hol4AdmittedSource
  erasure : derivation.erase = hol4DischProof
  goalEncoding :
    hol4Goal =
      hol4NativeProfile.derived
        (encodeTheorem [] (.implication propositionP propositionP))

/-- Exact checked anchor for the selected HOL4 source fragment. -/
theorem hol4_checked_native_anchor :
    ∃ derivation : Derivation hol4AdmittedSource.definition hol4Goal,
      HOL4AnchorCertificate derivation := by
  rcases hol4DischProof_exact_derivation with ⟨derivation, herasure⟩
  exact
    ⟨derivation,
      { sourceDerivation := ⟨hol4SourceAnchor⟩
        admission := hol4NativeSource_validate
        erasure := herasure
        goalEncoding := hol4_goal_encodes_source_anchor }⟩

end Mettapedia.GSLT.LanguageDef.HOLNativeSourceAdequacy
