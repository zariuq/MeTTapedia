import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.OSLF.Framework.NativeTypeTheory

/-!
# Checker capabilities of OSLF-generated native types

OSLF derives modal meaning from a reduction span.  That semantic generation
does not by itself make every native judgment finitely replayable.

The positive native fragment (`top`, conjunction, disjunction, spatial
heads, and diamond) has finite proof-relevant certificates, sound and
complete on its declared fragment.  Box is a universal predecessor
obligation and deliberately has no constructor in that certificate language.
Moreover, the modalities generated from an abstract GSLT inspect its rewrite
relation, not the separately authored structural equations.

These are capability boundaries, not a total ordering of logics.
-/

namespace Mettapedia.GSLT.LanguageDef.OSLFCheckerCapabilities

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.NativeTypeTheory

/-! ## Exact positive native certificates -/

/-- On the explicitly admitted finitary fragment, semantic inhabitation is
equivalent to existence of a finite positive native certificate. -/
theorem positiveCertificate_iff_satisfies
    {span : ReductionSpan Pattern} (nativeType : NativeType)
    (pattern : Pattern) (supported : nativeType.finitelyCertifiable = true) :
    Nonempty (Certificate span nativeType pattern) <->
      satisfiesOver span nativeType pattern := by
  constructor
  · rintro ⟨certificate⟩
    exact certificate.sound
  · intro inhabited
    exact Certificate.complete nativeType pattern supported inhabited

/-! ## A true box judgment outside the positive certificate language -/

/-- A reduction span with no edges. -/
def noEdgeSpan : ReductionSpan Pattern where
  Edge := Empty
  source := fun edge => nomatch edge
  target := fun edge => nomatch edge

private def samplePattern : Pattern := .apply "oslf-capability-sample" []

/-- Universal predecessor truth can hold vacuously even though the positive
certificate syntax intentionally contains no box constructor. -/
theorem true_box_without_positive_certificate :
    satisfiesOver noEdgeSpan (.box .top) samplePattern /\
      IsEmpty (Certificate noEdgeSpan (.box .top) samplePattern) := by
  constructor
  · intro edge
    exact nomatch edge
  · exact box_not_certifiable noEdgeSpan .top samplePattern

/-! ## Structural equations are a separate authority -/

/-- The discrete-equation companion to `equationOnlyGSLT`; both theories
have the same empty rewrite relation. -/
def discreteNoRewriteGSLT : GSLT where
  Term := Bool
  equations :=
    { r := Eq
      iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩ }
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ step
    exact step.elim
  rewrites_resp_right := by
    intro _ _ _ step _
    exact step.elim

/-- The two theories generate the same diamond and box observations because
their rewrite graphs are equal. -/
theorem equationOnly_modalities_match_discrete :
    (∀ predicate source,
      gsltDiamond equationOnlyGSLT predicate source <->
        gsltDiamond discreteNoRewriteGSLT predicate source) /\
    (∀ predicate target,
      gsltBox equationOnlyGSLT predicate target <->
        gsltBox discreteNoRewriteGSLT predicate target) := by
  constructor
  · intro predicate source
    rw [gsltDiamond_spec, gsltDiamond_spec]
    simp [GSLT.Step, equationOnlyGSLT, discreteNoRewriteGSLT]
  · intro predicate target
    rw [gsltBox_spec, gsltBox_spec]
    simp [GSLT.Step, equationOnlyGSLT, discreteNoRewriteGSLT]

/-- Nevertheless their structural equation judgments differ. -/
theorem equationOnly_equations_differ_from_discrete :
    ¬ ∀ source target,
      equationOnlyGSLT.Equiv source target <->
        discreteNoRewriteGSLT.Equiv source target := by
  intro sameEquations
  have discreteEquivalent : discreteNoRewriteGSLT.Equiv false true :=
    (sameEquations false true).mp equationOnlyGSLT_false_true_equivalent
  exact Bool.false_ne_true discreteEquivalent

/-- OSLF modalities generated from the rewrite span do not determine the
GSLT's independently authored structural equations. -/
theorem oslf_modalities_do_not_determine_structural_equations :
    (∀ predicate source,
      gsltDiamond equationOnlyGSLT predicate source <->
        gsltDiamond discreteNoRewriteGSLT predicate source) /\
    (∀ predicate target,
      gsltBox equationOnlyGSLT predicate target <->
        gsltBox discreteNoRewriteGSLT predicate target) /\
    ¬ ∀ source target,
      equationOnlyGSLT.Equiv source target <->
        discreteNoRewriteGSLT.Equiv source target :=
  ⟨equationOnly_modalities_match_discrete.1,
    equationOnly_modalities_match_discrete.2,
    equationOnly_equations_differ_from_discrete⟩

end Mettapedia.GSLT.LanguageDef.OSLFCheckerCapabilities
