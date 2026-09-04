import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.OSLF.Framework.GSLTQuotientCoherence
import Mettapedia.OSLF.StructuralModal.Formula

/-!
# Checker capabilities of OSLF-generated native types

OSLF derives modal meaning from a reduction span.  That semantic generation
does not by itself make every native judgment finitely replayable.

The positive native fragment (`top`, conjunction, disjunction, spatial
heads, and diamond) has finite proof-relevant certificates, sound and
complete on its declared fragment.  Box is a universal predecessor
obligation and deliberately has no constructor in that certificate language.
The canonical OSLF retains both coordinates of a GSLT: modalities act through
its equation-compatible step relation, while the predicate carrier consists
of equation-invariant observations.  The modal maps considered in isolation
do not determine the equation theory; the full generated type system does not
discard it.

These are capability boundaries, not a total ordering of logics.
-/

namespace Mettapedia.GSLT.LanguageDef.OSLFCheckerCapabilities

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.GSLTQuotientCoherence
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.StructuralModal

/-! ## Exact positive native certificates -/

/-- On the explicitly admitted finitary fragment, semantic inhabitation is
equivalent to existence of a finite positive native certificate. -/
theorem positiveCertificate_iff_satisfies
    {span : ReductionSpan Pattern} (formula : Formula)
    (pattern : Pattern) (supported : formula.finitelyCertifiable = true) :
    Nonempty (Certificate span formula pattern) <->
      satisfiesOver span formula pattern := by
  constructor
  · rintro ⟨certificate⟩
    exact certificate.sound
  · intro inhabited
    exact Certificate.complete formula pattern supported inhabited

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

/-- The two theories have the same underlying diamond and box maps on raw
predicates because their rewrite graphs are equal.  This is not an equality
of their generated OSLF type systems: those have different semantic predicate
carriers. -/
theorem equationOnly_underlying_modal_maps_match_discrete :
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

/-- Underlying modal maps, considered without the semantic predicate carrier,
do not determine a GSLT's structural equations. -/
theorem underlying_modal_maps_do_not_determine_structural_equations :
    (∀ predicate source,
      gsltDiamond equationOnlyGSLT predicate source <->
        gsltDiamond discreteNoRewriteGSLT predicate source) /\
    (∀ predicate target,
      gsltBox equationOnlyGSLT predicate target <->
        gsltBox discreteNoRewriteGSLT predicate target) /\
    ¬ ∀ source target,
      equationOnlyGSLT.Equiv source target <->
        discreteNoRewriteGSLT.Equiv source target :=
  ⟨equationOnly_underlying_modal_maps_match_discrete.1,
    equationOnly_underlying_modal_maps_match_discrete.2,
    equationOnly_equations_differ_from_discrete⟩

/-! ## Canonical semantic terms retain the missing distinction -/

/-- The equation-only theory identifies its two authored Boolean
presentations at the semantic-term boundary. -/
theorem equationOnly_semanticTerms_identify_false_true :
    (Quotient.mk equationOnlyGSLT.equations false :
        SemanticTerm equationOnlyGSLT) =
      Quotient.mk equationOnlyGSLT.equations true :=
  Quotient.sound equationOnlyGSLT_false_true_equivalent

/-- The discrete theory retains the two Boolean presentations as distinct
semantic terms. -/
theorem discrete_semanticTerms_separate_false_true :
    (Quotient.mk discreteNoRewriteGSLT.equations false :
        SemanticTerm discreteNoRewriteGSLT) ≠
      Quotient.mk discreteNoRewriteGSLT.equations true := by
  intro equalClasses
  exact Bool.false_ne_true (Quotient.exact equalClasses)

/-- The semantic carrier retains information absent from the underlying modal
maps: identical step graphs can have different semantic term carriers exactly
when their equations differ. -/
theorem semantic_carriers_retain_equation_difference :
    (Quotient.mk equationOnlyGSLT.equations false :
        SemanticTerm equationOnlyGSLT) =
        Quotient.mk equationOnlyGSLT.equations true /\
      (Quotient.mk discreteNoRewriteGSLT.equations false :
        SemanticTerm discreteNoRewriteGSLT) ≠
        Quotient.mk discreteNoRewriteGSLT.equations true :=
  ⟨equationOnly_semanticTerms_identify_false_true,
    discrete_semanticTerms_separate_false_true⟩

#print axioms semantic_carriers_retain_equation_difference

end Mettapedia.GSLT.LanguageDef.OSLFCheckerCapabilities
