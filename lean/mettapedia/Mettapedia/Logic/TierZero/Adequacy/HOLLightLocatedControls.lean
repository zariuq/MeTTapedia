import Mettapedia.Logic.TierZero.Adequacy.HOLLightLocatedAdequacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceAuthorityControls

/-!
# HOL protected-publication controls and exact hypothesis boundaries

The positive case is an ordinary source ASSUME operation realized by an
actual protected CMR run. Negative source controls retain abstraction's
hypothesis-freshness condition and ASSUME's Boolean-type condition. Generic
physical controls separately reject public-space premises, forged activation
outputs, and unauthorized client publication.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLocatedControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.FirstOrder
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

def booleanVariable : CanonicalTerm :=
  ⟨.free ⟨Name.global "p", Ty.bool⟩, Ty.bool, by simp⟩

def assumed : Theorem := Theorem.emptyResult {booleanVariable} booleanVariable

theorem assume_step : (InferenceRequest.assume booleanVariable).Semantics assumed := by
  apply (InferenceRequest.check_eq_some_iff _ _).mp
  decide +kernel

/-- A genuinely used local hypothesis is present in the protected published
sequent; it is not replaced by a closed claim with the same conclusion. -/
theorem assume_reaches :
    InferenceKernelReachability.Reaches (validatedHolCalculus []) (sequentJ assumed.sequent) :=
  HOLLightLocatedAdequacy.every_inference_reaches [] emptyAxiomPolicy
    (fun _ impossible => False.elim impossible) assume_step
    (by intro premise member; cases member)

theorem assume_hypothesis_retained : assumed.sequent.hyp = {booleanVariable} := rfl

theorem assumed_claim_is_not_closed : assumed.sequent.hyp ≠ ∅ := by
  simp [assumed, Theorem.emptyResult]

theorem abstraction_with_free_hypothesis_refused (binder : SourceVar) (input : Theorem)
    (occurs : FreeInHypotheses binder input.sequent.hyp) :
    ¬∃ out, (InferenceRequest.abs binder input).Semantics out := by
  rintro ⟨out, step⟩
  exact step.1 occurs

def nonBooleanVariable : CanonicalTerm :=
  ⟨.free ⟨Name.global "q", .var (Name.global "A")⟩, .var (Name.global "A"), by simp⟩

theorem nonBoolean_assume_refused : (InferenceRequest.assume nonBooleanVariable).check = none := by
  decide +kernel

theorem nonBoolean_assume_has_no_semantics :
    ¬∃ out, (InferenceRequest.assume nonBooleanVariable).Semantics out := by
  rintro ⟨out, semantics⟩
  have accepted := (InferenceRequest.check_eq_some_iff _ _).mpr semantics
  rw [nonBoolean_assume_refused] at accepted
  cases accepted

theorem no_implicit_axiom_authority (sequent : Sequent) : ¬emptyAxiomPolicy sequent := id

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLocatedControls
