import Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionObservation

/-!
# The proof-relevant boundary between Compρ observation and path admission

The existing NIK observed-refinement square is stated over ordinary GSLT
execution paths.  Prime's intrinsic interaction fibre is richer: an
`EventPath` retains the authored site and occurrence evidence of every step.

This module proves that endpoint/path erasure cannot serve as a universal
adapter between those interfaces.  Two intrinsic computations may erase to
the same GSLT rewrite path while their exact occurrence histories differ.
Consequently no readout of the erased path can reconstruct the provenance
observation, and no site-sensitive policy can factor through erasure.

The result does not weaken path-based NIK admission.  It scopes that interface
to observations invariant under interaction erasure and establishes the
requirement for a proof-relevant execution refinement square before intrinsic
`Compρ` admission is claimed.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionNIKBoundary

open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionObservation

namespace Canary

open Mettapedia.GSLT.Core.InteractionEvent.Canary
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionObservation.Canary

/-- Site and occurrence evidence are absent from ordinary rewrite-path
erasure.  The cheap and dear one-step computations therefore have the same
erased execution. -/
theorem cheap_dear_erasure_equal :
    erase cheapComputation = erase dearComputation := by
  rfl

/-- Exact occurrence provenance cannot be reconstructed uniformly from the
erased GSLT path. -/
theorem no_provenance_readout_from_erasure :
    ¬ ∃ readout : loopTheory.RewritePath () () →
        List (Occurrence loopPresentation),
      ∀ execution : Computation loopInterpretation loopPresentation
          loopTerm loopTerm,
        readout (erase execution) = events execution := by
  rintro ⟨readout, factors⟩
  have cheap := factors cheapComputation
  have dear := factors dearComputation
  apply cheap_dear_provenance_distinct
  rw [← cheap, ← dear, cheap_dear_erasure_equal]

/-- The obstruction already appears at the Boolean policy layer.  No policy
on erased paths can decide which authenticated loop site occurred. -/
theorem no_site_policy_from_erasure :
    ¬ ∃ policy : loopTheory.RewritePath () () → Bool,
      (∀ execution : Computation loopInterpretation loopPresentation
          loopTerm loopTerm,
        policy (erase execution) = beginsAtCheap (events execution)) := by
  rintro ⟨policy, factors⟩
  have cheap := factors cheapComputation
  have dear := factors dearComputation
  have same :
      policy (erase cheapComputation) = policy (erase dearComputation) := by
    rw [cheap_dear_erasure_equal]
  rw [cheap, dear, beginsAtCheap_cheap, beginsAtCheap_dear] at same
  exact Bool.noConfusion same

/-- The exact boundary in one statement: erasure preserves the semantic path
but cannot preserve the full provenance observation that distinguishes the
two intrinsic worlds. -/
theorem erasure_is_semantic_but_not_provenance_faithful :
    erase cheapComputation = erase dearComputation ∧
      events cheapComputation ≠ events dearComputation :=
  ⟨cheap_dear_erasure_equal, cheap_dear_provenance_distinct⟩

end Canary

#print axioms Canary.cheap_dear_erasure_equal
#print axioms Canary.no_provenance_readout_from_erasure
#print axioms Canary.no_site_policy_from_erasure
#print axioms Canary.erasure_is_semantic_but_not_provenance_faithful

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionNIKBoundary
