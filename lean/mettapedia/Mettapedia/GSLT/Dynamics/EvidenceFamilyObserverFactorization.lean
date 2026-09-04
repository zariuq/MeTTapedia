import Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
import Mettapedia.TypeTheory.DependentFamilyObserverFactorization

/-!
# Observer boundary for endpoint-indexed exact evidence

The evidence-indexed branching canary has a coarse completion observer which
identifies its two completed branches.  That observer is a valid split readout
of endpoint completion and it supports constant families.  It cannot support
the exact-evidence family, however: the left completed endpoint has a
singleton evidence fibre and the right completed endpoint has a Boolean
evidence fibre.

This gives one concrete extensional/intensional/operational coherence test.
An extensional observation may remain a valid companion semantics for visible
results while being too coarse to index the dependent evidence needed by the
operational theory.  Retaining the endpoint supports the family exactly;
quotienting endpoints by completion does not.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.EvidenceFamilyObserverFactorization

open Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.ExtensionalReadout

/-! ## Coarse completion as a split readout -/

/-- Select one canonical source endpoint for each completion value. -/
def completionRepresentative : Bool -> SourceTerm
  | false => .entry
  | true => .leftDone

/-- Completion is a surjective but non-faithful readout of source endpoints. -/
def completionReadout : SplitReadout SourceTerm Bool where
  observe := sourceCompletion.observe
  representative := completionRepresentative
  observe_representative := by
    intro completed
    cases completed <;> rfl

theorem completionReadout_not_faithful :
    Not completionReadout.Faithful := by
  intro faithful
  have endpointsEqual : SourceTerm.leftDone = SourceTerm.rightDone :=
    faithful rfl
  cases endpointsEqual

theorem completionReadout_not_exact :
    Not completionReadout.Exact := by
  rw [completionReadout.exact_iff_faithful]
  exact completionReadout_not_faithful

/-! ## Family-level positive and negative controls -/

/-- A constant visible-result family is compatible with completion. -/
def constantVisibleFactorization :
    FamilyFactorization completionReadout.observe (fun _ => PUnit) :=
  FamilyFactorization.constant completionReadout.observe PUnit

/-- Retaining the exact endpoint carries the endpoint-indexed evidence family
without loss. -/
def endpointEvidenceFactorization :
    FamilyFactorization id exactFamily.Exact :=
  FamilyFactorization.pullback id exactFamily.Exact

/-- Completion identifies two endpoints whose exact-evidence fibres are not
equivalent, so the evidence family cannot descend to completion values. -/
theorem exactEvidence_does_not_factor_through_completion :
    Not (Nonempty
      (FamilyFactorization completionReadout.observe exactFamily.Exact)) := by
  exact FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := SourceTerm.leftDone) (right := SourceTerm.rightDone) rfl
    completed_exact_fibres_not_equivalent

/-- Canonicalizing the right endpoint preserves completion but moves to an
endpoint with a non-equivalent exact-evidence fibre. -/
theorem canonical_completion_changes_evidence_fibre :
    completionReadout.canonicalize SourceTerm.rightDone =
        SourceTerm.leftDone ∧
      completionReadout.observe
          (completionReadout.canonicalize SourceTerm.rightDone) =
        completionReadout.observe SourceTerm.rightDone ∧
      Not (Nonempty
        (exactFamily.Exact SourceTerm.rightDone ≃
          exactFamily.Exact
            (completionReadout.canonicalize SourceTerm.rightDone))) := by
  refine ⟨rfl, rfl, ?_⟩
  intro equivalence
  exact completed_exact_fibres_not_equivalent
    ⟨equivalence.some.symm⟩

/-- Paired architectural boundary: completion remains a lawful extensional
readout and supports simple constant data, while endpoint retention supports
the dependent evidence and completion quotienting does not. -/
theorem extensional_intensional_operational_boundary :
    Function.Surjective completionReadout.observe ∧
      Nonempty
        (FamilyFactorization completionReadout.observe (fun _ => PUnit)) ∧
      Nonempty (FamilyFactorization id exactFamily.Exact) ∧
      Not (Nonempty
        (FamilyFactorization completionReadout.observe exactFamily.Exact)) :=
  ⟨completionReadout.surjective,
    ⟨constantVisibleFactorization⟩,
    ⟨endpointEvidenceFactorization⟩,
    exactEvidence_does_not_factor_through_completion⟩

#print axioms completionReadout_not_faithful
#print axioms completionReadout_not_exact
#print axioms exactEvidence_does_not_factor_through_completion
#print axioms canonical_completion_changes_evidence_fibre
#print axioms extensional_intensional_operational_boundary

end Mettapedia.GSLT.Dynamics.EvidenceFamilyObserverFactorization
