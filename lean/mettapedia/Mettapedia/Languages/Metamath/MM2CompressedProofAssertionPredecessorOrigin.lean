import Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous

/-!
# Source origin of compact assertion predecessor rows

The assertion launcher consumes a compact pending row and heap lookup row.
This module isolates the row-local origin predicate used by the physical
boundary proof.  The complete-space theorem is proved from the generic
canonical/static decomposition, so it does not normalize generated rule
bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK

def AssertionPredecessorRowOrigin (context : DirectAssertionContext)
    (atom : Atom) : Prop :=
  (compressedDynamicRowHead? atom = some "mm-compressed-step-pending" →
      atom = context.pendingRow) ∧
    (compressedDynamicRowHead? atom = some "mm-compressed-heap-lookup" →
      atom = context.lookupRow)

theorem assertionPendingRow_origin (context : DirectAssertionContext) :
    AssertionPredecessorRowOrigin context context.pendingRow := by
  constructor
  · intro _
    rfl
  · intro lookup
    simp [DirectAssertionContext.pendingRow, compressedDynamicRowHead?]
      at lookup

theorem assertionLookupRow_origin (context : DirectAssertionContext) :
    AssertionPredecessorRowOrigin context context.lookupRow := by
  constructor
  · intro pending
    simp [DirectAssertionContext.lookupRow, compressedDynamicRowHead?]
      at pending
  · intro _
    rfl

theorem assertionPredecessorRowOrigin_of_other_head
    (context : DirectAssertionContext) {atom : Atom} (head : String)
    (headExact : compressedDynamicRowHead? atom = some head)
    (pendingDifferent : head ≠ "mm-compressed-step-pending")
    (lookupDifferent : head ≠ "mm-compressed-heap-lookup") :
    AssertionPredecessorRowOrigin context atom := by
  constructor
  · intro pending
    rw [headExact] at pending
    exact (pendingDifferent (Option.some.inj pending)).elim
  · intro lookup
    rw [headExact] at lookup
    exact (lookupDifferent (Option.some.inj lookup)).elim

private theorem isDynamicRow_of_predecessor_head
    {atom : Atom}
    (head : compressedDynamicRowHead? atom =
      some "mm-compressed-step-pending" ∨
      compressedDynamicRowHead? atom =
        some "mm-compressed-heap-lookup") :
    isDynamicRow atom = true := by
  rcases head with pending | lookup
  · obtain ⟨tail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff atom
        "mm-compressed-step-pending").mp pending
    simp [isDynamicRow, dynamicRowHeads]
  · obtain ⟨tail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff atom
        "mm-compressed-heap-lookup").mp lookup
    simp [isDynamicRow, dynamicRowHeads]

/-- A supported executable shell cannot masquerade as either predecessor data
row family.  This lemma is intentionally parametric in the decoded directive;
it does not normalize any generated rule body. -/
theorem assertionPredecessorRowOrigin_of_supported
    (context : DirectAssertionContext) {atom : Atom}
    {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive) :
    AssertionPredecessorRowOrigin context atom := by
  constructor
  · intro pending
    have none := extractSupportedSourceExecFact_eq_none_of_dynamic atom
      (isDynamicRow_of_predecessor_head (Or.inl pending))
    rw [decoded] at none
    contradiction
  · intro lookup
    have none := extractSupportedSourceExecFact_eq_none_of_dynamic atom
      (isDynamicRow_of_predecessor_head (Or.inr lookup))
    rw [decoded] at none
    contradiction

theorem assertionPredecessorRowOrigin_of_shape_exclusion
    (context : DirectAssertionContext) {atom : Atom}
    (pendingExcluded : ∀ tail,
      atom ≠ .expression
        (.symbol "mm-compressed-step-pending" :: tail))
    (lookupExcluded : ∀ tail,
      atom ≠ .expression
        (.symbol "mm-compressed-heap-lookup" :: tail)) :
    AssertionPredecessorRowOrigin context atom := by
  constructor
  · intro pending
    obtain ⟨tail, shape⟩ :=
      (compressedDynamicRowHead?_eq_some_iff atom
        "mm-compressed-step-pending").mp pending
    exact (pendingExcluded tail shape).elim
  · intro lookup
    obtain ⟨tail, shape⟩ :=
      (compressedDynamicRowHead?_eq_some_iff atom
        "mm-compressed-heap-lookup").mp lookup
    exact (lookupExcluded tail shape).elim

#print axioms assertionPredecessorRowOrigin_of_other_head
#print axioms assertionPredecessorRowOrigin_of_supported
#print axioms assertionPredecessorRowOrigin_of_shape_exclusion
#print axioms assertionPendingRow_origin
#print axioms assertionLookupRow_origin

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
