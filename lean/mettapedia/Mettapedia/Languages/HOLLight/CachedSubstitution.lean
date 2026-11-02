import Mettapedia.Languages.HOLLight.PrimitiveTransport

/-!
# Substitution from an existing checked theorem-cache root

The actual receiving cache supplies the source theorem. Two existing
primitive inferences instantiate its types and terms without copying the
source proof. Optional exact-claim matching prevents an unrelated root from
being used as the requested source. Earlier roots and receipts are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.CachedSubstitution

open Mettapedia.Languages.OpenTheory Mettapedia.Logic.DerivationGraph GraphExpansion

def apply? (policy : AxiomPolicy) [DecidablePred policy] (state : ProofExecution.State)
    (sourceRoot : Nat) (substitution : TypeCorrectTermSubstitution) (origin : ProofExecution.Origin) :
    Option (ProofExecution.State × Nat) := do
  let source ← state.cache[sourceRoot]?
  emitBlock policy [sourceRoot] (PrimitiveTransport.substitutionBlock substitution source origin) state

theorem apply_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} {state : ProofExecution.State} {source : Theorem} {sourceRoot : Nat}
    (earlier : BuildChecked policy premises state) (found : state.cache[sourceRoot]? = some source)
    (substitution : TypeCorrectTermSubstitution) (origin : ProofExecution.Origin) :
    ∃ after root, apply? policy state sourceRoot substitution origin = some (after, root) ∧
      BuildChecked policy premises after ∧ after.cache[root]? = some (substituteTheorem substitution source) ∧
      after.receipts.size = state.receipts.size + 2 ∧
      after.receipts.toList = state.receipts.toList ++
        (expandBlock [sourceRoot] state.cache.size (PrimitiveTransport.substitutionBlock substitution source origin)).1 ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → after.cache[index]? = some fact := by
  have selected : lookupPremises state.cache [sourceRoot] = some [source] := by
    simp [lookupPremises, found]
  obtain ⟨after, root, emitted, checked, result, receipts, old⟩ :=
    emitBlock_checked earlier selected (PrimitiveTransport.substitutionBlock_checked policy substitution source origin)
  refine ⟨after, root, ?_, checked, result, ?_, receipts, old⟩
  · simpa [apply?, found] using emitted
  · simpa only [PrimitiveTransport.substitutionBlock, List.length_cons, List.length_nil] using (emitBlock_size emitted).2

theorem apply_missing (policy : AxiomPolicy) [DecidablePred policy] (state : ProofExecution.State)
    (sourceRoot : Nat) (substitution : TypeCorrectTermSubstitution) (origin : ProofExecution.Origin)
    (missing : state.cache[sourceRoot]? = none) : apply? policy state sourceRoot substitution origin = none := by
  simp [apply?, missing]

def applyExpected? (policy : AxiomPolicy) [DecidablePred policy] (state : ProofExecution.State)
    (sourceRoot : Nat) (expected : Theorem) (substitution : TypeCorrectTermSubstitution)
    (origin : ProofExecution.Origin) : Option (ProofExecution.State × Nat) := do
  let source ← state.cache[sourceRoot]?
  if source.structuralSame expected then apply? policy state sourceRoot substitution origin else none

theorem applyExpected_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} {state : ProofExecution.State} {source : Theorem} {sourceRoot : Nat}
    (earlier : BuildChecked policy premises state) (found : state.cache[sourceRoot]? = some source)
    (substitution : TypeCorrectTermSubstitution) (origin : ProofExecution.Origin) :
    ∃ after root, applyExpected? policy state sourceRoot source substitution origin = some (after, root) ∧
      BuildChecked policy premises after ∧ after.cache[root]? = some (substituteTheorem substitution source) ∧
      after.receipts.size = state.receipts.size + 2 ∧
      after.receipts.toList = state.receipts.toList ++
        (expandBlock [sourceRoot] state.cache.size (PrimitiveTransport.substitutionBlock substitution source origin)).1 ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → after.cache[index]? = some fact := by
  obtain ⟨after, root, computed, checked, result, size, receipts, old⟩ := apply_checked earlier found substitution origin
  refine ⟨after, root, ?_, checked, result, size, receipts, old⟩
  simpa [applyExpected?, found, Theorem.structuralSame_eq_true_iff] using computed

theorem applyExpected_mismatch (policy : AxiomPolicy) [DecidablePred policy] (state : ProofExecution.State)
    (sourceRoot : Nat) (source expected : Theorem) (substitution : TypeCorrectTermSubstitution)
    (origin : ProofExecution.Origin) (found : state.cache[sourceRoot]? = some source) (different : source ≠ expected) :
    applyExpected? policy state sourceRoot expected substitution origin = none := by
  simp [applyExpected?, found, Theorem.structuralSame_eq_true_iff, different]

theorem applyExpected_missing (policy : AxiomPolicy) [DecidablePred policy] (state : ProofExecution.State)
    (sourceRoot : Nat) (expected : Theorem) (substitution : TypeCorrectTermSubstitution)
    (origin : ProofExecution.Origin) (missing : state.cache[sourceRoot]? = none) :
    applyExpected? policy state sourceRoot expected substitution origin = none := by
  simp [applyExpected?, missing]

#print axioms apply_checked
#print axioms applyExpected_checked
#print axioms applyExpected_mismatch

end Mettapedia.Languages.HOLLight.CachedSubstitution
