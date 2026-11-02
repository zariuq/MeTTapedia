import Mettapedia.Logic.DerivationGraph.CheckedMaterialization
import Mettapedia.Languages.HOLLight.GraphExpansion

/-!
# Appending a certified block through the existing graph semantics

An already checked block, together with exact external-premise selection,
determines its complete receiving cache. The construction preserves every
receipt and physical address and equals the original replaying append.
Independent receivers still check the emitted primitive inferences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.CertifiedBlockAppend

open Mettapedia.Logic.DerivationGraph Mettapedia.Languages.OpenTheory
open GraphExpansion

variable {policy : AxiomPolicy} [DecidablePred policy]

def append (state : ProofExecution.State) (roots : List Nat)
    (block : ProofSystem.Certificate) {premises : List Theorem} {conclusion : Theorem}
    (_selected : lookupPremises state.cache roots = some premises)
    (_checked : BlockChecked policy premises conclusion block) : ProofExecution.State × Nat :=
  let expanded := expandBlock roots state.cache.size block
  (⟨materialize state.cache expanded.1, state.receipts ++ expanded.1.toArray⟩, expanded.2)

theorem matches_replay (state : ProofExecution.State) (roots : List Nat)
    (block : ProofSystem.Certificate) {premises : List Theorem} {conclusion : Theorem}
    (selected : lookupPremises state.cache roots = some premises)
    (checked : BlockChecked policy premises conclusion block) :
    emitBlock policy roots block state = some (append state roots block selected checked) := by
  obtain ⟨result, accepted, found⟩ := expandBlock_checked selected checked
  have same := replayFrom_eq_materialize (ruleWitness policy) accepted
  subst result
  simp [emitBlock, selected, accepted, found, append]
  rfl

theorem preserves (state : ProofExecution.State) (roots : List Nat)
    (block : ProofSystem.Certificate) {premises external : List Theorem} {conclusion : Theorem}
    (selected : lookupPremises state.cache roots = some premises)
    (checked : BlockChecked policy premises conclusion block)
    (earlier : BuildChecked policy external state) :
    let result := append state roots block selected checked
    BuildChecked policy external result.1 ∧ result.1.cache[result.2]? = some conclusion ∧
      result.1.receipts.toList = state.receipts.toList ++ (expandBlock roots state.cache.size block).1 ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → result.1.cache[index]? = some fact := by
  obtain ⟨result, root, computed, valid, found, receipts, old⟩ :=
    emitBlock_checked earlier selected checked
  have same := Option.some.inj (computed.symm.trans (matches_replay state roots block selected checked))
  rw [← same]
  exact ⟨valid, found, receipts, old⟩

#print axioms matches_replay
#print axioms preserves

end Mettapedia.Languages.HOLLight.CertifiedBlockAppend
