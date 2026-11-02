import Mettapedia.Languages.HOLLight.CachedParameterCompilation
import Mettapedia.Languages.HOLLight.ParameterSchemaCompilationControls

/-!
# Cached specialization across collapsed source carriers

The existing two-carrier schema is installed once. Identity and crossing
assignments use the same original root and add four receipts in total.
Changed source hypotheses refuse reuse, and absent roots remain absent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.CachedParameterCompilationControls

open Mettapedia.Languages.OpenTheory Mettapedia.Logic.DerivationGraph
open ReverseTranslation GraphExpansion RetainedCompilation
open ParameterSchemaCompilationControls (types names targetNames theta swappedTheta schema guardedSchema keys_distinct conclusion)

def installed : ProofExecution.State × Nat := CachedParameterCompilation.install (conclusion := conclusion) (assumptions := []) (start []) names schema

theorem installed_checked : BuildChecked emptyAxiomPolicy [] installed.1 :=
  (CachedParameterCompilation.install_checked (conclusion := conclusion) (assumptions := []) (start []) names schema (start_checked emptyAxiomPolicy [])).1

theorem installed_found : installed.1.cache[installed.2]? = some schema.proof.result :=
  (CachedParameterCompilation.install_checked (conclusion := conclusion) (assumptions := []) (start []) names schema (start_checked emptyAxiomPolicy [])).2.1

theorem two_clients_available :
    ∃ first firstRoot second secondRoot,
      CachedParameterCompilation.specialize? (conclusion := conclusion) (assumptions := []) types names targetNames theta schema keys_distinct
        installed.1 installed.2 ("cached-identity", 0) = some (first, firstRoot) ∧
      CachedParameterCompilation.specialize? (conclusion := conclusion) (assumptions := []) types names targetNames swappedTheta schema keys_distinct
        first installed.2 ("cached-crossing", 0) = some (second, secondRoot) ∧
      BuildChecked emptyAxiomPolicy [] second ∧
      second.cache[firstRoot]? = some (CachedParameterCompilation.result (conclusion := conclusion) (assumptions := []) types names targetNames theta schema) ∧
      second.cache[secondRoot]? = some (CachedParameterCompilation.result (conclusion := conclusion) (assumptions := []) types names targetNames swappedTheta schema) ∧
      second.cache[installed.2]? = some schema.proof.result ∧
      second.receipts.size = installed.1.receipts.size + 4 := by
  obtain ⟨first, firstRoot, firstComputed, firstChecked, firstFound, firstSize, _, firstOld⟩ :=
    CachedParameterCompilation.specialize_checked (conclusion := conclusion) (assumptions := []) types names targetNames theta schema keys_distinct
      installed_checked installed_found ("cached-identity", 0)
  obtain ⟨second, secondRoot, secondComputed, secondChecked, secondFound, secondSize, _, secondOld⟩ :=
    CachedParameterCompilation.specialize_checked (conclusion := conclusion) (assumptions := []) types names targetNames swappedTheta schema keys_distinct
      firstChecked (firstOld _ _ installed_found) ("cached-crossing", 0)
  refine ⟨first, firstRoot, second, secondRoot, firstComputed, secondComputed, secondChecked,
    secondOld _ _ firstFound, secondFound, secondOld _ _ (firstOld _ _ installed_found), ?_⟩
  omega

theorem schemas_different : schema.proof.result ≠ guardedSchema.proof.result := by
  intro equal
  have hypotheses := congrArg (fun fact : Theorem => fact.sequent.hyp) equal
  rw [schema.hypotheses_exact, guardedSchema.hypotheses_exact] at hypotheses
  simp only [reverseHypotheses, List.map_nil, List.map_cons, List.toFinset_nil,
    List.toFinset_cons, Finset.insert_empty] at hypotheses
  exact Finset.notMem_empty _ (hypotheses.symm ▸ Finset.mem_singleton_self _)

theorem changed_source_refused :
    CachedParameterCompilation.specialize? (conclusion := conclusion) (assumptions := [conclusion]) types names targetNames theta guardedSchema keys_distinct
      installed.1 installed.2 ("wrong-source", 0) = none :=
  CachedSubstitution.applyExpected_mismatch emptyAxiomPolicy installed.1 installed.2 schema.proof.result
    guardedSchema.proof.result (ParameterSchemaCompilation.mapping types names targetNames theta)
    ("wrong-source", 0) installed_found schemas_different

theorem missing_root_refused :
    CachedParameterCompilation.specialize? (conclusion := conclusion) (assumptions := []) types names targetNames theta schema keys_distinct
      (start []) 0 ("missing-source", 0) = none := by
  apply CachedSubstitution.applyExpected_missing
  rfl

theorem target_hypotheses_empty :
    (CachedParameterCompilation.result (conclusion := conclusion) (assumptions := []) types names targetNames theta schema).sequent.hyp = ∅ := by
  simpa only [List.map_nil, reverseHypotheses_nil] using
    CachedParameterCompilation.result_hypotheses (conclusion := conclusion) (assumptions := []) types names targetNames theta schema keys_distinct

theorem crossing_conclusion :
    (CachedParameterCompilation.result (conclusion := conclusion) (assumptions := []) types names targetNames swappedTheta schema).sequent.concl =
      reverseCanonical targetNames (ParameterSchemaCompilation.image types names targetNames swappedTheta conclusion) :=
  CachedParameterCompilation.result_conclusion (conclusion := conclusion) (assumptions := []) types names targetNames swappedTheta schema keys_distinct

theorem guard_remains :
    (CachedParameterCompilation.result (conclusion := conclusion) (assumptions := [conclusion]) types names targetNames theta guardedSchema).sequent.hyp =
      {reverseCanonical targetNames (ParameterSchemaCompilation.image types names targetNames theta conclusion)} := by
  simpa only [List.map_cons, List.map_nil, reverseHypotheses, List.map_cons, List.map_nil,
    List.toFinset_cons, List.toFinset_nil, Finset.insert_empty] using
    CachedParameterCompilation.result_hypotheses (conclusion := conclusion) (assumptions := [conclusion]) types names targetNames theta guardedSchema keys_distinct

#print axioms two_clients_available
#print axioms changed_source_refused
#print axioms missing_root_refused
#print axioms guard_remains

end Mettapedia.Languages.HOLLight.CachedParameterCompilationControls
