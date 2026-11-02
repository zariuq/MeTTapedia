import Mettapedia.Logic.LP.PropositionalConnectionChainer

/-!
# Independent Boolean and branch-restoration controls

The satisfiable three-clause matrix has an explicit valuation and rejects
the trace that would close a sibling against a completed branch. Genuine
proofs close both root siblings separately and use reduction against a live
ancestor after nested extensions.
-/

namespace Mettapedia.Logic.LP.PropositionalConnectionControls

open FixtureAtom

def satisfiableClauses : ConnCNF FixtureAtom := [[.pos p, .pos q], [.neg p, .neg q], [.pos q]]

def valuation : FixtureAtom → Bool
  | p => false
  | q => true

def siblingLeakTrace : ProofTrace FixtureAtom :=
  [.step_extend (.pos p) [.neg p, .neg q], .step_extend (.neg q) [.pos q], .step_reduce (.pos q)]

def siblingLeakProof : ProofObj FixtureAtom := ⟨3, [.pos p, .pos q], siblingLeakTrace⟩

theorem the_matrix_has_the_stated_boolean_model : ConnSatisfies valuation satisfiableClauses := by
  simp [ConnSatisfies, satisfiableClauses, Lit.eval, valuation]

theorem the_sibling_leak_trace_is_rejected : checkProof satisfiableClauses siblingLeakProof = false := by
  decide +kernel

theorem every_proof_of_the_satisfiable_matrix_is_rejected (proof : ProofObj FixtureAtom) :
    checkProof satisfiableClauses proof = false :=
  checkProof_rejects_model satisfiableClauses valuation the_matrix_has_the_stated_boolean_model proof

theorem no_fuel_can_make_dfs_refute_the_satisfiable_matrix (fuel : Nat) (root : ConnClause FixtureAtom)
    (member : root ∈ satisfiableClauses) : connProveDFS satisfiableClauses root [] fuel = none := by
  cases computed : connProveDFS satisfiableClauses root [] fuel with
  | none => rfl
  | some trace =>
      have replayed := replay_true_of_traceDerivable _ _ _ _ (connProveDFS_sound_of_some _ _ _ _ _ computed)
      have checked : checkProof satisfiableClauses ⟨fuel, root, trace⟩ = true := by
        simp only [checkProof, member, decide_true, replayed, Bool.and_self]
      exact False.elim (checkProof_unsatisfiable _ _ checked valuation the_matrix_has_the_stated_boolean_model)

theorem no_fuel_can_make_all_search_refute_the_satisfiable_matrix (fuel : Nat) (root : ConnClause FixtureAtom)
    (member : root ∈ satisfiableClauses) : connProveAll satisfiableClauses root [] fuel = [] := by
  cases computed : connProveAll satisfiableClauses root [] fuel with
  | nil => rfl
  | cons trace rest =>
      have selected : trace ∈ connProveAll satisfiableClauses root [] fuel := by
        rw [computed]
        exact List.mem_cons_self
      have replayed := replay_true_of_traceDerivable _ _ _ _ (connProveAll_sound_of_mem selected)
      have checked : checkProof satisfiableClauses ⟨fuel, root, trace⟩ = true := by
        simp only [checkProof, member, decide_true, replayed, Bool.and_self]
      exact False.elim (checkProof_unsatisfiable _ _ checked valuation the_matrix_has_the_stated_boolean_model)

def siblingClauses : ConnCNF FixtureAtom := [[.pos p, .pos q], [.neg p], [.neg q]]
def siblingProof : ProofObj FixtureAtom :=
  ⟨2, [.pos p, .pos q], [.step_extend (.pos p) [.neg p], .step_extend (.pos q) [.neg q]]⟩

theorem both_root_siblings_have_complete_proofs : checkProof siblingClauses siblingProof = true := by
  decide +kernel

def reductionClauses : ConnCNF FixtureAtom := [[.pos p], [.neg p, .pos q], [.neg q, .neg p]]
def reductionProof : ProofObj FixtureAtom :=
  ⟨3, [.pos p], [.step_extend (.pos p) [.neg p, .pos q],
    .step_extend (.pos q) [.neg q, .neg p], .step_reduce (.neg p)]⟩

theorem nested_extensions_reduce_against_a_live_ancestor : checkProof reductionClauses reductionProof = true := by
  decide +kernel

theorem dfs_finds_a_complete_sibling_proof : ∃ trace, connProveDFS siblingClauses [.pos p, .pos q] [] 2 = some trace := by
  exact ⟨siblingProof.trace, by decide +kernel⟩

theorem all_search_retains_a_complete_sibling_proof : siblingProof.trace ∈ connProveAll siblingClauses [.pos p, .pos q] [] 2 := by
  decide +kernel

theorem an_empty_clause_is_an_independent_refutation :
    checkProof ([[]] : ConnCNF FixtureAtom) ⟨0, [], []⟩ = true := by
  decide +kernel

end Mettapedia.Logic.LP.PropositionalConnectionControls
