import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsSemiNaive

/-! Positive and separating controls for the dependency frontier. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds.SemiNaive.Controls

def link (_ : Unit) : SetStoreClosure.Instance Nat := ⟨{0}, {1}⟩
def axiomRule (_ : Unit) : SetStoreClosure.Instance Nat := ⟨∅, {1}⟩
def chain (choice : Bool) : SetStoreClosure.Instance Nat :=
  if choice then ⟨{1}, {2}⟩ else ⟨{0}, {1}⟩

theorem one_round : (rounds link {0} 1).known = {0, 1} := by
  ext value
  simp [rounds, round, heads, Hot, link, or_comm]

theorem repeated_production_stops : (round link (rounds link {0} 1)).delta = ∅ := by
  apply (delta_empty_iff_fixed link _ (rounds_invariant link {0} 1)).mpr
  rw [one_round]
  ext value
  simp [immediate, link]

theorem transitive_chain : (rounds chain {0} 2).known = {0, 1, 2} := by
  rw [rounds_eq_stage]
  ext value
  simp [stage, immediate, chain, Bool.exists_bool]
  aesop

theorem empty_premise_is_inspected : (rounds axiomRule ∅ 1).known = {1} := by
  ext value
  simp [rounds, round, heads, Hot, axiomRule]

/-- Dropping the initial frontier silently loses an enabled consequence. -/
theorem wrong_frontier_loses_row :
    (round link ⟨{0}, ∅⟩).known = {0} ∧ immediate link {0} = {0, 1} := by
  constructor <;> ext value <;> simp [round, heads, Hot, link, immediate, or_comm]

theorem wrong_frontier_invalid : ¬ Invariant link ⟨{0}, ∅⟩ := by
  intro valid
  have same := round_known link ⟨{0}, ∅⟩ valid
  rw [wrong_frontier_loses_row.1, wrong_frontier_loses_row.2] at same
  have member : 1 ∈ ({0, 1} : Set Nat) := by simp
  rw [← same] at member
  simp at member

def growth (n : Nat) : SetStoreClosure.Instance Nat := ⟨{n}, {n + 1}⟩

theorem growth_stage (n : Nat) : stage growth {0} n = {value | value ≤ n} := by
  induction n with
  | zero => ext value; simp [stage]
  | succ n ih =>
    rw [stage_succ, ih]
    ext value
    simp only [immediate, growth, Set.mem_union, Set.mem_ofPred_eq,
      Finset.mem_singleton, forall_eq]
    constructor
    · rintro (old | ⟨i, enabled, rfl⟩) <;> omega
    · intro bound
      by_cases old : value ≤ n
      · exact Or.inl old
      · exact Or.inr ⟨n, Nat.le_refl _, by omega⟩

/-- The finite seed does not make constructor-like growth terminate. -/
theorem finite_seed_never_stops (n : Nat) :
    (round growth (rounds growth {0} n)).delta ≠ ∅ := by
  intro stopped
  have fixed := (delta_empty_iff_fixed growth _ (rounds_invariant growth {0} n)).mp stopped
  rw [rounds_eq_stage, growth_stage] at fixed
  have next : n + 1 ∈ immediate growth {value | value ≤ n} := by
    refine Or.inr ⟨n, ?_, ?_⟩
    · intro premise member
      have same : premise = n := Finset.mem_singleton.mp member
      simp [same]
    · simp [growth]
  rw [fixed] at next
  exact Nat.not_succ_le_self n next

#print axioms transitive_chain
#print axioms wrong_frontier_invalid
#print axioms finite_seed_never_stops

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds.SemiNaive.Controls
