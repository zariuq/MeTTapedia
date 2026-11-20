import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsStages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOutcomes

/-!
# Actual set-store commits and immediate-consequence rounds

The store is a set, rules are a fixed set of range-restricted positive
propagation rules, and the source rows are ground. There are no takes or tells;
both ask timings consequently agree. The commit discipline remains a parameter.
The `every` statements use the existing symmetric match identity and actual
occurrence admission, not a replacement evaluator.

`EveryAdvance` totalizes a halted execution only at an actual terminal state.
It does not allow arbitrary pauses before closure. Step counts exclude the
terminal no-change probe.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings SetStoreSyntax

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

theorem actual_step_le_immediate {timing : SetStore.AskTiming}
    (pure : ∀ rule ∈ P, Propagates rule) {rows after : Finset (Term signature)}
    (ground : GroundRows rows) (transition : SetStore.Step timing P rows after) :
    (after : Set (Term signature)) ⊆ immediate (consequence (P := P)) (rows : Set (Term signature)) := by
  obtain ⟨candidate, _, admitted, answer, accepted, rfl, _⟩ := transition
  have yes := SetStore.admitted_after admitted
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer
      (candidate.information X (SetStore.represent rows)) := unifyTotal_sound _ _ accepted
  have takes := propagation_no_takes rows pure candidate yes
  intro value member
  change value ∈ SetStore.setResult rows candidate answer at member
  simp only [SetStore.setResult, takes, List.toFinset_nil, Finset.image_empty,
    SetStore.update, Finset.sdiff_empty, Finset.mem_union, Finset.mem_image] at member
  rcases member with ⟨term, prior, rfl⟩ | ⟨term, made, rfl⟩
  · rw [FirstOrder.ground_fixed answer term (ground term prior)]
    exact Or.inl prior
  · obtain ⟨m, inside, produced⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp made)
    obtain ⟨source, sourceMade, rfl⟩ := List.mem_map.mp produced
    let groundMatch := settledMember rows ground pure candidate yes answer solved m inside
    refine Or.inr ⟨groundMatch, ?_, ?_⟩
    · exact settledMember_enabled rows ground pure candidate yes answer solved m inside
    · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨source, sourceMade, Subst.applyTerm_comp _ _ _⟩)

theorem every_step_eq_immediate {timing : SetStore.AskTiming}
    (pure : ∀ rule ∈ P, Propagates rule) {rows after : Finset (Term signature)}
    (ground : GroundRows rows) (transition : DisciplinedStep .every timing P rows after) :
    (after : Set (Term signature)) = immediate (consequence (P := P)) (rows : Set (Term signature)) := by
  have raw := disciplined_is_step transition
  apply Set.Subset.antisymm (actual_step_le_immediate pure ground raw)
  obtain ⟨bag, _, _, every, answer, accepted, rfl, _⟩ := transition
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer
      (bag.information X (SetStore.represent rows)) := unifyTotal_sound _ _ accepted
  intro value member
  rcases member with old | ⟨match_, enabled, made⟩
  · exact actual_step_extensive pure ground raw old
  · exact complete_contains_consequence rows ground pure bag every.1 every.2.2.2 answer solved match_ enabled made

/-- A completed run remains stopped; it may not stutter before completion. -/
def EveryAdvance (timing : SetStore.AskTiming) (P : Program (Terms (Term signature)))
    (rows after : Finset (Term signature)) : Prop :=
  DisciplinedStep .every timing P rows after ∨
    (after = rows ∧ TerminalWith .every timing P rows)

theorem every_advance_eq_immediate (slots : signature.vars ≃ Nat)
    (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    {rows after : Finset (Term signature)} (ground : GroundRows rows)
    (advance : EveryAdvance timing P rows after) :
    (after : Set (Term signature)) = immediate (consequence (P := P)) (rows : Set (Term signature)) := by
  rcases advance with transition | ⟨same, terminal⟩
  · exact every_step_eq_immediate pure ground transition
  · subst after
    have closed := (discipline_terminal_iff_closed slots .every timing rows ground pure rules covers
      (by intro impossible; cases impossible)).mp terminal
    apply Set.Subset.antisymm (immediate_extensive _ _)
    intro value member
    rcases member with old | ⟨i, enabled, made⟩
    · exact old
    · exact closed i enabled made

theorem every_advance_preserves_ground {timing : SetStore.AskTiming}
    (pure : ∀ rule ∈ P, Propagates rule) {rows after : Finset (Term signature)}
    (ground : GroundRows rows) (advance : EveryAdvance timing P rows after) : GroundRows after := by
  rcases advance with transition | ⟨rfl, _⟩
  · exact actual_step_preserves_ground pure ground (disciplined_is_step transition)
  · exact ground

theorem exists_every_advance (slots : signature.vars ≃ Nat) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (rows : Finset (Term signature)) (ground : GroundRows rows) :
    ∃ after, EveryAdvance timing P rows after := by
  classical
  by_cases closed : SetStoreClosure.Closed (consequence (P := P)) rows
  · exact ⟨rows, Or.inr ⟨rfl,
      (discipline_terminal_iff_closed slots .every timing rows ground pure rules covers
        (by intro impossible; cases impossible)).mpr closed⟩⟩
  · obtain ⟨after, transition⟩ := discipline_progress slots .every timing rows ground pure rules covers
      (by intro impossible; cases impossible) closed
    exact ⟨after, Or.inl transition⟩

/-- Existence comes from actual admitted commits; terminal repetitions add no steps. -/
theorem exists_every_execution (slots : signature.vars ≃ Nat) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (seed : Finset (Term signature)) (ground : GroundRows seed) :
    ∃ execution : Nat → Finset (Term signature), execution 0 = seed ∧
      ∀ n, EveryAdvance timing P (execution n) (execution (n + 1)) := by
  classical
  let chooseNext (state : {rows : Finset (Term signature) // GroundRows rows}) :
      {rows : Finset (Term signature) // GroundRows rows} :=
    let offered := exists_every_advance slots timing pure rules covers state.val state.property
    ⟨Classical.choose offered, every_advance_preserves_ground pure state.property (Classical.choose_spec offered)⟩
  let states : Nat → {rows : Finset (Term signature) // GroundRows rows} :=
    Nat.rec ⟨seed, ground⟩ (fun _ state => chooseNext state)
  refine ⟨fun n => (states n).val, rfl, ?_⟩
  intro n
  exact Classical.choose_spec (exists_every_advance slots timing pure rules covers (states n).val (states n).property)

theorem every_run_stage (slots : signature.vars ≃ Nat) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (execution : Nat → Finset (Term signature)) (ground : GroundRows (execution 0))
    (advances : ∀ n, EveryAdvance timing P (execution n) (execution (n + 1))) (n : Nat) :
    GroundRows (execution n) ∧
      (execution n : Set (Term signature)) = stage (consequence (P := P)) (execution 0 : Set (Term signature)) n := by
  induction n with
  | zero => exact ⟨ground, rfl⟩
  | succ n ih =>
    refine ⟨every_advance_preserves_ground pure ih.1 (advances n), ?_⟩
    rw [every_advance_eq_immediate slots timing pure rules covers ih.1 (advances n), stage_succ, ih.2]

theorem discipline_prefix_bound (discipline : Discipline) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (execution : Nat → Finset (Term signature)) (ground : GroundRows (execution 0)) :
    ∀ n, (∀ k, k < n → DisciplinedStep discipline timing P (execution k) (execution (k + 1))) →
      GroundRows (execution n) ∧
        (execution n : Set (Term signature)) ⊆ stage (consequence (P := P)) (execution 0 : Set (Term signature)) n := by
  intro n
  induction n with
  | zero => intro _; exact ⟨ground, Set.Subset.refl _⟩
  | succ n ih =>
    intro transitions
    have earlier := ih (fun k inside => transitions k (by omega))
    have raw := disciplined_is_step (transitions n (Nat.lt_succ_self _))
    exact ⟨actual_step_preserves_ground pure earlier.1 raw,
      (actual_step_le_immediate pure earlier.1 raw).trans (immediate_mono _ earlier.2)⟩

theorem derived_row_round_lower_bound (discipline : Discipline) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (execution : Nat → Finset (Term signature)) (ground : GroundRows (execution 0))
    (n : Nat) (transitions : ∀ k, k < n →
      DisciplinedStep discipline timing P (execution k) (execution (k + 1)))
    (value : Term signature)
    (derived : value ∈ finiteProofs (consequence (P := P)) (execution 0 : Set (Term signature)))
    (delivered : value ∈ execution n) :
    minimumDepth (consequence (P := P)) (execution 0 : Set (Term signature)) value derived ≤ n :=
  (minimumDepth_le_iff _ _ value derived n).mpr
    ((discipline_prefix_bound discipline timing pure execution ground n transitions).2 delivered)

#print axioms actual_step_le_immediate
#print axioms every_step_eq_immediate
#print axioms every_run_stage
#print axioms exists_every_execution
#print axioms discipline_prefix_bound
#print axioms derived_row_round_lower_bound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds
