import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsStep

/-!
# Finite stabilization depth and round optimality

Finite closure, not just a finite seed or finite rule program, supplies a finite
maximum of minimum derivation depths. The result concerns completed set outcomes.
It is not a statement about bag termination, execution history or the cost of
enumerating every match in a round.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds

universe u v
variable {G : Type u} {I : Type v} [DecidableEq G]

theorem finite_closure_stabilizes (rules : I → SetStoreClosure.Instance G) (seed : Finset G)
    (finite : (SetStoreClosure.closure rules seed).Finite) :
    ∃ n, stage rules (seed : Set G) n = SetStoreClosure.closure rules seed := by
  have covered : ∀ value ∈ finite.toFinset, value ∈ finiteProofs rules (seed : Set G) := by
    intro value member
    rw [finiteProofs_eq_closure]
    exact finite.mem_toFinset.mp member
  obtain ⟨n, atStage⟩ := finite_premises_have_a_stage rules (seed : Set G) finite.toFinset covered
  refine ⟨n, Set.Subset.antisymm (stage_le_closure rules seed n) ?_⟩
  intro value member
  exact atStage value (finite.mem_toFinset.mpr member)

noncomputable def closureDepth (rules : I → SetStoreClosure.Instance G) (seed : Finset G)
    (finite : (SetStoreClosure.closure rules seed).Finite) : Nat := by
  classical
  exact Nat.find (finite_closure_stabilizes rules seed finite)

theorem closureDepth_spec (rules : I → SetStoreClosure.Instance G) (seed : Finset G)
    (finite : (SetStoreClosure.closure rules seed).Finite) :
    stage rules (seed : Set G) (closureDepth rules seed finite) = SetStoreClosure.closure rules seed := by
  classical
  exact Nat.find_spec (finite_closure_stabilizes rules seed finite)

theorem closureDepth_le_iff (rules : I → SetStoreClosure.Instance G) (seed : Finset G)
    (finite : (SetStoreClosure.closure rules seed).Finite) (n : Nat) :
    closureDepth rules seed finite ≤ n ↔ stage rules (seed : Set G) n = SetStoreClosure.closure rules seed := by
  classical
  constructor
  · intro bound
    apply Set.Subset.antisymm (stage_le_closure rules seed n)
    rw [← closureDepth_spec rules seed finite]
    exact stage_mono rules (seed : Set G) bound
  · exact Nat.find_min' (finite_closure_stabilizes rules seed finite)

theorem closureDepth_bounds_minimumDepth (rules : I → SetStoreClosure.Instance G) (seed : Finset G)
    (finite : (SetStoreClosure.closure rules seed).Finite) (value : G)
    (derived : value ∈ finiteProofs rules (seed : Set G)) :
    minimumDepth rules (seed : Set G) value derived ≤ closureDepth rules seed finite :=
  (closure_by_depth_iff rules seed _).mp (closureDepth_spec rules seed finite) value derived

theorem positive_closureDepth_is_attained (rules : I → SetStoreClosure.Instance G) (seed : Finset G)
    (finite : (SetStoreClosure.closure rules seed).Finite)
    (positive : 0 < closureDepth rules seed finite) :
    ∃ (value : G) (derived : value ∈ finiteProofs rules (seed : Set G)),
      minimumDepth rules (seed : Set G) value derived = closureDepth rules seed finite := by
  classical
  by_contra noMaximum
  have earlier : ∀ value (derived : value ∈ finiteProofs rules (seed : Set G)),
      minimumDepth rules (seed : Set G) value derived ≤ closureDepth rules seed finite - 1 := by
    intro value derived
    have bound := closureDepth_bounds_minimumDepth rules seed finite value derived
    have different : minimumDepth rules (seed : Set G) value derived ≠ closureDepth rules seed finite :=
      fun same => noMaximum ⟨value, derived, same⟩
    omega
  have complete := (closure_by_depth_iff rules seed _).mpr earlier
  have impossible := (closureDepth_le_iff rules seed finite _).mpr complete
  omega

omit [DecidableEq G] in
theorem closed_iff_immediate (rules : I → SetStoreClosure.Instance G) (rows : Finset G) :
    SetStoreClosure.Closed rules rows ↔ immediate rules (rows : Set G) = (rows : Set G) := by
  constructor
  · intro closed
    apply Set.Subset.antisymm
    · rintro value (old | ⟨i, enabled, made⟩)
      · exact old
      · exact closed i enabled made
    · exact immediate_extensive rules _
  · intro fixed i enabled value made
    change value ∈ (rows : Set G)
    rw [← fixed]
    exact Or.inr ⟨i, enabled, made⟩

section Actual

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open SetStoreSyntax

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

theorem every_terminal_iff_depth (slots : signature.vars ≃ Nat) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (execution : Nat → Finset (Term signature)) (ground : GroundRows (execution 0))
    (advances : ∀ n, EveryAdvance timing P (execution n) (execution (n + 1)))
    (finite : (SetStoreClosure.closure (consequence (P := P)) (execution 0)).Finite) (n : Nat) :
    TerminalWith .every timing P (execution n) ↔
      closureDepth (consequence (P := P)) (execution 0) finite ≤ n := by
  have actual := every_run_stage slots timing pure rules covers execution ground advances n
  rw [discipline_terminal_iff_closed slots .every timing _ actual.1 pure rules covers
    (by intro impossible; cases impossible), closed_iff_immediate, actual.2,
    closureDepth_le_iff, stage_eq_closure_iff_fixed]

theorem every_steps_exactly (slots : signature.vars ≃ Nat) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (execution : Nat → Finset (Term signature)) (ground : GroundRows (execution 0))
    (advances : ∀ n, EveryAdvance timing P (execution n) (execution (n + 1)))
    (finite : (SetStoreClosure.closure (consequence (P := P)) (execution 0)).Finite) :
    TerminalWith .every timing P
        (execution (closureDepth (consequence (P := P)) (execution 0) finite)) ∧
      ∀ k, k < closureDepth (consequence (P := P)) (execution 0) finite →
        DisciplinedStep .every timing P (execution k) (execution (k + 1)) := by
  refine ⟨(every_terminal_iff_depth slots timing pure rules covers execution ground advances finite _).mpr le_rfl, ?_⟩
  intro k earlier
  rcases advances k with transition | ⟨_, terminal⟩
  · exact transition
  · have late := (every_terminal_iff_depth slots timing pure rules covers execution ground advances finite k).mp terminal
    omega

theorem no_discipline_finishes_earlier (discipline : Discipline) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (execution : Nat → Finset (Term signature)) (ground : GroundRows (execution 0))
    (finite : (SetStoreClosure.closure (consequence (P := P)) (execution 0)).Finite)
    (n : Nat) (transitions : ∀ k, k < n →
      DisciplinedStep discipline timing P (execution k) (execution (k + 1)))
    (complete : (execution n : Set (Term signature)) =
      SetStoreClosure.closure (consequence (P := P)) (execution 0)) :
    closureDepth (consequence (P := P)) (execution 0) finite ≤ n := by
  apply (closureDepth_le_iff _ _ finite n).mpr
  apply Set.Subset.antisymm (stage_le_closure _ _ n)
  rw [← complete]
  exact (discipline_prefix_bound discipline timing pure execution ground n transitions).2

end Actual

#print axioms finite_closure_stabilizes
#print axioms closureDepth_le_iff
#print axioms closureDepth_bounds_minimumDepth
#print axioms positive_closureDepth_is_attained
#print axioms every_terminal_iff_depth
#print axioms every_steps_exactly
#print axioms no_discipline_finishes_earlier

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds
