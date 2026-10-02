import Mettapedia.Machines.ConstraintPropagation

/-!
# Static schedules for constraint propagation

A worklist can be eliminated when a finite schedule visits every propagator
and later operations preserve the fixed points established by earlier ones.
For finite Horn rules, a checkable sufficient condition is that no later rule
writes a premise of an earlier rule. One pass then equals the independently
defined terminating worklist solver, for every input fact set and selection
policy. This is a sufficient admission criterion, not a characterization of
all programs that admit one-pass evaluation.

The store here has set semantics. The result does not license deduplication of
answer occurrences, deletion of effects, or reordering arbitrary foreign hooks.
-/

namespace Mettapedia.Machines.ConstraintPropagation.PropagationSchedule

section General

variable {S I : Type*} [PartialOrder S]

/-- Executing `q` preserves every fixed point of `p`. -/
def PreservesFixed (p q : Propagator S) : Prop :=
  ∀ s, p.apply s = s → p.apply (q.apply s) = q.apply s

theorem preservesFixed_of_commute (p q : Propagator S)
    (commute : Function.Commute p.apply q.apply) : PreservesFixed p q := by
  intro s fixed
  rw [commute s, fixed]

theorem run_preserves_fixed (ps : I → Propagator S) (schedule : List I) (i : I)
    (preserves : ∀ j ∈ schedule, PreservesFixed (ps i) (ps j))
    {s : S} (fixed : (ps i).apply s = s) :
    (ps i).apply (run ps schedule s) = run ps schedule s := by
  induction schedule generalizing s with
  | nil => exact fixed
  | cons j rest ih =>
    apply ih (fun k hk => preserves k (List.mem_cons_of_mem j hk))
    exact preserves j (by simp) s fixed

/-- Unlike assuming quiescence, these local conditions derive it for every input. -/
theorem run_fixes_members (ps : I → Propagator S) (schedule : List I)
    (idempotent : ∀ i s, (ps i).apply ((ps i).apply s) = (ps i).apply s)
    (ordered : schedule.Pairwise (fun i j => PreservesFixed (ps i) (ps j)))
    (s : S) : ∀ i ∈ schedule, (ps i).apply (run ps schedule s) = run ps schedule s := by
  induction schedule generalizing s with
  | nil => simp
  | cons j rest ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp ordered
    intro i member
    rcases List.mem_cons.mp member with same | later
    · subst i
      exact run_preserves_fixed ps rest j head (idempotent j s)
    · exact ih tail ((ps j).apply s) i later

theorem run_quiescent (ps : I → Propagator S) (schedule : List I)
    (idempotent : ∀ i s, (ps i).apply ((ps i).apply s) = (ps i).apply s)
    (ordered : schedule.Pairwise (fun i j => PreservesFixed (ps i) (ps j)))
    (covers : ∀ i, i ∈ schedule) (s : S) : Quiescent ps (run ps schedule s) := by
  intro i
  exact run_fixes_members ps schedule idempotent ordered s i (covers i)

/-- Instrument rule invocations, not the internal cost of a rule. -/
def runCounted (ps : I → Propagator S) : List I → S → S × Nat
  | [], s => (s, 0)
  | i :: rest, s =>
    let result := runCounted ps rest ((ps i).apply s)
    (result.1, result.2 + 1)

theorem runCounted_eq (ps : I → Propagator S) (schedule : List I) (s : S) :
    runCounted ps schedule s = (run ps schedule s, schedule.length) := by
  induction schedule generalizing s with
  | nil => rfl
  | cons i rest ih => simp [runCounted, run, ih]

theorem covered_nodup_length [DecidableEq I] [Fintype I] (schedule : List I)
    (covers : ∀ i, i ∈ schedule) (distinct : schedule.Nodup) :
    schedule.length = Fintype.card I := by
  have complete : schedule.toFinset = Finset.univ := by
    ext i
    simp [covers i]
  rw [← List.toFinset_card_of_nodup distinct, complete, Finset.card_univ]

theorem runCounted_exact_visits [DecidableEq I] [Fintype I]
    (ps : I → Propagator S) (schedule : List I)
    (covers : ∀ i, i ∈ schedule) (distinct : schedule.Nodup) (s : S) :
    (runCounted ps schedule s).2 = Fintype.card I := by
  rw [runCounted_eq]
  exact covered_nodup_length schedule covers distinct

end General

section Horn

variable {Fact I : Type*} [DecidableEq Fact]

theorem delta_subset_conclusions (r : HornRule Fact) (s : Finset Fact) :
    r.apply s \ s ⊆ r.conclusions := by
  intro x hx
  obtain ⟨hx, absent⟩ := Finset.mem_sdiff.mp hx
  by_cases enabled : r.premises ⊆ s
  · simp only [HornRule.apply, if_pos enabled, Finset.mem_union] at hx
    exact hx.resolve_left absent
  · simp only [HornRule.apply, if_neg enabled] at hx
    exact (absent hx).elim

theorem preservesFixed_of_disjoint (p q : HornRule Fact)
    (independent : Disjoint p.premises q.conclusions) :
    PreservesFixed p.propagator q.propagator := by
  intro s stable
  exact p.stable_of_disjoint_delta (q.subset_apply s) stable
    (independent.mono_right (delta_subset_conclusions q s))

/-- There is no dependency from a later writer to an earlier reader. -/
def Forward (rules : I → HornRule Fact) (schedule : List I) : Prop :=
  schedule.Pairwise (fun i j => Disjoint (rules i).premises (rules j).conclusions)

instance [DecidableEq I] (rules : I → HornRule Fact) (schedule : List I) :
    Decidable (Forward rules schedule) := by
  unfold Forward
  infer_instance

theorem forward_preserves (rules : I → HornRule Fact) (schedule : List I)
    (forward : Forward rules schedule) :
    schedule.Pairwise (fun i j => PreservesFixed (rules i).propagator (rules j).propagator) := by
  exact forward.imp (fun h => preservesFixed_of_disjoint _ _ h)

theorem forward_quiescent (rules : I → HornRule Fact) (schedule : List I)
    (forward : Forward rules schedule) (covers : ∀ i, i ∈ schedule)
    (s : Finset Fact) :
    Quiescent (fun i => (rules i).propagator) (run (fun i => (rules i).propagator) schedule s) :=
  run_quiescent _ schedule (fun i => (rules i).idempotent)
    (forward_preserves rules schedule forward) covers s

variable [DecidableEq I] [Fintype I] [Fintype Fact]

/-- A static pass and the dynamic worklist compute the same least model. -/
theorem forward_run_eq_solve (rules : I → HornRule Fact) (schedule : List I)
    (forward : Forward rules schedule) (covers : ∀ i, i ∈ schedule)
    (select : Selector I) (s : Finset Fact) :
    run (fun i => (rules i).propagator) schedule s = solve rules select s := by
  have solved := solve_least rules select s
  apply Finset.Subset.antisymm
  · exact run_le_fixed _ schedule solved.1 solved.2.1
  · exact solved.2.2 _ (le_run _ schedule s) (forward_quiescent rules schedule forward covers s)

end Horn

/-! ## Positive and negative controls -/

theorem chain_forward : Forward chainRules [false, true] := by decide

theorem chain_static_equals_worklist (s : Finset (Fin 3)) :
    run (fun i => (chainRules i).propagator) [false, true] s =
      solve chainRules leastPending s := by
  apply forward_run_eq_solve _ _ chain_forward
  intro i
  cases i <;> simp

theorem empty_premise_static_equals_worklist (s : Finset (Fin 2)) :
    run (fun i => (startupRules i).propagator) [false, true] s =
      solve startupRules leastPending s := by
  apply forward_run_eq_solve _ _ (by decide)
  intro i
  cases i <;> simp

theorem empty_schedule_is_quiescent {S : Type*} [PartialOrder S]
    (ps : Empty → Propagator S) (s : S) : Quiescent ps (run ps [] s) := by
  intro i
  exact i.elim

theorem reverse_chain_rejected : ¬ Forward chainRules [true, false] := by decide

theorem reverse_chain_misses_fact :
    run (fun i => (chainRules i).propagator) [true, false] {0} = {0, 1} ∧
    solve chainRules leastPending {0} = {0, 1, 2} := by decide

theorem missing_rule_misses_fact :
    run (fun i => (chainRules i).propagator) [false] {0} ≠
      solve chainRules leastPending {0} := by decide

/-- Syntactic cycles may require revisiting rules: a single pass is not enough. -/
def feedbackRules : Fin 3 → HornRule (Fin 4)
  | 0 => ⟨{0}, {1}⟩
  | 1 => ⟨{1}, {2}⟩
  | 2 => ⟨{2}, {0, 3}⟩

def feedbackSelector : Selector (Fin 3) := fun pending nonempty =>
  ⟨pending.min' nonempty, pending.min'_mem nonempty⟩

theorem feedback_requires_revisit :
    ¬ Forward feedbackRules [0, 1, 2] ∧
    run (fun i => (feedbackRules i).propagator) [0, 1, 2] {2} = {0, 2, 3} ∧
    solve feedbackRules feedbackSelector {2} = {0, 1, 2, 3} := by decide

/-- Rejection is conservative: a redundant dependency may be harmless. -/
def redundantRules : Bool → HornRule (Fin 1)
  | false => ⟨{0}, {0}⟩
  | true => ⟨∅, {0}⟩

theorem rejection_does_not_imply_incorrectness :
    ¬ Forward redundantRules [false, true] ∧
    run (fun i => (redundantRules i).propagator) [false, true] ∅ = {0} := by decide

end Mettapedia.Machines.ConstraintPropagation.PropagationSchedule
