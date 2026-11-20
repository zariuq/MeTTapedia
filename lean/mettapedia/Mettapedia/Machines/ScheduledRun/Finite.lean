import Mettapedia.Machines.ScheduledRun.Periodicity
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Relation

/-!
# Finite-state completeness of scheduled live-return certificates

Only the states actually visited need be finite. The usual finite-reachable-
state hypothesis implies this through the actual run's reachability proof.
The common clock is the LCM of visited arities; nontermination proves all of
them positive. Pigeonhole is applied to state/phase pairs, never to states
alone. An arbitrary future cutoff is supported for epoch-reset monitors.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

universe u
variable {S : Type u}

def visited (next : S → List S) (schedule : Schedule) (initial : S) : Set S :=
  {state | ∃ turn, run next schedule initial turn = some state}

noncomputable def visitedPeriod (next : S → List S) (schedule : Schedule) (initial : S)
    (finite : (visited next schedule initial).Finite) : Nat :=
  finite.toFinset.lcm (fun state => (next state).length)

theorem visited_arity_dvd (next : S → List S) (schedule : Schedule) (initial : S)
    (finite : (visited next schedule initial).Finite) {state : S}
    (member : state ∈ visited next schedule initial) :
    (next state).length ∣ visitedPeriod next schedule initial finite :=
  Finset.dvd_lcm (finite.mem_toFinset.mpr member)

theorem visitedPeriod_pos (next : S → List S) (schedule : Schedule) (initial : S)
    (finite : (visited next schedule initial).Finite) (infinite : Nonterminating next schedule initial) :
    0 < visitedPeriod next schedule initial finite := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro state member
  obtain ⟨turn, present⟩ := finite.mem_toFinset.mp member
  exact Nat.ne_of_gt (nonterminal_on_infinite next schedule initial infinite present)

theorem finite_phase_return_after (next : S → List S) (schedule : Schedule) (initial : S)
    (finite : (visited next schedule initial).Finite) (infinite : Nonterminating next schedule initial)
    (period cutoff : Nat) (positive : 0 < period) :
    ∃ first last state, cutoff ≤ first ∧ first < last ∧
      run next schedule initial first = some state ∧ run next schedule initial last = some state ∧
      Nat.ModEq period first last := by
  classical
  have present : ∀ turn, ∃ state, run next schedule initial turn = some state := by
    intro turn
    cases value : run next schedule initial turn with
    | none => exact False.elim (infinite turn value)
    | some state => exact ⟨state, rfl⟩
  let value : Nat → {state // state ∈ visited next schedule initial} := fun turn =>
    ⟨Classical.choose (present turn), turn, Classical.choose_spec (present turn)⟩
  let : Fintype {state // state ∈ visited next schedule initial} := finite.fintype
  let key := fun offset : Nat =>
    (value (cutoff + offset), (⟨(cutoff + offset) % period, Nat.mod_lt _ positive⟩ : Fin period))
  obtain ⟨i, j, different, equal⟩ := Finite.exists_ne_map_eq_of_infinite key
  have stateEq : (value (cutoff + i)).val = (value (cutoff + j)).val :=
    congrArg (fun pair => pair.1.val) equal
  have phaseEq : (cutoff + i) % period = (cutoff + j) % period :=
    congrArg (fun pair => pair.2.val) equal
  have left : run next schedule initial (cutoff + i) = some (value (cutoff + i)).val :=
    Classical.choose_spec (present _)
  have right : run next schedule initial (cutoff + j) = some (value (cutoff + i)).val :=
    (Classical.choose_spec (present _)).trans (congrArg some stateEq.symm)
  rcases lt_or_gt_of_ne different with order | order
  · exact ⟨cutoff + i, cutoff + j, _, Nat.le_add_right _ _, Nat.add_lt_add_left order _, left, right, phaseEq⟩
  · exact ⟨cutoff + j, cutoff + i, _, Nat.le_add_right _ _, Nat.add_lt_add_left order _, right, left, phaseEq.symm⟩

theorem finite_schedule_phase_detected (next : S → List S) (schedule : Schedule) (initial : S)
    (finite : (visited next schedule initial).Finite) (infinite : Nonterminating next schedule initial) :
    ∃ first last state, first < last ∧
      run next schedule initial first = some state ∧ run next schedule initial last = some state ∧
      Nat.ModEq (visitedPeriod next schedule initial finite) first last := by
  obtain ⟨first, last, state, _, order, left, right, phase⟩ :=
    finite_phase_return_after next schedule initial finite infinite
      (visitedPeriod next schedule initial finite) 0 (visitedPeriod_pos next schedule initial finite infinite)
  exact ⟨first, last, state, order, left, right, phase⟩

theorem finite_infinite_detected (next : S → List S) (initial : S)
    (finite : (visited next rotating initial).Finite) (infinite : Nonterminating next rotating initial) :
    ∃ first last state, first < last ∧
      run next rotating initial first = some state ∧ run next rotating initial last = some state ∧
      Nat.ModEq (visitedPeriod next rotating initial finite) first last :=
  finite_schedule_phase_detected next rotating initial finite infinite

theorem finite_infinite_periodic (next : S → List S) (initial : S)
    (finite : (visited next rotating initial).Finite) (infinite : Nonterminating next rotating initial) :
    ∃ start period, 0 < period ∧ PeriodicFrom next rotating initial start period := by
  obtain ⟨first, last, state, order, left, right, phase⟩ := finite_infinite_detected next initial finite infinite
  refine ⟨first, last - first, Nat.sub_pos_of_lt order, ?_⟩
  exact (return_mod_common_period next initial order state left right phase
    (fun turn _ _ value present => visited_arity_dvd next rotating initial finite ⟨turn, present⟩)).2

def reachable (next : S → List S) (initial : S) : Set S :=
  {state | Relation.ReflTransGen (fun before after => after ∈ next before) initial state}

theorem step_some_origin (next : S → List S) (schedule : Schedule) (turn : Nat)
    {observation : Option S} {after : S} (result : step next schedule turn observation = some after) :
    ∃ before, observation = some before ∧ after ∈ next before := by
  cases observation with
  | none => cases result
  | some before =>
    refine ⟨before, rfl, ?_⟩
    by_cases empty : (next before).length = 0
    · simp [step, empty] at result
    · simp only [step, empty, ↓reduceDIte, Option.some.injEq] at result
      rw [← result]
      exact List.get_mem _ _

theorem run_reachable (next : S → List S) (schedule : Schedule) (initial : S) :
    ∀ turn state, run next schedule initial turn = some state → state ∈ reachable next initial := by
  intro turn
  induction turn with
  | zero =>
    intro state present
    have same := Option.some.inj present
    subst state
    exact .refl
  | succ turn ih =>
    intro state present
    obtain ⟨before, previous, member⟩ := step_some_origin next schedule turn present
    exact (ih before previous).tail member

theorem finite_visited_of_finite_reachable (next : S → List S) (schedule : Schedule) (initial : S)
    (finite : (reachable next initial).Finite) : (visited next schedule initial).Finite :=
  finite.subset fun _ ⟨turn, present⟩ => run_reachable next schedule initial turn _ present

theorem finite_reachable_infinite_detected (next : S → List S) (initial : S)
    (finite : (reachable next initial).Finite) (infinite : Nonterminating next rotating initial) :
    ∃ first last state, first < last ∧ run next rotating initial first = some state ∧
      run next rotating initial last = some state ∧
      Nat.ModEq (visitedPeriod next rotating initial
        (finite_visited_of_finite_reachable next rotating initial finite)) first last :=
  finite_infinite_detected next initial _ infinite

end Mettapedia.Machines.ScheduledRun
