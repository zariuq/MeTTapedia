import Mettapedia.Languages.CHR.MachineProgress
import Mettapedia.Languages.CHR.MachineAdvance
import Mettapedia.Languages.CHR.PolicyDeterminism

/-! Reflection of the newest-first semantics by the refined CHR machine.

Every stopped state the newest-first semantics reaches from the initial
state of some constraints is shown by the machine after enough ticks: the
machine halts with the same failure or fault, or with the same final store up
to order (`advance_reflects`). With `advance_refines_policy`, a machine run
halts exactly when the semantics can stop (`machine_halts_iff`), and all
stopped outcomes of the semantics agree up to store order
(`policy_outcomes_agree`).

The proof follows the run of the semantics. Each tick either takes policy
steps, which re-root the run (`follow_many`), or keeps its abstract state
while `admin` drops (`tick_progress`). The measure is the run length, then
`deadRank`, then `admin`, lexicographically. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem outcome_pending (state : State) :
    outcome state = .pending ↔ state.status = .running ∧ state.tasks ≠ [] := by
  unfold outcome
  cases state.status <;> cases state.tasks <;> simp

/-- A state whose outcome is not pending is one the machine no longer works on. -/
theorem stopped_of_outcome {state : State} (halted : outcome state ≠ .pending) : ¬ Active state :=
  fun active => halted ((outcome_pending state).mpr active)

/-- Observations of equivalent states agree up to store order. -/
theorem outcome_reordered {shown : Outcome} {first second : CHR.State} (related : OutcomeRel shown (observe second))
    (same : Reordered first second) : OutcomeRel shown (observe first) := by
  rcases first with ⟨tasks, store, history, nextId, status⟩
  rcases second with ⟨tasks', store', history', nextId', status'⟩
  obtain ⟨perm, -, -, statusEq, related'⟩ := same
  simp only at perm statusEq related'
  subst statusEq
  cases status with
  | failed => exact related
  | fault reason => exact related
  | running =>
    cases related' with
    | nil =>
      change OutcomeRel shown (.completed (store'.map Occurrence.constraint)) at related
      show OutcomeRel shown (.completed (store.map Occurrence.constraint))
      cases related
      exact .completed _ _ ((perm.map _).trans (by assumption))
    | cons _ _ => exact related

/-- The reflection induction, over the run length, `deadRank` and `admin`. -/
theorem reflects_from (program : Program) :
    ∀ (length rank work : Nat) (state : State) (abstract final : CHR.State),
      rank = deadRank program abstract → work = admin state → Simulates program state abstract →
      Descending state.store → abstract.WellFormed → Run program length abstract final → Terminal final →
      ∃ budget, OutcomeRel (outcome (advance (table program) budget state)) (observe final) := by
  intro length
  induction length using Nat.strong_induction_on with
  | _ length outer =>
  intro rank
  induction rank using Nat.strong_induction_on with
  | _ rank middle =>
  intro work
  induction work using Nat.strong_induction_on with
  | _ work inner =>
  intro state abstract final rankEq workEq simulates descending formed run stopped
  by_cases going : state.status = .running ∧ state.tasks ≠ []
  · obtain ⟨running, busy⟩ := going
    have descending' := tick_descending (table program) state descending simulates.fresh
    rcases tick_progress program state abstract simulates descending running busy with
      ⟨later, path, related⟩ | ⟨related, less⟩
    · obtain ⟨length', final', run', same, smaller⟩ := follow_many path formed run stopped
      have formed' := transGen_wellFormed path formed
      have reached : ∃ budget, OutcomeRel (outcome (advance (table program) budget (tick (table program) state)))
          (observe final') := by
        rcases smaller with shorter | ⟨equal, lower⟩
        · exact outer length' shorter _ _ _ later final' rfl rfl related descending' formed' run'
            (terminal_reordered same stopped)
        · subst equal
          exact middle _ (by rw [rankEq]; exact lower) _ _ later final' rfl rfl related descending' formed' run'
            (terminal_reordered same stopped)
      obtain ⟨budget, shown⟩ := reached
      refine ⟨budget + 1, ?_⟩
      rw [advance_active (table program) state ⟨running, busy⟩ budget]
      exact outcome_reordered shown same
    · obtain ⟨budget, shown⟩ := inner _ (by rw [workEq]; exact less) _ _ _ rankEq rfl related descending' formed
        run stopped
      refine ⟨budget + 1, ?_⟩
      rw [advance_active (table program) state ⟨running, busy⟩ budget]
      exact shown
  · have halted : outcome state ≠ .pending := fun pending => going ((outcome_pending state).mp pending)
    have shown := outcome_simulates program state abstract simulates
    have terminal : Terminal abstract := by
      intro pending
      rw [pending] at shown
      generalize outcome state = shownOutcome at shown halted
      cases shown
      exact halted rfl
    refine ⟨0, ?_⟩
    cases run with
    | done => exact shown
    | step head _ => exact (terminal_stuck terminal head).elim

/-- **The machine reflects the newest-first semantics.** For every state the
policy-qualified refined semantics reaches from the initial state of
`constraints` and that has stopped (failed, faulted or completed), the
machine run from the seeds of `constraints` shows its outcome after enough
ticks, with the final store up to order. -/
theorem advance_reflects (program : Program) (constraints : List Constraint) (final : CHR.State)
    (run : Relation.ReflTransGen (PolicyStep program) (initial constraints) final) (stopped : observe final ≠ .pending) :
    ∃ budget, OutcomeRel (outcome (advance (table program) budget (start (constraints.map Constraint.asHead))))
      (observe final) := by
  obtain ⟨length, counted⟩ := Run.of_reflTransGen run
  exact reflects_from program length _ _ _ (initial constraints) final rfl rfl (start_simulates program constraints)
    (start_descending _) (initial_wellFormed constraints) counted stopped

/-- **The machine halts exactly when the semantics can stop.** -/
theorem machine_halts_iff (program : Program) (constraints : List Constraint) :
    (∃ budget, outcome (advance (table program) budget (start (constraints.map Constraint.asHead))) ≠ .pending) ↔
      ∃ final, Relation.ReflTransGen (PolicyStep program) (initial constraints) final ∧ observe final ≠ .pending := by
  constructor
  · rintro ⟨budget, halted⟩
    obtain ⟨final, run, _, shown⟩ := advance_refines_policy program constraints budget
    refine ⟨final, run, fun pending => halted ?_⟩
    rw [pending] at shown
    generalize outcome (advance (table program) budget (start (constraints.map Constraint.asHead))) = shownOutcome
      at shown ⊢
    cases shown
    rfl
  · rintro ⟨final, run, stopped⟩
    obtain ⟨budget, shown⟩ := advance_reflects program constraints final run stopped
    refine ⟨budget, fun pending => stopped ?_⟩
    rw [pending] at shown
    generalize observe final = shownObservation at shown ⊢
    cases shown
    rfl

theorem outcomeRel_agree {shown first second : Outcome} (one : OutcomeRel shown first) (two : OutcomeRel shown second) :
    first = second ∨ ∃ left right, first = .completed left ∧ second = .completed right ∧ left.Perm right := by
  cases one with
  | pending => cases two; exact .inl rfl
  | completed machine abstract permuted =>
    cases two with
    | completed _ abstract' permuted' => exact .inr ⟨abstract, abstract', rfl, rfl, permuted.trans permuted'.symm⟩
  | failed => cases two; exact .inl rfl
  | fault reason => cases two; exact .inl rfl

/-- **The newest-first semantics has one outcome up to store order.** Any two
stopped states it reaches from the same initial state fail alike, fault
alike, or complete with the same constraints up to order. -/
theorem policy_outcomes_agree (program : Program) (constraints : List Constraint) (first second : CHR.State)
    (one : Relation.ReflTransGen (PolicyStep program) (initial constraints) first)
    (two : Relation.ReflTransGen (PolicyStep program) (initial constraints) second)
    (stopped : observe first ≠ .pending) (stopped' : observe second ≠ .pending) :
    observe first = observe second ∨
      ∃ left right, observe first = .completed left ∧ observe second = .completed right ∧ left.Perm right := by
  obtain ⟨budget, shown⟩ := advance_reflects program constraints first one stopped
  obtain ⟨budget', shown'⟩ := advance_reflects program constraints second two stopped'
  set seeds := start (constraints.map Constraint.asHead)
  have halted : outcome (advance (table program) budget seeds) ≠ .pending := by
    intro pending
    rw [pending] at shown
    generalize observe first = shownObservation at shown stopped
    cases shown
    exact stopped rfl
  have halted' : outcome (advance (table program) budget' seeds) ≠ .pending := by
    intro pending
    rw [pending] at shown'
    generalize observe second = shownObservation at shown' stopped'
    cases shown'
    exact stopped' rfl
  have same : advance (table program) budget seeds = advance (table program) budget' seeds :=
    calc advance (table program) budget seeds
        = advance (table program) budget' (advance (table program) budget seeds) :=
          (advance_stopped _ _ (stopped_of_outcome halted) budget').symm
      _ = advance (table program) (budget + budget') seeds := advance_add _ _ _ _
      _ = advance (table program) (budget' + budget) seeds := by rw [Nat.add_comm]
      _ = advance (table program) budget (advance (table program) budget' seeds) := (advance_add _ _ _ _).symm
      _ = advance (table program) budget' seeds := advance_stopped _ _ (stopped_of_outcome halted') budget
  rw [same] at shown
  exact outcomeRel_agree shown shown'

#print axioms advance_reflects
#print axioms machine_halts_iff
#print axioms policy_outcomes_agree

end Mettapedia.Languages.CHR.Machine
