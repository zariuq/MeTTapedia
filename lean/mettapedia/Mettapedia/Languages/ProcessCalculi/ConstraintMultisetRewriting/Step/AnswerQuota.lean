import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Answer demand on admitted firings

The quota belongs to one evaluation episode. Its observation specifies
the number of answers published by each firing, which can be zero.
At zero quota the episode is parked. At positive quota a firing may
publish its whole contribution if it fits. Its effects and its place
in the schedule come from the underlying step.

This is an answer quota. Work, output-free effects and scheduling
fairness have their own contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.AnswerQuota

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS}
  {Firing : State → Type uF} (P : Step X O State Firing)
  (answers : (s : State) → Firing s → Nat)

/-- The same effect core and firings, restricted by the remaining
answer demand. The quota is decreased by the complete firing. -/
def step : Step X O (State × Nat) (fun s => Firing s.1) where
  frame s := P.frame s.1
  knowledge s := P.knowledge s.1
  present s := P.present s.1
  selection f := P.selection f
  target f := P.target f
  extension f := P.extension f
  information f := P.information f
  information_refines := by
    intro s f b σ solved
    exact P.information_refines f σ solved
  Shapes f := P.Shapes f
  preparedResult {s} f prepared := (P.preparedResult f prepared, s.2 - answers s.1 f)
  present_preparedResult f prepared := P.present_preparedResult f prepared
  preparedSettle f prepared := P.preparedSettle f prepared
  result_refines := by
    intro s f prepared b σ solved
    exact P.result_refines f prepared σ solved
  Admits {s} f := P.Admits f ∧ 0 < s.2 ∧ answers s.1 f ≤ s.2
  admitted_prepares _ admitted := P.prepares admitted.1

local notation "Q" => step P answers

/-- If the original admission is expressed by asks, the quota is a
state-level condition conjoined to those asks at the same cut. -/
instance guarded [P.Guarded] : (Q).Guarded where
  holds {s} f b σ := P.Holds f b σ ∧ 0 < s.2 ∧ answers s.1 f ≤ s.2
  admission f := by
    constructor
    · rintro ⟨admitted, within⟩
      have source := (P.admits_iff_prepares f).mp admitted
      exact ⟨source.1, fun b σ solved => ⟨source.2 b σ solved, within⟩⟩
    · rintro ⟨prepared, asked⟩
      have admitted := (P.admits_iff_prepares f).mpr
        ⟨prepared, fun b σ solved => (asked b σ solved).1⟩
      obtain ⟨b, σ, solved⟩ := prepared.2.2
      exact ⟨admitted, (asked b σ solved).2⟩

theorem zero_stops (s : State) (f : Firing s) :
    ¬ (Q).Admits (s := (s, 0)) f :=
  fun admitted => Nat.not_lt_zero _ admitted.2.1

theorem answerless_admitted {s : State} {f : Firing s} {quota : Nat}
    (admitted : P.Admits f) (pending : 0 < quota) (silent : answers s f = 0) :
    (Q).Admits (s := (s, quota)) f :=
  ⟨admitted, pending, silent ▸ Nat.zero_le quota⟩

theorem group_refused {s : State} {f : Firing s} {quota : Nat} (tooMany : quota < answers s f) :
    ¬ (Q).Admits (s := (s, quota)) f :=
  fun admitted => Nat.not_le_of_lt tooMany admitted.2.2

/-- Drop the demand coordinate, retaining the exact dependent run. -/
def erase : {s : State × Nat} → (Q).Run s → P.Run s.1
  | _, .nil s => .nil s.1
  | _, .cons f allowed rest => .cons f allowed.1 (erase rest)

theorem erase_last : ∀ {s : State × Nat} (run : (Q).Run s), (erase P answers run).last = run.last.1
  | _, .nil _ => rfl
  | _, .cons _ _ rest => erase_last rest

/-- An ordered run fits precisely when each event can use the quota left
by its prefix. Empty runs fit even at zero. -/
inductive Fits : {s : State} → P.Run s → Nat → Prop where
  | nil (s : State) (quota : Nat) : Fits (.nil s) quota
  | cons {s : State} {f : Firing s} {admitted : P.Admits f} {quota : Nat}
      {rest : P.Run (P.result f admitted)} :
      0 < quota → answers s f ≤ quota →
      Fits rest (quota - answers s f) → Fits (.cons f admitted rest) quota

theorem erase_fits : ∀ {s : State × Nat} (run : (Q).Run s), Fits P answers (erase P answers run) s.2
  | _, .nil _ => .nil _ _
  | _, .cons _ allowed rest => .cons allowed.2.1 allowed.2.2 (erase_fits rest)

/-- Exact characterization of schedules of the demand-restricted step. -/
theorem run_iff_fits {s : State} (run : P.Run s) (quota : Nat) :
    (∃ actual : (Q).Run (s, quota), erase P answers actual = run) ↔ Fits P answers run quota := by
  constructor
  · rintro ⟨actual, rfl⟩
    exact erase_fits P answers actual
  · intro fits
    induction fits with
    | nil s quota => exact ⟨.nil (s, quota), rfl⟩
    | @cons s f admitted quota rest pending within fits ih =>
      obtain ⟨actual, projected⟩ := ih
      have allowed : (Q).Admits (s := (s, quota)) f := ⟨admitted, pending, within⟩
      exact ⟨.cons f allowed actual, congrArg (fun tail => Step.Run.cons f admitted tail) projected⟩

/-- The published answers and the retained quota account for exactly the
supplied demand, including paths through answerless commits. -/
theorem balance {s : State × Nat} (run : (Q).Run s) :
    run.last.2 + ((erase P answers run).word.map fun e => answers e.1 e.2).sum = s.2 := by
  induction run with
  | nil => simp [erase, Step.Run.last, Step.Run.word]
  | @cons s f allowed rest ih =>
    have within : answers s.1 f ≤ s.2 := allowed.2.2
    change _ = s.2 - answers s.1 f at ih
    change rest.last.2 + (answers s.1 f + ((erase P answers rest).word.map
      fun e => answers e.1 e.2).sum) = s.2
    omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.AnswerQuota
