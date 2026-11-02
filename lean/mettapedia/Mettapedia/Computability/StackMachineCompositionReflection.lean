import Mettapedia.Computability.StackMachineComposition

/-!
# Recovering the first physical execution from a completed composition

The first program retains its original transitions until its halt transfers
control. A completed composite therefore contains an actual halting prefix
of that first program. The extraction is bounded by the composite's executed
steps and makes no termination assumption about competing input programs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.StackMachineComposition

open Turing StateTransition

theorem source_step_none_iff (source : FinTM2) (state : source.Cfg) :
    source.step state = none ↔ state.l = none := by
  cases state with
  | mk label registers contents => cases label <;> simp [FinTM2.step, TM2.step]

/-- A terminal caller run contains an actual terminal source prefix when
successful source transitions are preserved and embedded states are not
caller terminals. Competing source computations need not terminate. -/
theorem completed_source_prefix_generic {Source Target : Type}
    (sourceStep : Source → Option Source) (targetStep : Target → Option Target)
    (embed : Source → Target) (terminal : Target → Prop)
    (notTerminal : ∀ state, ¬ terminal (embed state))
    (preserves : ∀ before after, sourceStep before = some after → targetStep (embed before) = some (embed after))
    (count : Nat) (before : Source) (final : Target)
    (ran : (flip bind targetStep)^[count] (some (embed before)) = some final)
    (stopped : terminal final) :
    ∃ after, sourceStep after = none ∧ Nonempty (EvalsToInTime sourceStep before (some after) count) := by
  induction count generalizing before with
  | zero =>
      have same := Option.some.inj ran
      exact False.elim (notTerminal before (by rw [same]; exact stopped))
  | succ count ih =>
      cases advanced : sourceStep before with
      | none => exact ⟨before, advanced, ⟨{ steps := 0, steps_le_m := Nat.zero_le _, evals_in_steps := rfl }⟩⟩
      | some middle =>
          have called := preserves before middle advanced
          simp only [Function.iterate_succ_apply, flip, Option.bind_eq_bind, Option.bind_some, called] at ran
          obtain ⟨after, halted, ⟨tail⟩⟩ := ih middle ran
          have joined := EvalsToInTime.trans sourceStep 1 count _ _ _ (oneStep advanced) tail
          exact ⟨after, halted, ⟨{ joined.toEvalsTo with
            steps_le_m := by simpa [Nat.add_comm] using joined.steps_le_m }⟩⟩

variable (first second : FinTM2)
  [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)]

omit [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
theorem firstConfig_not_halted (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀) (state : first.Cfg) :
    (firstConfig first second bridge state).l ≠ none := by
  cases selected : state.l <;> simp [firstConfig, selected]

omit [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
theorem active_step_exists (state : first.Cfg) (label : first.Λ) (active : state.l = some label) :
    first.step state = some (Turing.TM2.stepAux (first.m label) state.var state.stk) := by
  cases state with
  | mk current registers contents =>
      dsimp only at active
      subst current
      rfl

theorem completed_first_prefix (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (count : Nat) (before : first.Cfg) (final : (machine first second bridge).Cfg)
    (ran : (flip bind (machine first second bridge).step)^[count]
      (some (firstConfig first second bridge before)) = some final)
    (stopped : final.l = none) :
    ∃ after : first.Cfg, after.l = none ∧ Nonempty (EvalsToInTime first.step before (some after) count) := by
  have preserves (before after : first.Cfg) (advanced : first.step before = some after) :
      (machine first second bridge).step (firstConfig first second bridge before) =
        some (firstConfig first second bridge after) := by
    cases active : before.l with
    | none =>
        rw [(source_step_none_iff first before).mpr active] at advanced
        cases advanced
    | some label => rw [first_step first second bridge before label active, advanced]; rfl
  obtain ⟨after, halted, execution⟩ := completed_source_prefix_generic first.step (machine first second bridge).step
    (firstConfig first second bridge) (fun state => state.l = none)
    (firstConfig_not_halted first second bridge) preserves count before final ran stopped
  exact ⟨after, (source_step_none_iff first after).mp halted, execution⟩

theorem terminal_first_halts (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {input : List (first.Γ first.k₀)} {final : (machine first second bridge).Cfg} {time : Nat}
    (executed : EvalsToInTime (machine first second bridge).step
      (initList (machine first second bridge) input) (some final) time) (halted : final.l = none) :
    ∃ after : first.Cfg, after.l = none ∧ Nonempty (EvalsToInTime first.step (initList first input) (some after) time) := by
  have ran : (flip bind (machine first second bridge).step)^[executed.steps]
      (some (firstConfig first second bridge (initList first input))) =
        some final := by
    simpa only [init_eq first second bridge input] using executed.evals_in_steps
  obtain ⟨after, stopped, ⟨prefixRun⟩⟩ := completed_first_prefix first second bridge
    executed.steps (initList first input) final ran halted
  exact ⟨after, stopped, ⟨{ prefixRun.toEvalsTo with steps_le_m := prefixRun.steps_le_m.trans executed.steps_le_m }⟩⟩

theorem outputs_first_halts (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {input : List (first.Γ first.k₀)} {output : List (second.Γ second.k₁)} {time : Nat}
    (executed : TM2OutputsInTime (machine first second bridge) input (some output) time) :
    ∃ after : first.Cfg, after.l = none ∧ Nonempty (EvalsToInTime first.step (initList first input) (some after) time) :=
  terminal_first_halts first second bridge executed rfl

end Mettapedia.Computability.StackMachineComposition
