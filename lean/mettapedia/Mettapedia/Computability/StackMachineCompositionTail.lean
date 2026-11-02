import Mettapedia.Computability.StackMachineContextCall

/-!
# Reflecting the second execution of a physical composition

A known first execution and its actual transfer form a successful prefix.
Removing that prefix from a terminal composite trace exposes the unchanged
second machine in the original total budget. No independent termination
assumption is made about that second machine.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.StackMachineComposition

open Turing StateTransition

variable (first second : FinTM2)
  [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)]

def eraseSecond (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (state : (machine first second bridge).Cfg) : second.Cfg where
  l := match state.l with
    | some (.inr (.inr label)) => some label
    | _ => none
  var := state.var.2.1
  stk key := state.stk (rightKey first second key)

theorem eraseSecond_secondConfig (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀) (state : second.Cfg) :
    eraseSecond first second bridge (secondConfig first second bridge state) = state := by
  cases state with
  | mk label registers contents => cases label <;> rfl

omit [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
theorem secondConfig_halted_iff (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀) (state : second.Cfg) :
    (secondConfig first second bridge state).l = none ↔ state.l = none := by simp [secondConfig]

theorem second_iteration (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀) (count : Nat) (state : second.Cfg) :
    (flip bind (machine first second bridge).step)^[count] (some (secondConfig first second bridge state)) =
      ((flip bind second.step)^[count] (some state)).map (secondConfig first second bridge) := by
  have commute (current : Option second.Cfg) :
      (flip bind (machine first second bridge).step) (current.map (secondConfig first second bridge)) =
        ((flip bind second.step) current).map (secondConfig first second bridge) := by
    cases current with
    | none => rfl
    | some current => exact second_step first second bridge current
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact commute _

theorem reflects_second_execution (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {before : second.Cfg} {final : (machine first second bridge).Cfg} {time : Nat}
    (executed : EvalsToInTime (machine first second bridge).step
      (secondConfig first second bridge before) (some final) time) :
    ∃ after : second.Cfg, secondConfig first second bridge after = final ∧
      Nonempty (EvalsToInTime second.step before (some after) time) := by
  have ran := executed.evals_in_steps
  rw [second_iteration] at ran
  obtain ⟨after, original, same⟩ := Option.map_eq_some_iff.mp ran
  exact ⟨after, same, ⟨⟨⟨executed.steps, original⟩, executed.steps_le_m⟩⟩⟩

/-- The first clock is not assumed smaller than the terminal bound: its
actual successful prefix determines how many transitions can be removed. -/
theorem terminal_after_known_first (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {input : List (first.Γ first.k₀)} {middle : List (first.Γ first.k₁)} {firstTime totalTime : Nat}
    (firstRun : TM2OutputsInTime first input (some middle) firstTime)
    {final : (machine first second bridge).Cfg}
    (executed : EvalsToInTime (machine first second bridge).step
      (initList (machine first second bridge) input) (some final) totalTime)
    (stopped : final.l = none) :
    ∃ after : second.Cfg, secondConfig first second bridge after = final ∧
      Nonempty (EvalsToInTime second.step (initList second (middle.map bridge)) (some after) totalTime) := by
  have started := first_execution first second bridge firstRun
  rw [← init_eq first second bridge input] at started
  have transferred := transfer_run first second bridge middle
  have prefixRun := EvalsToInTime.trans _ _ _ _ _ _ started transferred
  have tail := StackMachineContextCall.terminal_tail (machine first second bridge).step prefixRun executed
    ((source_step_none_iff (machine first second bridge) final).mpr stopped)
  exact reflects_second_execution first second bridge tail

theorem reflects_second_outputs (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {input : List (first.Γ first.k₀)} {middle : List (first.Γ first.k₁)}
    {output : List (second.Γ second.k₁)} {firstTime totalTime : Nat}
    (firstRun : TM2OutputsInTime first input (some middle) firstTime)
    (executed : TM2OutputsInTime (machine first second bridge) input (some output) totalTime) :
    Nonempty (TM2OutputsInTime second (middle.map bridge) (some output) totalTime) := by
  obtain ⟨after, same, ⟨original⟩⟩ := terminal_after_known_first first second bridge firstRun executed rfl
  rw [← second_halt_eq first second bridge output] at same
  have sourceSame := congrArg (eraseSecond first second bridge) same
  simp only [eraseSecond_secondConfig] at sourceSame
  exact ⟨by simpa only [sourceSame, TM2OutputsInTime, Option.map_some] using original⟩

end Mettapedia.Computability.StackMachineComposition
