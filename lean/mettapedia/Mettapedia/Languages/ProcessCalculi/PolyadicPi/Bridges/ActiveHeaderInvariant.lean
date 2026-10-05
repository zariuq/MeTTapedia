import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion

/-!
# Active communication headers survive every static equation

Input continuation bodies are opaque; private scope and parallel composition
expose their headers, and replication preserves header availability. The
invariant is checked separately for each arity and direction, including scope
exchange, unused restrictions, extrusion and replication unfolding. Thus an
extracted actual communication must use headers already available in the
original equation class; static changes inside guarded continuations cannot
create a different active arity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion

inductive Header where
  | input1
  | input2
  | output1
  | output2
  deriving DecidableEq, Repr

def visible (header : Header) : {Γ : Ctx sig} → Proc Γ → Bool
  | _, .var _ => false
  | _, .op .nil .nil => false
  | _, .op .par (.cons first (.cons second .nil)) => visible header first || visible header second
  | _, .op .inp1 (.cons _ (.cons _ .nil)) => decide (header = .input1)
  | _, .op .inp2 (.cons _ (.cons _ .nil)) => decide (header = .input2)
  | _, .op .out1 (.cons _ (.cons _ .nil)) => decide (header = .output1)
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => decide (header = .output2)
  | _, .op .nu (.cons body .nil) => visible header body
  | _, .op .rep (.cons body .nil) => visible header body
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem visible_rename (header : Header) :
    ∀ {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (process : Proc Γ),
      visible header (rename environment process) = visible header process
  | _, _, _, .var _ => by simp only [rename, visible]
  | _, _, _, .op .nil .nil => by simp only [rename, renameArgs, visible]
  | _, _, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, visible]
      rw [visible_rename header environment first, visible_rename header environment second]
  | _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, visible]
  | _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, visible]
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, visible]
  | _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by simp only [rename, renameArgs, visible]
  | _, _, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, visible]
      exact visible_rename header (liftRen environment [.nm]) body
  | _, _, environment, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, visible]
      exact visible_rename header environment body
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Input congruence changes only suspended bodies. No static generator
changes the arity or direction of an available active component. -/
theorem visible_structural {Γ : Ctx sig} (header : Header) {first second : Proc Γ}
    (equal : StructuralEq first second) : visible header first = visible header second := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | parComm first second =>
      simpa only [par, visible] using Bool.or_comm (visible header first) (visible header second)
  | parAssoc first second third =>
      simpa only [par, visible] using Bool.or_assoc (visible header first) (visible header second) (visible header third)
  | parUnit process => simp only [par, nil, visible, Bool.or_false]
  | nuUnused process => simpa only [nu, visible, weaken] using visible_rename header (fun _ name => .succ name) process
  | nuPar process frame =>
      simp only [par, nu, visible, weaken]
      rw [visible_rename]
  | nuSwap process => simpa only [nu, visible] using (visible_rename header swapRen process).symm
  | repUnfold process => simp only [rep, par, visible, Bool.or_self]
  | par _ _ firstIH secondIH => simpa only [par, visible] using congrArg₂ Bool.or firstIH secondIH
  | nu _ ih => simpa only [nu, visible] using ih
  | inp1 => simp only [inp1, visible]
  | inp2 => simp only [inp2, visible]
  | rep _ ih => simpa only [rep, visible] using ih

theorem visible_scope (header : Header) :
    ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (body : Proc Δ),
      visible header (scope.close body) = visible header body
  | _, _, .nil, _ => rfl
  | _, _, .bind rest, body => by
      simp only [Scope.close, nu, visible]
      exact visible_scope header rest body

def inputHeader {Γ : Ctx sig} {redex reduct : Proc Γ} :
    Communication redex reduct → Header
  | .unary .. => .input1
  | .binary .. => .input2

def outputHeader {Γ : Ctx sig} {redex reduct : Proc Γ} :
    Communication redex reduct → Header
  | .unary .. => .output1
  | .binary .. => .output2

theorem communication_input_visible {Γ : Ctx sig} {redex reduct : Proc Γ}
    (selected : Communication redex reduct) : visible (inputHeader selected) redex = true := by
  cases selected <;> simp [inputHeader, visible, par, inp1, inp2, out1, out2]

theorem communication_output_visible {Γ : Ctx sig} {redex reduct : Proc Γ}
    (selected : Communication redex reduct) : visible (outputHeader selected) redex = true := by
  cases selected <;> simp [outputHeader, visible, par, inp1, inp2, out1, out2]

/-- The actual selected receiver had its arity available in the original
class, before any scope, frame or guarded-body rearrangement. -/
theorem exposure_input_visible {Γ : Ctx sig} {source target : Proc Γ}
    (occurrence : Exposure source target) :
    visible (inputHeader occurrence.selected) source = true := by
  rw [visible_structural _ occurrence.before, visible_scope]
  simp only [par, visible, communication_input_visible occurrence.selected, Bool.true_or]

theorem exposure_output_visible {Γ : Ctx sig} {source target : Proc Γ}
    (occurrence : Exposure source target) :
    visible (outputHeader occurrence.selected) source = true := by
  rw [visible_structural _ occurrence.before, visible_scope]
  simp only [par, visible, communication_output_visible occurrence.selected, Bool.true_or]

/-- Each authored communication has matching input and output arities. -/
theorem communication_headers {Γ : Ctx sig} {redex reduct : Proc Γ}
    (selected : Communication redex reduct) :
    (inputHeader selected = .input1 ∧ outputHeader selected = .output1) ∨
      (inputHeader selected = .input2 ∧ outputHeader selected = .output2) := by
  cases selected with
  | unary => exact .inl ⟨rfl, rfl⟩
  | binary => exact .inr ⟨rfl, rfl⟩

/-- No equation representative can communicate without an available input
of one of the authored arities. Suspended input bodies remain opaque. -/
theorem no_step_of_no_inputs {Γ : Ctx sig} (source : Proc Γ)
    (unary : visible .input1 source = false) (binary : visible .input2 source = false) :
    ∀ target, ¬ StepModulo source target := by
  intro target step
  obtain ⟨occurrence⟩ := modulo_step_exposes step
  have observed := exposure_input_visible occurrence
  rcases communication_headers occurrence.selected with headers | headers
  · rw [headers.1, unary] at observed
    cases observed
  · rw [headers.1, binary] at observed
    cases observed

/-- The dual header test rejects communications in an equation class with
no active output, even if a guarded continuation contains one. -/
theorem no_step_of_no_outputs {Γ : Ctx sig} (source : Proc Γ)
    (unary : visible .output1 source = false) (binary : visible .output2 source = false) :
    ∀ target, ¬ StepModulo source target := by
  intro target step
  obtain ⟨occurrence⟩ := modulo_step_exposes step
  have observed := exposure_output_visible occurrence
  rcases communication_headers occurrence.selected with headers | headers
  · rw [headers.2, unary] at observed
    cases observed
  · rw [headers.2, binary] at observed
    cases observed

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant
