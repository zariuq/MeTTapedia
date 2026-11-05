import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoContinuation
import Mettapedia.OSLF.Syntax.RhoIntrinsicEncoding

/-!
# Quotation safety of the two-view continuation interpretation

The source's existing quotation-aware scope check determines which variables
can affect the interpretation. In particular, an admitted literal quotation
is independent of the surrounding receiver environment, including its active
process views. Its own nested input binders remain available.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoContinuation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open RhoSchema.IntrinsicEncoding
open ContextualCommunication (base quote)

variable {V : Type} {declaration : V → MetaArity base}

/-- The two interpretations agree on every locally available variable view. -/
structure Environment.AgreesBelow {Γ Δ : Ctx base} (depth : Nat)
    (first second : Environment declaration Γ Δ) : Prop where
  names : ∀ position, (varIdx position).val < depth → first.name position = second.name position
  processes : ∀ position, (varIdx position).val < depth → first.process position = second.process position
  activations : ∀ position, (varIdx position).val < depth → first.active position = second.active position

theorem Environment.agrees_zero {Γ Δ : Ctx base} (first second : Environment declaration Γ Δ) :
    AgreesBelow 0 first second := by
  constructor <;> intro position bounded <;> omega

theorem Environment.AgreesBelow.lift {Γ Δ : Ctx base} {depth : Nat}
    {first second : Environment declaration Γ Δ} (agree : AgreesBelow depth first second) :
    AgreesBelow (depth + 1) first.lift second.lift := by
  constructor
  · intro position bounded
    cases position with
    | zero => rfl
    | succ position =>
        apply congrArg weaken
        exact agree.names position (by simpa [varIdx] using bounded)
  · intro position bounded
    cases position with
    | succ position =>
        apply congrArg weaken
        exact agree.processes position (by simpa [varIdx] using bounded)
  · intro position bounded
    cases position with
    | zero => rfl
    | succ position =>
        apply congrArg weaken
        exact agree.activations position (by simpa [varIdx] using bounded)

mutual

theorem compileName_agrees {Γ Δ : Ctx base} (first second : Environment declaration Γ Δ)
    (depth : Nat) (agree : Environment.AgreesBelow depth first second) :
    ∀ name : Term base Γ .nm, intrinsicQuoteSafe depth name = true →
      compileName first name = compileName second name
  | .var position, safe => by
      rw [compileName,compileName]
      exact agree.names position (by simpa [intrinsicQuoteSafe] using safe)
  | .op .quo (.cons body .nil), safe => by
      have bodySafe : intrinsicQuoteSafe 0 body = true := by
        simpa [intrinsicQuoteSafe,intrinsicQuoteSafeArgs] using safe
      rw [compileName,compileName,
        compileProcess_agrees first second 0 (Environment.agrees_zero first second) body bodySafe]
termination_by name => termSize name
decreasing_by all_goals (simp only [termSize,argsSize]; omega)

theorem compileProcess_agrees {Γ Δ : Ctx base} (first second : Environment declaration Γ Δ)
    (depth : Nat) (agree : Environment.AgreesBelow depth first second) :
    ∀ process : Term base Γ .pr, intrinsicQuoteSafe depth process = true →
      compileProcess first process = compileProcess second process
  | .var position, safe => by
      rw [compileProcess,compileProcess]
      exact agree.processes position (by simpa [intrinsicQuoteSafe] using safe)
  | .op .nil .nil, _ => by rw [compileProcess,compileProcess]
  | .op .par (.cons left (.cons right .nil)), safe => by
      have parts : intrinsicQuoteSafe depth left = true ∧ intrinsicQuoteSafe depth right = true := by
        simpa [intrinsicQuoteSafe,intrinsicQuoteSafeArgs] using safe
      rw [compileProcess,compileProcess,
        compileProcess_agrees first second depth agree left parts.1,
        compileProcess_agrees first second depth agree right parts.2]
  | .op .out (.cons channel (.cons payload .nil)), safe => by
      have parts : intrinsicQuoteSafe depth channel = true ∧ intrinsicQuoteSafe depth payload = true := by
        simpa [intrinsicQuoteSafe,intrinsicQuoteSafeArgs] using safe
      rw [compileProcess,compileProcess,
        compileName_agrees first second depth agree channel parts.1,
        compileProcess_agrees first second depth agree payload parts.2]
  | .op .inp (.cons channel (.cons body .nil)), safe => by
      have parts : intrinsicQuoteSafe depth channel = true ∧ intrinsicQuoteSafe (depth + 1) body = true := by
        simpa [intrinsicQuoteSafe,intrinsicQuoteSafeArgs] using safe
      rw [compileProcess,compileProcess,
        compileName_agrees first second depth agree channel parts.1,
        compileProcess_agrees first.lift second.lift (depth + 1) agree.lift body parts.2]
  | .op .drp (.cons (.var position) .nil), safe => by
      rw [compileProcess,compileProcess]
      exact agree.activations position (by simpa [intrinsicQuoteSafe,intrinsicQuoteSafeArgs] using safe)
  | .op .drp (.cons (.op .quo (.cons body .nil)) .nil), safe => by
      have bodySafe : intrinsicQuoteSafe 0 body = true := by
        simpa [intrinsicQuoteSafe,intrinsicQuoteSafeArgs] using safe
      rw [compileProcess,compileProcess,
        compileProcess_agrees first second 0 (Environment.agrees_zero first second) body bodySafe]
termination_by process => termSize process
decreasing_by all_goals (simp only [termSize,argsSize]; omega)

end

/-- Admitted sealed code is unaffected by either view of the received name. -/
theorem quoted_code_ignores_environment {Γ Δ : Ctx base}
    (first second : Environment declaration Γ Δ) (code : Term base Γ .pr)
    (safe : intrinsicQuoteSafe 0 code = true) :
    compileName first (.op .quo (.cons code .nil)) =
      compileName second (.op .quo (.cons code .nil)) := by
  rw [compileName,compileName,
    compileProcess_agrees first second 0 (Environment.agrees_zero first second) code safe]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoContinuation
