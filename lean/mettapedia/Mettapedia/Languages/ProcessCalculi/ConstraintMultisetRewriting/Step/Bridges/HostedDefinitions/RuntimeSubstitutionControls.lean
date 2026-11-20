import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitutionProgress

/-!
# Scoped executions and adversarial controls for the source helper

The beta-substitution control retains a free variable beneath a lambda. A
caller continuation that resembles an internal frame remains opaque until the
public port. An added looping clause demonstrates why the helper's progress
theorems do not extend to arbitrary surrounding programs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration

theorem scoped_shift_runs {n : Nat} (amount : Nat) (term : Tower.Tm n) (continuation : MClosed) :
    Runs (shiftC amount 0 (encodeTm term) continuation)
      (resumeC (encodeTm (rename (NativeSyntax.weakenRen amount) term)) continuation) := by
  simpa only [quoteRaw_rawTm, quoteRaw_shift] using shift_runs amount 0 (rawTm term) continuation

theorem scoped_zero_runs {n : Nat} (argument : Tower.Tm n) (body : Tower.Tm (n + 1)) (continuation : MClosed) :
    Runs (substituteZeroC (encodeTm argument) 0 (encodeTm body) continuation)
      (resumeC (encodeTm (inst0 argument body)) continuation) := by
  simpa only [quoteRaw_rawTm, quoteRaw_substituteZero] using
    zero_runs (rawTm argument) 0 (rawTm body) continuation

theorem scoped_zero_reflects {n : Nat} (argument : Tower.Tm n) (body : Tower.Tm (n + 1))
    (continuation value after : MClosed)
    (run : Runs (substituteZeroC (encodeTm argument) 0 (encodeTm body) continuation) (resumeC value after)) :
    value = encodeTm (inst0 argument body) ∧ after = continuation :=
  resume_endpoints run (scoped_zero_runs argument body continuation)

theorem capture_avoiding_source_run (continuation : MClosed) :
    Runs (substituteZeroC (encodeTm (.var 0 : Tower.Tm 1)) 0
      (encodeTm (.lam (.var 1) : Tower.Tm 2)) continuation)
      (resumeC (encodeTm (.lam (.var 1) : Tower.Tm 1)) continuation) :=
  scoped_zero_runs (.var 0) (.lam (.var 1)) continuation

theorem captured_answer_impossible (continuation after : MClosed) :
    ¬ Runs (substituteZeroC (encodeTm (.var 0 : Tower.Tm 1)) 0
      (encodeTm (.lam (.var 1) : Tower.Tm 2)) continuation)
      (resumeC (encodeTm (.lam (.var 0) : Tower.Tm 1)) after) := by
  intro run
  have wrong := (resume_endpoints run (capture_avoiding_source_run continuation)).1
  exact capture_sensitive_terms_distinct wrong

def misleadingContinuation : MClosed := bottom (csym "caller-continuation")

theorem caller_payload_stops_at_boundary :
    Runs (shiftC 0 0 (quoteRaw (.var 0)) misleadingContinuation)
      (resumeC (quoteRaw (.var 0)) misleadingContinuation) ∧
      ¬ ∃ next, Step (resumeC (quoteRaw (.var 0)) misleadingContinuation) next := by
  exact ⟨shift_runs 0 0 (.var 0) misleadingContinuation, no_resume_step _ _⟩

def uncovered : Equation := RuleBuilder.equation (n := 1)
  (RuleBuilder.literal (csym "uncovered-call")) (RuleBuilder.slot 0)

theorem uncovered_rule_has_two_answers :
    ProgramBinders.Answers uncovered (csym "uncovered-call") (csym "one") ∧
      ProgramBinders.Answers uncovered (csym "uncovered-call") (csym "two") ∧
      csym "one" ≠ csym "two" := by
  have first := RuleBuilder.instantiated_answer (n := 1)
    (RuleBuilder.literal (csym "uncovered-call")) (RuleBuilder.slot 0) (fun _ => csym "one")
  have second := RuleBuilder.instantiated_answer (n := 1)
    (RuleBuilder.literal (csym "uncovered-call")) (RuleBuilder.slot 0) (fun _ => csym "two")
  exact ⟨by simpa [uncovered] using first, by simpa [uncovered] using second, by decide⟩

theorem uncovered_rule_not_certified :
    LiteralPaths.pathsChecked (RuleBuilder.literal (n := 1) (csym "uncovered-call")) = false := by
  decide +kernel

def spinningStart : MClosed := shiftC 0 0 (quoteRaw (.var 0)) (csym "stop")
def foreignLoop : Equation := RuleBuilder.equation (n := 0)
  (RuleBuilder.literal spinningStart) (RuleBuilder.literal spinningStart)
def extendedRules : List Equation := rules ++ [foreignLoop]

theorem extension_has_self_step : ProgramBinders.Rewrites extendedRules.get spinningStart spinningStart := by
  have member : foreignLoop ∈ extendedRules := by simp [extendedRules]
  obtain ⟨index, indexed⟩ := List.mem_iff_get.mp member
  refine ⟨index, ?_⟩
  rw [indexed]
  have applied := RuleBuilder.instantiated_answer (n := 0)
    (RuleBuilder.literal spinningStart) (RuleBuilder.literal spinningStart) Fin.elim0
  simpa [foreignLoop] using applied

theorem an_arbitrary_extension_can_spin :
    ∃ sequence : Nat → MClosed, sequence 0 = spinningStart ∧
      ∀ index, ProgramBinders.Rewrites extendedRules.get (sequence index) (sequence (index + 1)) :=
  ⟨fun _ => spinningStart, rfl, fun _ => extension_has_self_step⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution
