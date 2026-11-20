import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitutionProgress

/-!
# Helper prefixes stay inside their phases or reach the exact public port

The phase palette is read from the actual helper left-hand sides. Every
non-leaving clause returns to that palette. The one leaving clause constructs
the public resume node with its value and external continuation. These facts
support composition with a surrounding program whose clauses cannot match
the helper's internal phases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution

open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration
open LiteralPaths

def helperPhases : List String := rules.filterMap (fun rule => symbolAt rule.lhs [1, 0])

def phaseOf (term : MClosed) : Option String :=
  symbolAt (Rigid.includeTerm (ProgramBinders.ground MSig) term) [1, 0]

def Internal (term : MClosed) : Prop := ∃ phase, phaseOf term = some phase ∧ phase ∈ helperPhases
def AtResume (term : MClosed) : Prop := ∃ value continuation, term = resumeC value continuation

theorem active_phase (phase : String) (arguments : List MClosed) :
    phaseOf (activeC phase arguments) = some phase := rfl

theorem shift_internal (amount cutoff : Nat) (term continuation : MClosed) :
    Internal (shiftC amount cutoff term continuation) :=
  ⟨"hd-shift", rfl, by decide +kernel⟩

theorem zero_internal (argument : MClosed) (depth : Nat) (body continuation : MClosed) :
    Internal (substituteZeroC argument depth body continuation) :=
  ⟨"hd-subst-zero", rfl, by decide +kernel⟩

theorem environment_internal (environment body continuation : MClosed) :
    Internal (substituteEnvironmentC environment body continuation) :=
  ⟨"hd-subst-env", rfl, by decide +kernel⟩

theorem helperPhases_exclude_resume : "hd-resume" ∉ helperPhases := by decide +kernel

theorem resume_not_internal (value continuation : MClosed) : ¬ Internal (resumeC value continuation) := by
  rintro ⟨phase, found, inside⟩
  have same : "hd-resume" = phase := Option.some.inj found
  subst phase
  exact helperPhases_exclude_resume inside

theorem continuing_phases_checked :
    (List.finRange rules.length).all (fun index =>
      if index.val = 3 then true else
        match symbolAt (rules.get index).rhs [1, 0] with
        | none => false
        | some phase => decide (phase ∈ helperPhases)) = true := by
  decide +kernel

theorem leaving_rule_answer (call result : MClosed) (answered : ProgramBinders.Answers leave call result) :
    AtResume result := by
  obtain ⟨environment, _, output⟩ := (RuleBuilder.answers_iff (n := 2) _ _ call result).mp answered
  refine ⟨environment 0, environment 1, ?_⟩
  simpa [Templates.act, resumeC, activeC] using output.symm

theorem step_result_scope {before after : MClosed} (step : Step before after) :
    Internal after ∨ AtResume after := by
  obtain ⟨index, answered⟩ := step
  by_cases leaving : index.val = 3
  · have same : index = (⟨3, by decide⟩ : Fin rules.length) := Fin.ext leaving
    subst index
    exact Or.inr (leaving_rule_answer before after answered)
  · obtain ⟨environment, _, result⟩ := answered
    have checked := List.all_eq_true.mp continuing_phases_checked index (by simp)
    change (if index.val = 3 then true else
      match symbolAt (rules.get index).rhs [1, 0] with
      | none => false
      | some phase => decide (phase ∈ helperPhases)) = true at checked
    rw [if_neg leaving] at checked
    cases found : symbolAt (rules.get index).rhs [1, 0] with
    | none =>
        rw [found] at checked
        cases checked
    | some phase =>
        rw [found] at checked
        have inside : phase ∈ helperPhases := of_decide_eq_true checked
        have named := symbolAt_instantiate ((rules.get index).assign environment (ProgramBinders.ground MSig)) found
        rw [result] at named
        exact Or.inl ⟨phase, named, inside⟩

theorem prefix_internal_or_resume {first current : MClosed} (initial : Internal first)
    (prefixRun : Runs first current) : Internal current ∨ AtResume current := by
  induction prefixRun with
  | refl => exact Or.inl initial
  | tail _ step _ => exact step_result_scope step

theorem shift_prefix (amount cutoff : Nat) (term continuation current : MClosed)
    (run : Runs (shiftC amount cutoff term continuation) current) :
    Internal current ∨ AtResume current :=
  prefix_internal_or_resume (shift_internal amount cutoff term continuation) run

theorem zero_prefix (argument : MClosed) (depth : Nat) (body continuation current : MClosed)
    (run : Runs (substituteZeroC argument depth body continuation) current) :
    Internal current ∨ AtResume current :=
  prefix_internal_or_resume (zero_internal argument depth body continuation) run

theorem environment_prefix (environment body continuation current : MClosed)
    (run : Runs (substituteEnvironmentC environment body continuation) current) :
    Internal current ∨ AtResume current :=
  prefix_internal_or_resume (environment_internal environment body continuation) run

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution
