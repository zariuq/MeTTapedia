import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueWorkerInvariant
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowPhases

/-! # Literal phase exclusion for the compiled value worker -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage.Elaboration
open ValueContinuation LiteralPaths

abbrev Rule := ProgramBinders.Equation MSig [] ()

def continuationTags : List String :=
  ["hd-main-finish", "hd-main-value-succ", "hd-main-value-pair-first", "hd-main-value-pair-second"]

def stackTag : Stack → String
  | .base => "hd-main-finish"
  | .succ _ => "hd-main-value-succ"
  | .first _ _ => "hd-main-value-pair-first"
  | .second _ _ => "hd-main-value-pair-second"

theorem stackTag_member (stack : Stack) : stackTag stack ∈ continuationTags := by
  cases stack <;> simp [stackTag, continuationTags]

theorem resume_stack_symbol (datum : MClosed) (stack : Stack) :
    symbolAt (Rigid.includeTerm (ProgramBinders.ground MSig) (resumeC datum (code stack))) [1, 2, 0] =
      some (stackTag stack) := by
  cases stack <;> rfl

/-- A sufficient syntactic exclusion test, checked on the actual templates. -/
def avoidsWorker (rule : Rule) : Bool :=
  (symbolAt rule.lhs [1, 0]).any fun phase =>
    if phase = "hd-resume" then
      (symbolAt rule.lhs [1, 2, 0]).any fun tag => decide (tag ∉ continuationTags)
    else decide (phase ≠ "hd-value")

theorem traversal_avoids : ContextRules.traversal.all avoidsWorker = true := by decide +kernel
theorem primitive_avoids : ContextRules.primitive.all avoidsWorker = true := by decide +kernel
theorem driver_prefix_avoids : (ContextRules.driver.take 3).all avoidsWorker = true := by decide +kernel
theorem helpers_avoid : RuntimeSubstitution.rules.all avoidsWorker = true := by decide +kernel

theorem answer_symbol {rule : Rule} {call answer : MClosed} {path : List Nat} {symbol : String}
    (answered : ProgramBinders.Answers rule call answer) (found : symbolAt rule.lhs path = some symbol) :
    symbolAt (Rigid.includeTerm (ProgramBinders.ground MSig) call) path = some symbol := by
  obtain ⟨environment, matched, _⟩ := answered
  have named := symbolAt_instantiate (rule.assign environment (ProgramBinders.ground MSig)) found
  rw [matched] at named
  exact named

theorem avoiding_cannot_value {rule : Rule} (checked : avoidsWorker rule = true)
    (datum continuation answer : MClosed) :
    ¬ ProgramBinders.Answers rule (valueC datum continuation) answer := by
  intro answered
  obtain ⟨phase, found, passed⟩ := (Option.any_eq_true _ _).mp checked
  have actual := answer_symbol answered found
  change some "hd-value" = some phase at actual
  have same := (Option.some.inj actual).symm
  subst phase
  rw [if_neg (by decide : "hd-value" ≠ "hd-resume")] at passed
  exact Bool.false_ne_true passed

theorem avoiding_cannot_resume {rule : Rule} (checked : avoidsWorker rule = true)
    (datum answer : MClosed) (stack : Stack) :
    ¬ ProgramBinders.Answers rule (resumeC datum (code stack)) answer := by
  intro answered
  obtain ⟨phase, found, passed⟩ := (Option.any_eq_true _ _).mp checked
  have actual := answer_symbol answered found
  change some "hd-resume" = some phase at actual
  have same := (Option.some.inj actual).symm
  subst phase
  rw [if_pos rfl] at passed
  obtain ⟨tag, tagged, different⟩ := (Option.any_eq_true _ _).mp passed
  have actualTag := answer_symbol answered tagged
  rw [resume_stack_symbol] at actualTag
  have sameTag := (Option.some.inj actualTag).symm
  subst tag
  exact (of_decide_eq_true different) (stackTag_member stack)

theorem avoiding_cannot_invariant {rule : Rule} (checked : avoidsWorker rule = true)
    {original current answer : MClosed} (invariant : Invariant original current) :
    ¬ ProgramBinders.Answers rule current answer := by
  rcases invariant with checking | returning
  · obtain ⟨datum, stack, rfl, _, _⟩ := checking
    exact avoiding_cannot_value checked _ _ _
  · obtain ⟨datum, stack, _, rfl, _, _⟩ := returning
    exact avoiding_cannot_resume checked _ _ _

theorem root_avoids {rule : Rule} (phase : symbolAt rule.lhs [1, 0] = some "hd-root") :
    avoidsWorker rule = true := by
  rw [avoidsWorker, phase]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker
