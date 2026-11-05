import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPublicationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequencingControls

/-!
# Compiled private bodies retain schema origins and reject conflicting reads

The first body publishes an open schema before fixing its caller variable.
The second computes a lookup key through a stored function, consumes a token,
and reuses its conditional answer twice. A conflicting second read is refused
by the compiled plan, despite having the same physical footprint.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualSourceSchedules ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

namespace EarlierSchema

open ContextualPrefixPublicationControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

def body : Schedule base Nat [] () initial afterSecond :=
  .snoc (.snoc (.nil initial) none firstPlan firstSelection) none secondPlan secondSelection

theorem admitted : body.Admitted := by
  have consistent := (Schedule.snoc (Schedule.nil initial) none firstPlan firstSelection).source_solvable first_admitted.solvable
  exact ⟨⟨consistent, first_admitted⟩, second_admitted⟩

theorem compiled_accepts : body.compile.Holds initial.present := body.compile_exact.mpr admitted

theorem compiled_effect : fire initial.present body.compile.resources.effect = {0} := by
  exact (body.compile_effect compiled_accepts).2.trans (by decide +kernel)

def savedBirth : Birth afterSecond.declarations Nat [] () :=
  body.compile.births[0]'(by decide +kernel)

/-- The saved schema can still choose 2, even though the terminal caller is fixed to 1. -/
theorem the_compiled_origin_still_accepts_two :
    ∃ candidate : Assignment savedBirth.saved none,
      ContextualResidual.Models candidate savedBirth.problem ∧
      instantiate candidate savedBirth.value = box (symbol 2) := by
  refine ⟨firstModel none 2, ?_, rfl⟩
  change ContextualResidual.Models (firstModel none 2) []
  intro equation member
  cases member

theorem the_compiled_terminal_information_keeps_one {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment afterSecond.declarations decl)
    (model : ContextualResidual.Models candidate body.compile.problem) :
    instantiate candidate secondX = symbol 1 := by
  apply the_callers_variable_is_one decl candidate
  rw [body.final_equations]
  exact model

theorem the_origin_remains_reusable : savedBirth.reusable = true := rfl
theorem original_cuts_are_counted : body.compile.cuts.length = 2 := by decide +kernel

def guardedCode : RuleInstance (Term (signature base actor) [] ()) :=
  { firstCode with checks := [.equal callerX (symbol 1)] }
def guardedPlan : ContextualPublication.Plan (Term (signature base actor) [] ()) := ⟨guardedCode, [true], rfl⟩
abbrev guardedFirst := ContextualClauseSourceState.target none none initial guardedPlan firstSelection
abbrev guardedResult := ContextualClauseSourceState.target none firstLocals guardedFirst secondPlan secondSelection

def guardedBody : Schedule base Nat [] () initial guardedResult :=
  .snoc (.snoc (.nil initial) none guardedPlan firstSelection) none secondPlan secondSelection

theorem a_later_binding_does_not_repair_the_compiled_earlier_check :
    ¬ guardedBody.compile.Holds initial.present := by
  intro accepted
  have admitted := guardedBody.compile_exact.mp accepted
  have asked := admitted.1.2.checks (.equal callerX (symbol 1)) (List.mem_singleton_self _)
  have same := asked Empty none (firstModel none 2) (by
    change ContextualResidual.Models (firstModel none 2) []
    intro equation member
    cases member)
  change symbol (decl := none) 2 = symbol 1 at same
  have impossible : (2 : Nat) = 1 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj same).1)
  omega

/-- Its final equations and resource precondition are both consistent; the earlier cut refuses it. -/
theorem the_guard_refusal_is_not_a_terminal_conflict :
    guardedBody.compile.resources.condition.Holds Schedule.unitLabel initial.present ∧
      ContextualConditionalExecution.Solvable guardedBody.compile.problem := by
  refine ⟨compiled_accepts.2.1, ?_⟩
  change ContextualConditionalExecution.Solvable
    (ContextualResidual.mapProblem guardedBody.frame.assignment initial.equations ++ guardedBody.deltas)
  rw [← guardedBody.final_equations]
  exact second_admitted.solvable

end EarlierSchema

namespace ComputedBody

open ContextualClausePublication.BinderControls (DataOperator dataSignature base locals captures queries)
open ContextualComputedJoinControls (world plan picked source_admitted)
open ContextualClauseSequencingControls (afterFirst rowLocals nextPlan selection source_next_admitted)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) result)
  infer_instance
local instance : DecidableEq world.Names := world.equality

abbrev result := ContextualClauseSourceState.target captures rowLocals afterFirst nextPlan selection

def body : Schedule base Nat [] () world result :=
  .snoc (.snoc (.nil world) queries plan picked) captures nextPlan selection

theorem admitted : body.Admitted := by
  have consistent := (Schedule.snoc (Schedule.nil world) queries plan picked).source_solvable source_admitted.solvable
  exact ⟨⟨consistent, source_admitted⟩, source_next_admitted⟩

theorem compiled_accepts : body.compile.Holds world.present := body.compile_exact.mpr admitted

theorem compiled_effect : fire world.present body.compile.resources.effect = {0, 1, 2, 4, 5} := by
  exact (body.compile_effect compiled_accepts).2.trans (by decide +kernel)

abbrev conflictingResult := ContextualClauseSourceState.target captures rowLocals afterFirst
  ContextualClauseSequencingControls.conflictingPlan selection

def conflictingBody : Schedule base Nat [] () world conflictingResult :=
  .snoc (.snoc (.nil world) queries plan picked) captures ContextualClauseSequencingControls.conflictingPlan selection

theorem the_conflicting_body_is_refused : ¬ conflictingBody.compile.Holds world.present := by
  intro accepted
  have admitted := conflictingBody.compile_exact.mp accepted
  exact ContextualClauseSequencingControls.a_conflicting_second_read_cannot_fire admitted.2

/-- The refusal is about information, rather than an invented resource conflict. -/
theorem the_conflicting_body_has_the_same_resources :
    conflictingBody.compile.resources = body.compile.resources := rfl

end ComputedBody

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleControls
