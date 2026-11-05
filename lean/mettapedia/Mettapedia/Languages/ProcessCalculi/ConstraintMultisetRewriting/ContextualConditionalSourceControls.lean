import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecutionControls

/-!
# A source clause consumes another source clause's pending answer

The first clause publishes x with x = 1 still pending. The second clause
opens that row, binds its own query variable and produces (1, 7). Both are
actual zero-fuel compiler firings. A source take of 2 has no compiled result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses.SourceControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualClauseFrames ContextualConditionalRows ContextualGuardMatching
open ContextualConditionalSourceProblem ContextualConditionalSourceAdmission
open ContextualConditionalExecution.Controls (base locals queries captures constantAt)
open SchematicReach.Controls (symbol pair)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := by
  change DecidableEq (SchematicReach.Controls.DataOperator ⊕ Operator (SchematicReach.spaceDeclaration
    SchematicReach.Controls.dataSignature () (Name := Nat)) sort)
  infer_instance

abbrev initial := ContextualConditionalExecution.Controls.before
abbrev actor := queryFamily queries captures
def firstRule : RuleInstance (SchematicReach.Closed actor) := ⟨[], [], [], [], [generator actor (.inr 0)]⟩
def firstPlan : ContextualPublication.Plan (SchematicReach.Closed actor) := ⟨firstRule, [true], rfl⟩
def firstSelection : Selection Nat := ⟨[], [], [1]⟩
def firstProblem := problem queries locals captures firstSelection firstRule initial.rows initial.equations
def firstModel : Assignment (family queries locals captures) captures :=
  fun name => constantAt captures 1 (family queries locals captures name)

theorem first_source_admitted : Admitted queries locals captures firstSelection firstRule initial.rows initial.equations initial.present := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, firstModel, ?_⟩, ?_⟩
  · intro equation member
    change equation ∈ [_] at member
    have only := List.mem_singleton.mp member
    subst equation
    rfl
  · intro check member
    cases member

abbrev firstPrepared := prepareState queries locals initial
local instance : DecidableEq firstPrepared.Names := firstPrepared.equality
def firstOutputs := outputs queries locals captures ∅ firstSelection firstRule initial.rows
def firstInformation := ContextualConditionalExecution.information (bank queries locals) captures ∅ firstSelection
  (ContextualClauseProblem.nativeRule queries locals captures firstRule) firstPrepared.rows firstPrepared.equations
def firstUpdate := ContextualFrameWorklist.identity firstInformation
def firstFiring : ContextualConditionalExecution.Firing (bank queries locals) firstPrepared :=
  ⟨ContextualClauseProblem.nativeRule queries locals captures firstRule, firstSelection, firstOutputs,
    (fun _ => true), (admitted_iff queries locals initial firstSelection firstRule).mp first_source_admitted,
    0, firstUpdate, rfl⟩
def first : Compiled queries locals (before := initial) firstPlan firstSelection := ⟨firstFiring, rfl, rfl, rfl, rfl⟩

theorem the_source_producer_really_leaves_work_pending :
    first.firing.fuel = 0 ∧ first.firing.update.remaining.length = 1 ∧ first.firing.target.present = {1} := ⟨rfl, rfl, rfl⟩

abbrev nextLocals := ContextualPublication.privateFamily (bank queries locals) first.firing.update.declaration
abbrev nextCaptures := first.firing.target.declarations
abbrev nextActor := queryFamily queries nextCaptures
abbrev nextFamily := family queries nextLocals nextCaptures
local instance : DecidableEq first.firing.update.Variables := first.firing.update.equality
local instance : DecidableEq first.firing.target.Names := first.firing.target.equality

def secondRule : RuleInstance (SchematicReach.Closed nextActor) :=
  ⟨[generator nextActor (.inl 0)], [], [], [], [pair (generator nextActor (.inl 0)) (symbol 7)]⟩
def secondPlan : ContextualPublication.Plan (SchematicReach.Closed nextActor) := ⟨secondRule, [true], rfl⟩
def secondSelection : Selection Nat := ⟨[1], [], [2]⟩
def secondProblem := problem queries nextLocals nextCaptures secondSelection secondRule
  first.firing.target.rows first.firing.target.equations
def secondModel : Assignment nextFamily captures := fun name => constantAt captures 1 (nextFamily name)

theorem second_source_model {Next : Type} (next : Next → MetaArity base) :
    ContextualResidual.Models (fun name => constantAt next 1 (nextFamily name)) secondProblem := by
  intro equation member
  change equation ∈ [_, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem second_source_admitted : Admitted queries nextLocals nextCaptures secondSelection secondRule
    first.firing.target.rows first.firing.target.equations first.firing.target.present := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, secondModel, second_source_model captures⟩, ?_⟩
  intro check member
  cases member

abbrev secondPrepared := prepareState queries nextLocals first.firing.target
local instance : DecidableEq secondPrepared.Names := secondPrepared.equality
def secondOutputs := outputs queries nextLocals nextCaptures first.firing.target.occupied secondSelection secondRule first.firing.target.rows
def secondInformation := ContextualConditionalExecution.information (bank queries nextLocals) nextCaptures
  first.firing.target.occupied secondSelection (ContextualClauseProblem.nativeRule queries nextLocals nextCaptures secondRule)
  secondPrepared.rows secondPrepared.equations
def secondFiring : ContextualConditionalExecution.Firing (bank queries nextLocals) secondPrepared :=
  ⟨ContextualClauseProblem.nativeRule queries nextLocals nextCaptures secondRule, secondSelection, secondOutputs,
    (fun _ => true), (admitted_iff queries nextLocals first.firing.target secondSelection secondRule).mp second_source_admitted,
    0, ContextualFrameWorklist.identity secondInformation, rfl⟩
def second : Compiled queries nextLocals (before := first.firing.target) secondPlan secondSelection :=
  ⟨secondFiring, rfl, rfl, rfl, rfl⟩

theorem two_source_clauses_compose_through_a_pending_row :
    first.firing.fuel = 0 ∧ second.firing.fuel = 0 ∧ second.firing.target.present = {2} ∧
      second.firing.update.remaining.length = 3 := ⟨rfl, rfl, rfl, rfl⟩

theorem the_second_source_clause_publishes_one_and_seven
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment second.firing.target.declarations next) :
    Matches (ContextualPublication.privateFamily (bank queries nextLocals) second.firing.update.declaration)
      second.firing.target.declarations candidate (pair (symbol 1) (symbol 7)) (second.firing.target.rows 2) := by
  apply (second.ordinary_body_instances ⟨0, by decide +kernel⟩ rfl next candidate (pair (symbol 1) (symbol 7))).mpr
  refine ⟨Extension.identity next, (fun name => constantAt next 1 (nextFamily name)), second_source_model next, ?_⟩
  rfl

theorem the_first_source_answer_refuses_two
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment first.firing.target.declarations next) :
    ¬ Matches nextLocals nextCaptures candidate (symbol 2) (first.firing.target.rows 1) := by
  intro matched
  obtain ⟨extension, images, model, same⟩ :=
    (first.ordinary_body_instances ⟨0, by decide +kernel⟩ rfl next candidate (symbol 2)).mp matched
  have equation := model _ (List.mem_singleton_self _)
  change observe (instantiate images (generator (family queries locals captures) (.inr (.inr 0)))) =
    observe (instantiate images (symbol 1)) at equation
  have required := observe_injective equation
  change instantiate images (generator (family queries locals captures) (.inr (.inr 0))) =
    instantiate extension.assignment (symbol 2) at same
  change instantiate images (generator (family queries locals captures) (.inr (.inr 0))) =
    instantiate images (symbol 1) at required
  erw [instantiate_generator] at required same
  have impossible : (1 : Nat) = 2 := SchematicReach.Controls.symbol_injective (required.symm.trans same)
  omega

def wrongRule : RuleInstance (SchematicReach.Closed nextActor) := ⟨[symbol 2], [], [], [], [symbol 7]⟩

theorem the_source_consumer_cannot_ignore_the_producers_condition :
    ¬ Admitted queries nextLocals nextCaptures secondSelection wrongRule
      first.firing.target.rows first.firing.target.equations first.firing.target.present := by
  intro source
  have native := (admitted_iff queries nextLocals first.firing.target secondSelection wrongRule).mp source
  obtain ⟨Future, future, candidate, model⟩ := native.solvable
  have matched := ContextualConditionalExecution.take_matches (bank queries nextLocals) native candidate model ⟨0, by decide +kernel⟩
  change Matches (bank queries nextLocals) nextCaptures _ (symbol 2)
    (ContextualConditionalPublication.extendPrivate nextLocals queries nextCaptures (first.firing.target.rows 1)) at matched
  exact the_first_source_answer_refuses_two future _
    ((ContextualConditionalPublication.extendPrivate_matches_iff nextLocals queries nextCaptures _ _ (symbol 2)).mp matched)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses.SourceControls
