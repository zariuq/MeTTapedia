import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauseResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateScheduleCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseWitnesses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldCompilerSteps

/-!
# Source bodies publish conditional templates and use them independently

The source world is independent of native allocation. A captured-template
clause publishes compatible and incompatible schemas beside ordinary and
shared outputs. A following resolved clause reads the compatible occurrence
twice with distinct private values. Selecting the incompatible occurrence
instead is rejected despite the same available physical resources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSourceControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalRealizations ContextualClauseWitnesses
open ContextualConditionalTemplateControls (base Operation literal pair pattern body conditions reading)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

abbrev queries := ContextualConditionalTemplateControls.locals
abbrev inners := ContextualConditionalTemplateControls.inners
abbrev rowLocals := ContextualConditionalTemplateControls.bank
abbrev captures := ContextualConditionalTemplateControls.captures
abbrev before := ContextualWorldComparison.nativeWorld rowLocals ContextualConditionalTemplateControls.before
abbrev rule := ContextualConditionalTemplateControls.sourceRule
abbrev picked := ContextualConditionalTemplateControls.chosen
abbrev result := ContextualConditionalTemplateState.resultFamily queries inners rowLocals before
abbrev information := ContextualConditionalTemplateState.information queries inners rowLocals before rule picked

def gamma : Term (signature base result) [] () := generator result (.inr (.inr ()))

theorem information_explicit : information = [(observe gamma, observe (literal (Γ := []) 0))] := by
  with_unfolding_all rfl

def model {V : Type} (next : V → MetaArity base) : Assignment result next
  | .inl (.inl impossible) => nomatch impossible
  | .inl (.inr (_, ())) => literal 0
  | .inr (.inl ⟨_, .inl impossible⟩) => nomatch impossible
  | .inr (.inl ⟨_, .inr (_, ())⟩) => literal 0
  | .inr (.inr ()) => literal 0

theorem models_information {V : Type} (next : V → MetaArity base) : ContextualResidual.Models (model next) information := by
  rw [information_explicit]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem source_admitted : ContextualConditionalTemplateState.Admitted queries inners rowLocals before rule picked := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Unit, captures, model captures, models_information captures⟩, ?_⟩
  intro check member
  cases member

abbrev after := ContextualConditionalTemplateState.target queries inners rowLocals before rule picked
abbrev privateRows := ContextualConditionalTemplateState.resultLocals queries inners rowLocals before

local instance (side : Bool) : DecidableEq
    (ContextualConditionalTemplateState.PrivateNames (Query := Empty) (Inner := Unit) rowLocals before side) := by
  let _ : DecidableEq (Empty ⊕ (Nat × Unit)) := inferInstance
  let _ : DecidableEq (Mettapedia.Logic.LP.ScopedVar (Empty ⊕ (Nat × Unit))) := inferInstance
  let _ : DecidableEq (Mettapedia.Logic.LP.ScopedVar (Empty ⊕ (Nat × Unit)) ⊕ Unit) := inferInstance
  cases side
  · change DecidableEq (Empty ⊕ (Nat × Unit))
    infer_instance
  · change DecidableEq ((Empty ⊕ (Nat × Unit)) ⊕
      ((Empty ⊕ (Nat × Unit)) ⊕ (Mettapedia.Logic.LP.ScopedVar (Empty ⊕ (Nat × Unit)) ⊕ Unit)))
    infer_instance

theorem actor_is_zero {V : Type} (next : V → MetaArity base) (candidate : Assignment result next)
    (modeled : ContextualResidual.Models candidate information) :
    Assignment.compose candidate (ContextualConditionalTemplateState.actorEnv queries inners rowLocals before) = reading next 0 := by
  have equation := modeled (observe gamma, observe (literal (Γ := []) 0)) (by rw [information_explicit]; exact List.mem_singleton_self _)
  change observe (instantiate candidate gamma) = observe (literal (declaration := next) (Γ := []) 0) at equation
  have value := observe_injective equation
  funext name
  cases name with
  | inl impossible => exact nomatch impossible
  | inr name =>
      cases name
      exact value

theorem good_row_matches {V : Type} (next : V → MetaArity base) (candidate : Assignment result next)
    (modeled : ContextualResidual.Models candidate information) (number : Nat) :
    Matches privateRows result candidate (pattern number number 0) (after.rows 10) := by
  have row := ContextualConditionalTemplateState.produced_at source_admitted ⟨0, by decide +kernel⟩
  change after.rows 10 = ContextualConditionalTemplateState.producedDescription queries inners rowLocals before rule picked
    0 ⟨.schema body, conditions 0⟩ at row
  rw [row]
  apply (ContextualConditionalTemplateState.schema_description_matches (queries := queries) (inners := inners)
    (locals := rowLocals) (before := before) (rule := rule) (picked := picked) 0 body (conditions 0)
    next candidate (pattern number number 0)).mpr
  rw [actor_is_zero next candidate modeled]
  exact ContextualConditionalTemplateControls.source_has_private_instance next number

theorem bad_row_never_matches {V : Type} (next : V → MetaArity base) (candidate : Assignment result next)
    (modeled : ContextualResidual.Models candidate information) (value : Term (signature base next) [] ()) :
    ¬ Matches privateRows result candidate value (after.rows 11) := by
  have row := ContextualConditionalTemplateState.produced_at source_admitted ⟨1, by decide +kernel⟩
  change after.rows 11 = ContextualConditionalTemplateState.producedDescription queries inners rowLocals before rule picked
    1 ⟨.schema body, conditions 1⟩ at row
  intro matched
  rw [row] at matched
  have source := (ContextualConditionalTemplateState.schema_description_matches (queries := queries) (inners := inners)
    (locals := rowLocals) (before := before) (rule := rule) (picked := picked) 1 body (conditions 1)
    next candidate value).mp matched
  rw [actor_is_zero next candidate modeled] at source
  exact ContextualConditionalTemplateControls.incompatible_source_row_has_no_instance next value source

def nextCode : RuleInstance (Term (signature base (queryFamily queries result)) [] ()) :=
  ⟨[], [pattern 0 0 0, pattern 1 1 0], [], [], [literal 99]⟩

def nextPlan : ContextualPublication.Plan (Term (signature base (queryFamily queries result)) [] ()) :=
  ⟨nextCode, [true], rfl⟩

def nextSelection : Selection Nat := ⟨[], [10, 10], [14]⟩
def badSelection : Selection Nat := ⟨[], [10, 11], [14]⟩

theorem next_source_admitted : ContextualClauseSourceState.Admitted queries privateRows after nextPlan nextSelection := by
  let candidate := model captures
  let requests : List (Term (signature base captures) [] () × Row privateRows result [] ()) :=
    [(pattern 0 0 0, after.rows 10), (pattern 1 1 0, after.rows 10)]
  have matched : ∀ request ∈ requests, Matches privateRows result candidate request.1 request.2 := by
    intro request member
    rcases List.mem_cons.mp member with rfl | member
    · exact good_row_matches captures candidate (models_information captures) 0
    · have only := List.mem_singleton.mp member
      subst request
      exact good_row_matches captures candidate (models_information captures) 1
  obtain ⟨extension, filler, realized⟩ := finite_realizations privateRows result candidate requests matched
  let witness : Witness queries privateRows result nextSelection nextCode after.rows after.equations rfl rfl extension.declarations := by
    refine ⟨(fun impossible => nomatch impossible), Assignment.compose extension.assignment candidate, filler,
      ContextualResidual.models_compose (models_information captures) extension.assignment,
      (by intro equation member; cases member), ?_, ?_⟩
    · intro port
      exact Fin.elim0 port
    · intro port
      fin_cases port
      · exact realized (pattern 0 0 0, after.rows 10) List.mem_cons_self
      · exact realized (pattern 1 1 0, after.rows 10) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · obtain ⟨images, modeled, _, _⟩ := witness.gives_model queries privateRows result
    exact ⟨extension.Names, extension.declarations, images, modeled⟩
  · intro check member
    cases member

theorem incompatible_next_source_is_refused :
    ¬ ContextualClauseSourceState.Admitted queries privateRows after nextPlan badSelection := by
  intro admitted
  obtain ⟨Future, future, images, modeled⟩ := admitted.solvable
  let witness := witness_of_model queries privateRows result badSelection nextCode after.rows after.equations rfl rfl images modeled
  exact bad_row_never_matches future witness.capture witness.previous _
    ((witness.read ⟨1, by decide +kernel⟩).matches privateRows result)

abbrev firstPart := ContextualConditionalTemplateSchedules.Schedule.template before
  (ContextualConditionalTemplateSchedules.Schedule.nil before) queries inners rule picked
abbrev goodBody := ContextualConditionalTemplateSchedules.Schedule.segment firstPart
  (ContextualSourceSchedules.Schedule.snoc (ContextualSourceSchedules.Schedule.nil after) queries nextPlan nextSelection)
abbrev badBody := ContextualConditionalTemplateSchedules.Schedule.segment firstPart
  (ContextualSourceSchedules.Schedule.snoc (ContextualSourceSchedules.Schedule.nil after) queries nextPlan badSelection)

theorem the_mixed_body_is_admitted : goodBody.Admitted := by
  exact ⟨⟨⟨Unit, captures, (fun _ => literal 0), (by intro equation member; cases member)⟩, source_admitted⟩,
    ⟨source_admitted.solvable, next_source_admitted⟩⟩

theorem the_mixed_body_compiles : goodBody.compile.Holds before.present :=
  goodBody.compile_exact.mpr the_mixed_body_is_admitted

theorem both_bodies_have_available_resources :
    goodBody.compile.resources.condition.Holds ContextualSourceSchedules.Schedule.unitLabel before.present ∧
      badBody.compile.resources.condition.Holds ContextualSourceSchedules.Schedule.unitLabel before.present := by
  decide +kernel

theorem the_incompatible_body_is_refused : ¬ badBody.compile.Holds before.present := by
  intro compiled
  exact incompatible_next_source_is_refused (badBody.compile_exact.mp compiled).2.2

theorem compiled_effect_keeps_the_dormant_row :
    fire before.present goodBody.compile.resources.effect = {10, 11, 12, 13, 14} := by
  exact (goodBody.compile_effect the_mixed_body_compiles).2

theorem actual_template_clause_has_the_source_world (occupied : Finset Nat) (fuel : Nat) :
    ∃ compiled : ContextualConditionalTemplateClauses.Compiled queries inners rowLocals before occupied rule picked,
      compiled.firing.fuel = fuel ∧
      ContextualWorldComparison.Equivalent after
        (ContextualConditionalTemplateState.actorEnv queries inners rowLocals before)
        (ContextualWorldComparison.nativeWorld (ContextualConditionalTemplateClauses.Compiled.resultLocals compiled)
          (ContextualConditionalTemplateClauses.Compiled.target compiled))
        (ContextualConditionalTemplateClauses.Compiled.actorValues compiled) :=
  (ContextualConditionalTemplateClauses.source_iff_compiled_at_fuel queries inners rowLocals before occupied rule picked fuel).mp source_admitted

abbrev FirstCompiled (occupied : Finset Nat) :=
  ContextualConditionalTemplateClauses.Compiled queries inners rowLocals before occupied rule picked

local instance {occupied : Finset Nat} (first : FirstCompiled occupied) : DecidableEq first.firing.update.Variables :=
  first.firing.update.equality

local instance {occupied : Finset Nat} (first : FirstCompiled occupied) (side : Bool) :
    DecidableEq (ContextualConditionalTemplateClauses.Compiled.PrivateNames first side) := by
  let _ : DecidableEq (Empty ⊕ (Nat × Unit)) := inferInstance
  let _ : DecidableEq ((Empty ⊕ (Nat × Unit)) ⊕ (Empty ⊕ (Nat × Unit))) := inferInstance
  cases side
  · change DecidableEq (Empty ⊕ (Nat × Unit))
    infer_instance
  · change DecidableEq (((Empty ⊕ (Nat × Unit)) ⊕ (Empty ⊕ (Nat × Unit))) ⊕ first.firing.update.Variables)
    infer_instance

def publicNextPlan : ContextualPublication.Plan
    (Term (signature base (queryFamily queries (ContextualTemplateSource.Actor queries captures))) [] ()) :=
  ⟨⟨[], [pattern 0 0 0, pattern 1 1 0], [], [], [literal 99]⟩, [true], rfl⟩

theorem actual_following_reuse {occupied : Finset Nat} (first : FirstCompiled occupied) (fuel : Nat) :
    ∃ second : ContextualConditionalClauses.Compiled queries
        (ContextualConditionalTemplateClauses.Compiled.resultLocals first)
        (before := ContextualConditionalTemplateClauses.Compiled.target first)
        (ContextualWorldComparison.preparedPlan queries
          (ContextualConditionalTemplateClauses.Compiled.actorValues first) publicNextPlan) nextSelection,
      second.firing.fuel = fuel ∧ second.firing.selection.read = [10, 10] ∧
        second.firing.target.present = {10, 11, 12, 13, 14} := by
  have equivalent := ContextualConditionalTemplateClauses.Compiled.source_world_equivalent first
  have admitted : ContextualClauseSourceState.Admitted queries privateRows after
      (ContextualWorldComparison.preparedPlan queries
        (ContextualConditionalTemplateState.actorEnv queries inners rowLocals before) publicNextPlan) nextSelection :=
    next_source_admitted
  obtain ⟨second, budget, _compared⟩ := equivalent.realize_step queries publicNextPlan nextSelection admitted fuel
  refine ⟨second, budget, ?_, ?_⟩
  · rw [second.selected]
    rfl
  · rw [second.physical_result, ContextualConditionalTemplateClauses.Compiled.physical_exact first]
    decide +kernel

theorem actual_following_incompatible_read_is_refused {occupied : Finset Nat}
    (first : FirstCompiled occupied) (fuel : Nat) :
    ¬ ∃ second : ContextualConditionalClauses.Compiled queries
        (ContextualConditionalTemplateClauses.Compiled.resultLocals first)
        (before := ContextualConditionalTemplateClauses.Compiled.target first)
        (ContextualWorldComparison.preparedPlan queries
          (ContextualConditionalTemplateClauses.Compiled.actorValues first) publicNextPlan) badSelection,
      second.firing.fuel = fuel := by
  rintro ⟨second, _budget⟩
  have equivalent := ContextualConditionalTemplateClauses.Compiled.source_world_equivalent first
  exact incompatible_next_source_is_refused
    ((ContextualWorldComparison.admitted_iff equivalent queries badSelection publicNextPlan.rule).mp second.source_admitted)

theorem two_source_linked_actual_firings (occupied : Finset Nat) (publicationFuel useFuel : Nat) :
    ∃ first : FirstCompiled occupied, first.firing.fuel = publicationFuel ∧
      ∃ second : ContextualConditionalClauses.Compiled queries
          (ContextualConditionalTemplateClauses.Compiled.resultLocals first)
          (before := ContextualConditionalTemplateClauses.Compiled.target first)
          (ContextualWorldComparison.preparedPlan queries
            (ContextualConditionalTemplateClauses.Compiled.actorValues first) publicNextPlan) nextSelection,
        second.firing.fuel = useFuel ∧ second.firing.selection.read = [10, 10] ∧
          second.firing.target.present = {10, 11, 12, 13, 14} := by
  obtain ⟨first, budget, _equivalent⟩ := actual_template_clause_has_the_source_world occupied publicationFuel
  obtain ⟨second, useBudget, reads, present⟩ := actual_following_reuse first useFuel
  exact ⟨first, budget, second, useBudget, reads, present⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSourceControls
