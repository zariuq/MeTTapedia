import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseAdmission

/-!
# Source query bindings construct actual body publication

A resolved clause supplies all take/read patterns, body equations, guards,
output terms and storage intents. The compiler embeds its query variables
into a fresh actor scope, opens stored rows per port, and constructs the
existing checked publication owner. Reusable body values have exactly the
instances of the original source problem, including its caller bindings.

This is a uniform compiler for resolved clauses. Reducing arbitrary active
expressions, textual scope resolution and compound-source collection retain
their separate source contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClausePublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConjunctiveQueries
open ContextualClauseFrames ContextualClauseProblem ContextualClauseAdmission
open ContextualScopeSupport ContextualWorldScopeLedger

variable {S : Signature} {V Next : Type} {source : V → MetaArity S}

/-- Extending declarations changes no original source instances. The reverse
direction supplies formal generators for unused native declarations. -/
theorem source_instances_extension (extension : Extension source)
    {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort))
    (value : Term (signature S source) Γ sort) (next : Next → MetaArity S)
    (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances
      (ContextualResidual.observeProblem (ContextualFrameUnifier.mapProblem extension.assignment problem))
      (instantiate extension.assignment value) next pattern ↔
    ContextualPublication.SourceInstances (ContextualResidual.observeProblem problem) value next pattern := by
  constructor
  · rintro ⟨later, candidate, model, same⟩
    refine ⟨later, Assignment.compose candidate extension.assignment, ?_, ?_⟩
    · apply (ContextualResidual.models_observeProblem _ _).mpr
      exact (ContextualFrameUnifier.models_mapProblem _ _ _).mp
        ((ContextualResidual.models_observeProblem _ _).mp model)
    · exact (Assignment.instantiate_compose candidate extension.assignment value).trans same
  · rintro ⟨later, candidate, model, same⟩
    let added := Extension.withLocals extension.complementDeclarations later.declarations
    refine ⟨later.trans added, extension.liftModel candidate, ?_, ?_⟩
    · apply (ContextualResidual.models_observeProblem _ _).mpr
      exact (extension.models_liftModel_iff candidate problem).mpr
        ((ContextualResidual.models_observeProblem _ _).mp model)
    · erw [Extension.trans_assignment, ← Assignment.instantiate_compose, extension.liftModel_square,
        Assignment.instantiate_compose]
      have mapped := congrArg (instantiate added.assignment) same
      exact mapped.trans (Assignment.instantiate_compose added.assignment later.assignment pattern).symm

variable {Query Local Shared O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {Γ : Ctx S} {sort : S.Srt}

def compiledPlan (plan : ContextualPublication.Plan
    (Term (signature S (queryFamily queries captures)) Γ sort)) :
    ContextualPublication.Plan (Term (signature S (nativeRaw queries locals captures)) Γ sort) where
  rule := nativeRule queries locals captures plan.rule
  reusable := plan.reusable
  shape := by simpa only [nativeRule, RuleInstance.map, List.length_map] using plan.shape

theorem rule_covered (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (covered : RuleCovered (privateScopes scopes) occupied code) :
    RuleCovered (privateScopes scopes) occupied (nativeRule queries locals captures code) := by
  intro value member
  rw [nativeRule, ruleTerms_map] at member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  apply covered_instantiate_of_respects (privateScopes scopes) (privateScopes scopes) occupied
    (actor queries locals captures) _ (covered original present)
  intro name
  cases name with
  | inl name =>
      change term (privateScopes scopes) (generator (nativeRaw queries locals captures) (.inl (.inr name))) ⊆ ∅
      rw [term_generator]
      exact Finset.Subset.refl _
  | inr name =>
      change term (privateScopes scopes) (generator (nativeRaw queries locals captures) (.inr name)) ⊆ scopes name
      rw [term_generator]
      exact Finset.Subset.refl _

theorem problem_pattern (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (patterned : ContextualPatternFragment.ProblemPattern
      (ContextualResidual.observeProblem (problem queries locals captures selection code rows before))) :
    ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem (bank queries locals) captures occupied selection
        (nativeRule queries locals captures code) (nativeRows queries locals captures rows) before)) := by
  rw [actual_problem, ContextualResidual.observeProblem_mapProblem]
  apply ContextualPatternFragment.map_patterns _ _ _ patterned
  intro name
  rcases name with name | name | name
  · exact ContextualPatternFragment.generator_pattern (S := S)
      (declaration := nativeActive queries locals captures)
      (.inl ⟨ContextualActivationScopes.start occupied, .inr name⟩)
  · exact ContextualPatternFragment.generator_pattern (S := S)
      (declaration := nativeActive queries locals captures)
      (.inl ⟨occupied.sup id + name.scope, .inl name.name⟩)
  · exact ContextualPatternFragment.generator_pattern (S := S)
      (declaration := nativeActive queries locals captures) (.inr name)

theorem output_at_port [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (distinct : selection.made.Nodup) (shape : selection.made.length = code.produce.length)
    (port : Fin selection.made.length) :
    outputs queries locals captures occupied selection code rows (selection.made.get port) =
      instantiate (frame queries locals captures occupied).assignment
        (queryView queries locals captures (code.produce.get ⟨port.val, shape ▸ port.isLt⟩)) := by
  let values := (ContextualActivatedStep.prepared (bank queries locals) captures occupied selection
    (nativeRule queries locals captures code) (nativeRows queries locals captures rows)).rule.produce
  have length : selection.made.length = values.length := by
    simpa only [values, ContextualActivatedStep.prepared, ContextualSelectionViews.prepare, nativeRule,
      ContextualFreshening.ruleAt, RuleInstance.map, List.length_map] using shape
  have atPort := ContextualTemplateSource.assign_get selection.made values distinct length port
  change (ContextualTemplateSource.assign selection.made values (selection.made.get port)).getD _ = _
  rw [atPort]
  have mapped : values = (code.produce.map (queryView queries locals captures)).map
      (instantiate (frame queries locals captures occupied).assignment) :=
    congrArg (fun prepared => prepared.produce) (prepared_rule queries locals captures occupied selection code rows)
  exact (List.getElem_of_eq mapped (i := port.val) (length ▸ port.isLt)).trans (by
    simp only [List.get_eq_getElem, List.getElem_map])

section Execution

variable [DecidableEq Query] [DecidableEq Local] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {before : ContextualExecution.Endpoint locals O Γ sort}

structure Compiled (plan : ContextualPublication.Plan
    (Term (signature S (queryFamily queries before.declarations)) Γ sort)) (selection : Selection O) where
  firing : ContextualPublication.Firing (before := prepareEndpoint queries locals before)
  authored : firing.rule = nativeRule queries locals before.declarations plan.rule
  selected : firing.selection = selection
  values : firing.outputs = outputs queries locals before.declarations before.occupied selection plan.rule before.inventory.rows
  intents : selection.made.map firing.reusable = plan.reusable

/-- A source-admitted clause constructs actual solver execution and body
publication. Source predicates and returned body bindings are both retained. -/
theorem realize (plan : ContextualPublication.Plan
    (Term (signature S (queryFamily queries before.declarations)) Γ sort)) (selection : Selection O)
    (covered : RuleCovered (privateScopes before.scopes) before.occupied plan.rule)
    (source : Admitted queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (problem queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration))) :
    Nonempty (Compiled queries locals plan selection) := by
  let _ := before.equality
  obtain ⟨firing, authored, selected, values, intents⟩ := ContextualPublication.realize_planned_publication
    (bank queries locals) (prepareEndpoint queries locals before)
    (compiledPlan queries locals before.declarations plan) selection
    (outputs queries locals before.declarations before.occupied selection plan.rule before.inventory.rows)
    (rule_covered queries locals before.declarations before.scopes before.occupied plan.rule covered)
    ((admitted_iff queries locals before.declarations before.occupied selection plan.rule before.inventory.rows
      before.inventory.configuration).mp source)
    (problem_pattern queries locals before.declarations before.occupied selection plan.rule before.inventory.rows
      before.inventory.configuration patterned)
  exact ⟨⟨firing, authored, selected, values, intents⟩⟩

namespace Compiled

variable {queries locals} {plan : ContextualPublication.Plan
    (Term (signature S (queryFamily queries before.declarations)) Γ sort)} {selection : Selection O}

theorem source_admitted (compiled : Compiled queries locals plan selection) :
    Admitted queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration := by
  have actual := compiled.firing.execution.semantic_admission
  change ContextualGuardedStep.Valid (bank queries locals) before.declarations before.occupied
    compiled.firing.selection compiled.firing.rule (nativeRows queries locals before.declarations before.inventory.rows)
    before.inventory.configuration compiled.firing.outputs at actual
  rw [compiled.authored, compiled.selected, compiled.values] at actual
  exact (admitted_iff queries locals before.declarations before.occupied selection plan.rule before.inventory.rows
    before.inventory.configuration).mpr actual

theorem native_problem (compiled : Compiled queries locals plan selection) :
    ContextualActivatedStep.problem (bank queries locals) before.declarations before.occupied
      compiled.firing.selection compiled.firing.rule (nativeRows queries locals before.declarations before.inventory.rows)
      before.inventory.configuration =
    ContextualFrameUnifier.mapProblem (frame queries locals before.declarations before.occupied).assignment
      (problem queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration) := by
  rw [compiled.authored, compiled.selected]
  exact actual_problem queries locals before.declarations before.occupied selection plan.rule before.inventory.rows
    before.inventory.configuration

/-- The actually computed substitution is itself an original source model,
so a source-determined body result can be checked against the real output. -/
theorem solved_source_model (compiled : Compiled queries locals plan selection) :
    ContextualFrameUnifier.Models (Assignment.compose compiled.firing.update.answer
      (frame queries locals before.declarations before.occupied).assignment)
      (problem queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration) := by
  have actual := (ContextualResidual.models_observeProblem compiled.firing.update.answer _).mp
    (compiled.firing.update.completed compiled.firing.execution.empty)
  have sourceModel := (congrArg (fun equations => ContextualFrameUnifier.Models compiled.firing.update.answer equations)
    compiled.native_problem).mp actual
  exact (ContextualFrameUnifier.models_mapProblem _ _ _).mp sourceModel

def resultFrame (compiled : Compiled queries locals plan selection) :
    Extension (nativeActive queries locals before.declarations) where
  Names := compiled.firing.target.Names
  declarations := compiled.firing.target.declarations
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

theorem resultFrame_assignment (compiled : Compiled queries locals plan selection) :
    compiled.resultFrame.assignment = ContextualComputedFreshFrame.includeSource compiled.firing.update := by
  funext name
  exact (ContextualFreshFrameScopeLedger.includeSource_image compiled.firing.update name).symm

/-- Source identities remain distinct in the actual returned endpoint,
even when the solver changes declaration families and introduces helpers. -/
def sourceFrame (compiled : Compiled queries locals plan selection) :
    Extension (family queries locals before.declarations) :=
  (frame queries locals before.declarations before.occupied).trans compiled.resultFrame

theorem sourceFrame_assignment (compiled : Compiled queries locals plan selection) :
    compiled.sourceFrame.assignment = Assignment.compose
      (ContextualComputedFreshFrame.includeSource compiled.firing.update)
      (frame queries locals before.declarations before.occupied).assignment := by
  exact ((frame queries locals before.declarations before.occupied).trans_assignment compiled.resultFrame).trans
    (congrArg (fun assignment => Assignment.compose assignment
      (frame queries locals before.declarations before.occupied).assignment) compiled.resultFrame_assignment)

def continuationEnv (compiled : Compiled queries locals plan selection) :
    Assignment (queryFamily queries before.declarations) compiled.firing.target.declarations :=
  Assignment.compose compiled.sourceFrame.assignment (queryEmbedding queries locals before.declarations)

theorem result_equations (compiled : Compiled queries locals plan selection) :
    compiled.firing.target.inventory.configuration.equations =
      ContextualFrameUnifier.mapProblem compiled.sourceFrame.assignment
        (problem queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration) := by
  have actual := compiled.firing.native_equations
  change compiled.firing.target.inventory.configuration.equations =
    ContextualFrameUnifier.mapProblem (ContextualComputedFreshFrame.includeSource compiled.firing.update)
      (ContextualActivatedStep.problem (bank queries locals) before.declarations before.occupied compiled.firing.selection
        compiled.firing.rule (nativeRows queries locals before.declarations before.inventory.rows)
        before.inventory.configuration) at actual
  exact actual.trans ((congrArg (ContextualFrameUnifier.mapProblem
    (ContextualComputedFreshFrame.includeSource compiled.firing.update)) compiled.native_problem).trans
      ((ContextualComputedFreshFrame.map_compose _ _ _).trans
        (congrArg (fun assignment => ContextualFrameUnifier.mapProblem assignment
          (problem queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration))
          compiled.sourceFrame_assignment.symm)))

/-- A following body can use the actual returned query environment without
depending on the solver's helper representation or losing source bindings. -/
theorem continuation_instances (compiled : Compiled queries locals plan selection)
    (value : Term (signature S (queryFamily queries before.declarations)) Γ sort)
    {Next : Type} (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (ContextualResidual.observeProblem compiled.firing.target.inventory.configuration.equations)
      (instantiate compiled.continuationEnv value) next pattern ↔
    ContextualPublication.SourceInstances (ContextualResidual.observeProblem
      (problem queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration))
      (queryView queries locals before.declarations value) next pattern := by
  rw [compiled.result_equations]
  change ContextualPublication.SourceInstances _
    (instantiate (Assignment.compose compiled.sourceFrame.assignment (queryEmbedding queries locals before.declarations)) value)
    next pattern ↔ _
  rw [Assignment.instantiate_compose]
  exact source_instances_extension compiled.sourceFrame _ _ next pattern

theorem ordinary_body_instances (compiled : Compiled queries locals plan selection)
    (port : Fin selection.made.length) (reusable : compiled.firing.reusable (selection.made.get port) = true)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    ContextualGuardMatching.Matches
      (ContextualPublication.privateFamily (bank queries locals) compiled.firing.update.declaration)
      candidate pattern (compiled.firing.target.inventory.rows (selection.made.get port)) ↔
    ContextualPublication.SourceInstances (ContextualResidual.observeProblem
      (problem queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration))
      (queryView queries locals before.declarations
        (plan.rule.produce.get ⟨port.val, compiled.source_admitted.output_shape ▸ port.isLt⟩)) next pattern := by
  have made : selection.made.get port ∈ compiled.firing.selection.made := by
    rw [compiled.selected]
    exact List.get_mem _ _
  have actual := compiled.firing.ordinary_matches_source made reusable next candidate pattern
  apply actual.trans
  rw [compiled.authored, compiled.selected, compiled.values]
  rw [output_at_port queries locals before.declarations before.occupied selection plan.rule before.inventory.rows
    compiled.source_admitted.output_distinct compiled.source_admitted.output_shape port]
  change ContextualPublication.SourceInstances (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem (bank queries locals) before.declarations before.occupied selection
      (nativeRule queries locals before.declarations plan.rule)
      (nativeRows queries locals before.declarations before.inventory.rows) before.inventory.configuration)) _ next pattern ↔ _
  rw [actual_problem]
  exact source_instances_extension (frame queries locals before.declarations before.occupied) _ _ next pattern

theorem shared_body_value (compiled : Compiled queries locals plan selection)
    (port : Fin selection.made.length) (live : compiled.firing.reusable (selection.made.get port) = false) :
    compiled.firing.target.inventory.rows (selection.made.get port) = ContextualStoredRows.Row.shared
      (instantiate compiled.continuationEnv
        (plan.rule.produce.get ⟨port.val, compiled.source_admitted.output_shape ▸ port.isLt⟩)) := by
  have made : selection.made.get port ∈ compiled.firing.selection.made := by
    rw [compiled.selected]
    exact List.get_mem _ _
  rw [compiled.firing.shared_row made live, compiled.values,
    output_at_port queries locals before.declarations before.occupied selection plan.rule before.inventory.rows
      compiled.source_admitted.output_distinct compiled.source_admitted.output_shape port]
  apply congrArg ContextualStoredRows.Row.shared
  unfold continuationEnv
  exact (Assignment.instantiate_compose (ContextualComputedFreshFrame.includeSource compiled.firing.update)
    (frame queries locals before.declarations before.occupied).assignment _).symm.trans
      ((congrArg (fun assignment => instantiate assignment
        (queryView queries locals before.declarations (plan.rule.produce.get
          ⟨port.val, compiled.source_admitted.output_shape ▸ port.isLt⟩))) compiled.sourceFrame_assignment.symm).trans
        (Assignment.instantiate_compose compiled.sourceFrame.assignment
          (queryEmbedding queries locals before.declarations) _).symm)

theorem physical_result (compiled : Compiled queries locals plan selection) :
    compiled.firing.target.inventory.configuration.present =
      MeTTaCalculus.OccurrenceCommits.fire before.inventory.configuration.present (selection.commit (T := Unit)) := by
  rw [compiled.firing.physical_result, compiled.selected]
  rfl

end Compiled

theorem source_iff_compiled (plan : ContextualPublication.Plan
    (Term (signature S (queryFamily queries before.declarations)) Γ sort)) (selection : Selection O)
    (covered : RuleCovered (privateScopes before.scopes) before.occupied plan.rule)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (problem queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration))) :
    Admitted queries locals before.declarations selection plan.rule before.inventory.rows before.inventory.configuration ↔
      Nonempty (Compiled queries locals plan selection) :=
  ⟨fun admitted => realize queries locals plan selection covered admitted patterned,
    fun ⟨compiled⟩ => compiled.source_admitted⟩

end Execution

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClausePublication
