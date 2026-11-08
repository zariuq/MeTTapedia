import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalSourceAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClausePublication

/-!
# Resolved source clauses publish conditional answers at any solver budget

The independent conditional-input source semantics and its query/row/capture
embedding construct the conditional execution directly, including when a
previous clause left pending conditions. No structural-pattern
completion hypothesis is needed. The source admission still supplies joint
solvability and original-cut guards; arbitrary unfinished solver results
are neither empty answers nor admission certificates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualClauseFrames ContextualConditionalSourceProblem ContextualConditionalSourceAdmission
open ContextualConditionalNaturality
open ContextualConjunctiveQueries

variable {S : Signature} {Query Local O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S)
    [DecidableEq Query] [DecidableEq Local] [DecidableEq O]
    [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {Γ : Ctx S} {sort : S.Srt} {before : ContextualConditionalExecution.State locals O Γ sort}

abbrev Compiled (plan : ContextualPublication.Plan
    (Term (signature S (queryFamily queries before.declarations)) Γ sort)) (selection : Selection O) :=
  ContextualConditionalExecution.Published (bank queries locals) (prepareState queries locals before)
    (ContextualClauseProblem.nativeRule queries locals before.declarations plan.rule) selection
    (outputs queries locals before.declarations before.occupied selection plan.rule before.rows)
    (.made plan.reusable)

theorem realize (plan : ContextualPublication.Plan
    (Term (signature S (queryFamily queries before.declarations)) Γ sort)) (selection : Selection O)
    (source : Admitted queries locals before.declarations selection plan.rule before.rows before.equations before.present)
    (fuel : Nat) : ∃ compiled : Compiled queries locals plan selection, compiled.firing.fuel = fuel := by
  let _ := before.equality
  have conditional := (admitted_iff queries locals before selection plan.rule).mp source
  obtain ⟨firing, authored, selected, values, kinds, budget⟩ := ContextualConditionalExecution.realize_at_fuel
    (bank queries locals) (prepareState queries locals before)
    (ContextualClauseProblem.nativeRule queries locals before.declarations plan.rule) selection
    (outputs queries locals before.declarations before.occupied selection plan.rule before.rows)
    (ContextualPublication.flagsFor selection.made plan.reusable) conditional fuel
  refine ⟨⟨firing, authored, selected, values, ?_⟩, budget⟩
  rw [kinds]
  exact ContextualPublication.flagsFor_map _ _ source.output_distinct (source.output_shape.trans plan.shape.symm)

namespace Compiled

variable {queries locals} {plan : ContextualPublication.Plan
    (Term (signature S (queryFamily queries before.declarations)) Γ sort)} {selection : Selection O}

theorem source_admitted (compiled : Compiled queries locals plan selection) :
    Admitted queries locals before.declarations selection plan.rule before.rows before.equations before.present := by
  have actual := compiled.firing.admitted
  rw [compiled.authored, compiled.selected, compiled.values] at actual
  exact (admitted_iff queries locals before selection plan.rule).mpr actual

theorem target_formed (compiled : Compiled queries locals plan selection)
    (scopes : before.Names → Finset Nat) (formed : ContextualConditionalScopes.Formed locals before scopes)
    (covered : ContextualWorldScopeLedger.RuleCovered (ContextualScopeSupport.privateScopes scopes)
      before.occupied plan.rule) :
    ContextualConditionalScopes.Formed
      (ContextualPublication.privateFamily (bank queries locals) compiled.firing.update.declaration)
      compiled.firing.target (ContextualConditionalScopes.targetScopes (bank queries locals) compiled.firing scopes) := by
  apply ContextualConditionalScopes.firing_preserves_formation
  · exact prepare_formed queries locals before scopes formed
  · rw [compiled.authored]
    exact ContextualClausePublication.rule_covered queries locals before.declarations scopes
      before.occupied plan.rule covered

theorem native_information (compiled : Compiled queries locals plan selection) :
    ContextualConditionalExecution.information (bank queries locals) before.declarations before.occupied
      compiled.firing.selection compiled.firing.rule
      (prepareState queries locals before).rows before.equations =
    ContextualResidual.mapProblem
      (frame queries locals before.declarations before.occupied).assignment
      (problem queries locals before.declarations selection plan.rule before.rows before.equations) := by
  rw [compiled.authored, compiled.selected]
  exact actual_information queries locals before.declarations before.occupied selection plan.rule before.rows before.equations

def sourceFrame (compiled : Compiled queries locals plan selection) :
    ContextualGuardMatching.Extension (family queries locals before.declarations) :=
  (frame queries locals before.declarations before.occupied).trans compiled.firing.resultFrame

theorem sourceFrame_assignment (compiled : Compiled queries locals plan selection) :
    compiled.sourceFrame.assignment = Assignment.compose (ContextualComputedFreshFrame.includeSource compiled.firing.update)
      (frame queries locals before.declarations before.occupied).assignment :=
  ((frame queries locals before.declarations before.occupied).trans_assignment compiled.firing.resultFrame).trans
    (congrArg (fun assignment => Assignment.compose assignment
      (frame queries locals before.declarations before.occupied).assignment) compiled.firing.resultFrame_assignment)

def continuationEnv (compiled : Compiled queries locals plan selection) :
    Assignment (queryFamily queries before.declarations) compiled.firing.target.declarations :=
  Assignment.compose compiled.sourceFrame.assignment (queryEmbedding queries locals before.declarations)

theorem result_equations (compiled : Compiled queries locals plan selection) :
    compiled.firing.target.equations = ContextualResidual.mapProblem compiled.sourceFrame.assignment
      (problem queries locals before.declarations selection plan.rule before.rows before.equations) := by
  have mapped := congrArg (ContextualResidual.mapProblem
    (ContextualComputedFreshFrame.includeSource compiled.firing.update)) compiled.native_information
  apply mapped.trans
  erw [map_problem_compose, ← compiled.sourceFrame_assignment]
  rfl

theorem continuation_instances (compiled : Compiled queries locals plan selection)
    (value : Term (signature S (queryFamily queries before.declarations)) Γ sort)
    {Next : Type} (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances compiled.firing.target.equations
      (instantiate compiled.continuationEnv value) next pattern ↔
    ContextualPublication.SourceInstances
      (problem queries locals before.declarations selection plan.rule before.rows before.equations)
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
    ContextualConditionalRows.Matches
      (ContextualPublication.privateFamily (bank queries locals) compiled.firing.update.declaration)
      compiled.firing.target.declarations candidate pattern (compiled.firing.target.rows (selection.made.get port)) ↔
    ContextualPublication.SourceInstances
      (problem queries locals before.declarations selection plan.rule before.rows before.equations)
      (queryView queries locals before.declarations
        (plan.rule.produce.get ⟨port.val, compiled.source_admitted.output_shape ▸ port.isLt⟩)) next pattern := by
  have made : selection.made.get port ∈ compiled.firing.selection.made := by
    rw [compiled.selected]
    exact List.get_mem _ _
  have actual := compiled.firing.ordinary_matches_source _ made reusable next candidate pattern
  apply actual.trans
  rw [compiled.values]
  change ContextualPublication.SourceInstances
    (ContextualConditionalExecution.information (bank queries locals) before.declarations before.occupied
      compiled.firing.selection compiled.firing.rule
      (prepareState queries locals before).rows before.equations)
    (ContextualClauseAdmission.outputs queries locals before.declarations before.occupied selection plan.rule
      (fun occurrence => (before.rows occurrence).value) (selection.made.get port)) next pattern ↔ _
  rw [ContextualClausePublication.output_at_port queries locals before.declarations before.occupied
    selection plan.rule (fun occurrence => (before.rows occurrence).value)
    compiled.source_admitted.output_distinct compiled.source_admitted.output_shape port, compiled.native_information]
  exact source_instances_extension (frame queries locals before.declarations before.occupied) _ _ next pattern

theorem physical_result (compiled : Compiled queries locals plan selection) :
    compiled.firing.target.present = MeTTaCalculus.OccurrenceCommits.fire
      before.present (selection.commit (T := Unit)) := by
  rw [compiled.firing.physical_result, compiled.selected]
  rfl

end Compiled

theorem source_iff_compiled_at_fuel (plan : ContextualPublication.Plan
    (Term (signature S (queryFamily queries before.declarations)) Γ sort)) (selection : Selection O) (fuel : Nat) :
    Admitted queries locals before.declarations selection plan.rule before.rows before.equations before.present ↔
      ∃ compiled : Compiled queries locals plan selection, compiled.firing.fuel = fuel :=
  ⟨fun source => realize queries locals plan selection source fuel, fun ⟨compiled, _⟩ => compiled.source_admitted⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses
