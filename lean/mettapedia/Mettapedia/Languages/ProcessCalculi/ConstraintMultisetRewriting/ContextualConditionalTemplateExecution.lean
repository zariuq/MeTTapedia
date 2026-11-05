import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSource
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalNaturality

/-!
# Conditional template descriptors in an actual solver-backed publication

The source value grammar lowers through the existing template compiler.
Each schema descriptor additionally installs its own conditional row.
Production metadata is selected from the authored output port, and its
value is connected to the actual prepared production. Other outputs use
the existing ordinary/live constructors. The physical update and global
information remain those of the same actual conditional firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualTemplateSource ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local Inner O : Type}
    (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
    [DecidableEq Local] [DecidableEq Inner] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {Γ : Ctx S} {sort : S.Srt}

structure Firing (before : ContextualConditionalExecution.State (Expanded locals inners) O Γ sort) where
  sourceRule : ContextualConditionalTemplateSource.Rule locals inners before.declarations Γ sort
  execution : ContextualConditionalExecution.Firing (Expanded locals inners) before
  compiled : execution.rule = sourceRule.code.lower locals inners before.declarations
  flags : execution.reusable = sourceRule.ordinaryFlags execution.selection.made

namespace Firing

variable {locals inners} {before : ContextualConditionalExecution.State (Expanded locals inners) O Γ sort}

abbrev selection (firing : Firing locals inners before) := firing.execution.selection
abbrev update (firing : Firing locals inners before) := firing.execution.update

def scope (firing : Firing locals inners before) :=
  ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.rulePort firing.selection)

def descriptor (firing : Firing locals inners before) := firing.sourceRule.outputsFor firing.selection.made

theorem output_length (firing : Firing locals inners before) :
    firing.selection.made.length = firing.sourceRule.code.produce.length := by
  have lengths := congrArg List.length firing.execution.admitted.outputs
  rw [firing.compiled] at lengths
  simpa only [List.length_map, ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
    ContextualFreshening.ruleAt, RuleInstance.map, ContextualTemplateSource.Rule.lower, List.length_mapIdx] using lengths

theorem output_at_port (firing : Firing locals inners before) (position : Fin firing.selection.made.length) :
    firing.execution.outputs (firing.selection.made.get position) =
      (firing.sourceRule.code.produce.get ⟨position.val, firing.output_length ▸ position.isLt⟩).atScope
        locals inners before.declarations firing.scope position.val := by
  have values := congrArg (fun list => list[position.val]?) firing.execution.admitted.outputs
  rw [firing.compiled] at values
  change (firing.selection.made.map firing.execution.outputs)[position.val]? =
    ((firing.sourceRule.code.produce.mapIdx fun port production => production.lower locals inners before.declarations port).map
      (ContextualFreshening.termAt (Expanded locals inners) before.declarations firing.scope))[position.val]? at values
  have bound : position.val < (firing.sourceRule.code.produce.mapIdx
      fun port production => production.lower locals inners before.declarations port).length := by
    rw [List.length_mapIdx]
    exact firing.output_length ▸ position.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem position.isLt,
    List.getElem?_eq_getElem bound, Option.map_some] at values
  have actual := Option.some.inj values
  erw [List.getElem_mapIdx, Production.freshened_lower] at actual
  exact actual

theorem output_of_descriptor (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (description : ContextualConditionalTemplateSource.Description locals inners before.declarations Γ sort)
    (selected : firing.descriptor occurrence = some (origin, description)) :
    firing.execution.outputs occurrence = description.1.atScope locals inners before.declarations firing.scope origin := by
  have member := ContextualTemplateSource.assign_mem firing.selection.made firing.sourceRule.descriptions
    occurrence (origin, description) selected
  obtain ⟨position, same⟩ := List.mem_iff_get.mp member
  have source := firing.sourceRule.output_at_port firing.selection.made firing.execution.admitted.output_distinct firing.output_length position
  rw [same] at source
  have entries := Option.some.inj (source.symm.trans selected)
  have ordinal := congrArg Prod.fst entries
  have production := congrArg (fun entry => entry.2.1) entries
  change position.val = origin at ordinal
  change firing.sourceRule.code.produce.get ⟨position.val, firing.output_length ▸ position.isLt⟩ = description.1 at production
  have value := firing.output_at_port position
  rw [same, production, ordinal] at value
  exact value

def publishedRows (firing : Firing locals inners before) (occurrence : O) :
    Row (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration)
      firing.execution.target.declarations Γ sort :=
  match firing.descriptor occurrence with
  | some (origin, ⟨.schema body, conditions⟩) =>
      ContextualConditionalPublication.extendPrivate (Expanded locals inners) firing.update.declaration _
        (ContextualConditionalTemplates.stored locals inners before.declarations
          (ContextualTemplatePublication.captureValues locals inners before.declarations firing.update firing.scope)
          origin ⟨.schema body, conditions⟩)
  | _ => firing.execution.target.rows occurrence

def target (firing : Firing locals inners before) :
    ContextualConditionalExecution.State
      (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration) O Γ sort :=
  { firing.execution.target with rows := firing.publishedRows }

theorem schema_row (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (body : Term (signature S (Blueprint locals inners before.declarations)) Γ sort)
    (conditions : ContextualResidual.Problem (Blueprint locals inners before.declarations))
    (selected : firing.descriptor occurrence = some (origin, ⟨.schema body, conditions⟩)) :
    firing.target.rows occurrence =
      ContextualConditionalPublication.extendPrivate (Expanded locals inners) firing.update.declaration _
        (ContextualConditionalTemplates.stored locals inners before.declarations
          (ContextualTemplatePublication.captureValues locals inners before.declarations firing.update firing.scope)
          origin ⟨.schema body, conditions⟩) := by
  change firing.publishedRows occurrence = _
  rw [publishedRows, selected]

theorem schema_matches_source (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (body : Term (signature S (Blueprint locals inners before.declarations)) Γ sort)
    (conditions : ContextualResidual.Problem (Blueprint locals inners before.declarations))
    (selected : firing.descriptor occurrence = some (origin, ⟨.schema body, conditions⟩))
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment firing.target.declarations next)
    (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration)
        firing.target.declarations candidate pattern (firing.target.rows occurrence) ↔
      Matches inners (Actor locals before.declarations)
        (Assignment.compose candidate (ContextualTemplatePublication.captureValues locals inners before.declarations firing.update firing.scope))
        pattern ⟨.schema body, conditions⟩ := by
  rw [firing.schema_row occurrence origin body conditions selected]
  erw [ContextualConditionalPublication.extendPrivate_matches_iff]
  exact ContextualConditionalTemplates.stored_matches_iff locals inners before.declarations _ origin candidate _ pattern

theorem ordinary_matches_source (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (value : Term (signature S (Actor locals before.declarations)) Γ sort)
    (selected : firing.descriptor occurrence = some (origin, ⟨.ordinary value, PUnit.unit⟩))
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment firing.target.declarations next)
    (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration)
        firing.target.declarations candidate pattern (firing.target.rows occurrence) ↔
      ContextualPublication.SourceInstances
        (ContextualConditionalExecution.information (Expanded locals inners) before.declarations before.occupied
          firing.selection firing.execution.rule before.rows before.equations)
        (instantiate (actorAt locals inners before.declarations firing.scope) value) next pattern := by
  have made := ContextualTemplateSource.assign_mem firing.selection.made firing.sourceRule.descriptions
    occurrence (origin, ⟨.ordinary value, PUnit.unit⟩) selected
  have erased := firing.sourceRule.outputs_erase firing.selection.made occurrence
  change (firing.descriptor occurrence).map ContextualConditionalTemplateSource.Rule.eraseDescription = _ at erased
  rw [selected] at erased
  have ordinary : firing.execution.reusable occurrence = true := by
    rw [firing.flags]
    unfold ContextualConditionalTemplateSource.Rule.ordinaryFlags
    rw [← erased]
    rfl
  change Matches _ _ candidate pattern (firing.publishedRows occurrence) ↔ _
  rw [publishedRows, selected]
  change Matches _ firing.execution.target.declarations candidate pattern (firing.execution.target.rows occurrence) ↔ _
  rw [firing.execution.ordinary_matches_source occurrence made ordinary next candidate pattern,
    firing.output_of_descriptor occurrence origin _ selected]
  rfl

theorem live_row (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (value : Term (signature S (Actor locals before.declarations)) Γ sort)
    (selected : firing.descriptor occurrence = some (origin, ⟨.live value, PUnit.unit⟩)) :
    firing.target.rows occurrence = ofStored _ _ (.live
      (instantiate (ContextualComputedFreshFrame.includeSource firing.update)
        (instantiate (actorAt locals inners before.declarations firing.scope) value))) := by
  have made := ContextualTemplateSource.assign_mem firing.selection.made firing.sourceRule.descriptions
    occurrence (origin, ⟨.live value, PUnit.unit⟩) selected
  have erased := firing.sourceRule.outputs_erase firing.selection.made occurrence
  change (firing.descriptor occurrence).map ContextualConditionalTemplateSource.Rule.eraseDescription = _ at erased
  rw [selected] at erased
  have shared : firing.execution.reusable occurrence = false := by
    rw [firing.flags]
    unfold ContextualConditionalTemplateSource.Rule.ordinaryFlags
    rw [← erased]
    rfl
  change firing.publishedRows occurrence = _
  rw [publishedRows, selected, firing.execution.live_row occurrence made shared,
    firing.output_of_descriptor occurrence origin _ selected]
  rfl

/-- The schema's body comes from the actual compiled production through
the existing binding-role decoder, rather than a supplied target value. -/
theorem schema_body_from_actual_production (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (body : Term (signature S (Blueprint locals inners before.declarations)) Γ sort)
    (conditions : ContextualResidual.Problem (Blueprint locals inners before.declarations))
    (selected : firing.descriptor occurrence = some (origin, ⟨.schema body, conditions⟩)) :
    instantiate (ContextualTemplatePublication.decoder locals inners before.declarations firing.update.declaration)
        (instantiate (ContextualComputedFreshFrame.includeSource firing.update) (firing.execution.outputs occurrence)) =
      ContextualStoredRows.asTemplate (Expanded locals inners) firing.target.declarations
        (ContextualTemplateSource.stored locals inners before.declarations
          (ContextualTemplatePublication.captureValues locals inners before.declarations firing.update firing.scope) origin body) := by
  rw [firing.output_of_descriptor occurrence origin _ selected]
  exact ContextualTemplatePublication.stored_decodes_the_compiled_body locals inners before.declarations firing.update firing.scope origin body

theorem retained_row (firing : Firing locals inners before) (occurrence : O)
    (notMade : occurrence ∉ firing.selection.made) : firing.target.rows occurrence = firing.execution.target.rows occurrence := by
  have missing : firing.descriptor occurrence = none := by
    cases selected : firing.descriptor occurrence with
    | none => rfl
    | some entry =>
        exact False.elim (notMade (ContextualTemplateSource.assign_mem firing.selection.made firing.sourceRule.descriptions occurrence entry selected))
  change firing.publishedRows occurrence = _
  rw [publishedRows, missing]

theorem physical_result (firing : Firing locals inners before) :
    firing.target.present = fire before.present (firing.selection.commit (T := Unit)) := rfl

theorem global_information (firing : Firing locals inners before) :
    firing.target.equations = firing.execution.target.equations := rfl

def resultFrame (firing : Firing locals inners before) :
    ContextualGuardMatching.Extension (Active locals inners before.declarations) where
  Names := firing.target.Names
  declarations := firing.target.declarations
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

theorem resultFrame_assignment (firing : Firing locals inners before) :
    firing.resultFrame.assignment = ContextualComputedFreshFrame.includeSource firing.update := by
  funext name
  exact (ContextualFreshFrameScopeLedger.includeSource_image firing.update name).symm

theorem every_native_model_projects (firing : Firing locals inners before)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment firing.target.declarations next)
    (model : ContextualResidual.Models candidate firing.target.equations) :
    ContextualResidual.Models (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
      (ContextualConditionalExecution.information (Expanded locals inners) before.declarations before.occupied
        firing.selection firing.execution.rule before.rows before.equations) :=
  (ContextualResidual.models_mapProblem _ _ _).mp model

/-- Every given actor model, not just some solution, survives publication.
New solver declarations are supplied in a fresh extension of that model. -/
theorem every_actor_model_extends (firing : Firing locals inners before)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment (Active locals inners before.declarations) next)
    (model : ContextualResidual.Models candidate
      (ContextualConditionalExecution.information (Expanded locals inners) before.declarations before.occupied
        firing.selection firing.execution.rule before.rows before.equations)) :
    ∃ extension : ContextualGuardMatching.Extension next,
    ∃ realized : Assignment firing.target.declarations extension.declarations,
      ContextualResidual.Models realized firing.target.equations ∧
        Assignment.compose realized (ContextualComputedFreshFrame.includeSource firing.update) =
          Assignment.compose extension.assignment candidate := by
  let extension := ContextualGuardMatching.Extension.withLocals firing.resultFrame.complementDeclarations next
  refine ⟨extension, firing.resultFrame.liftModel candidate, ?_, ?_⟩
  · change ContextualResidual.Models _ (ContextualResidual.mapProblem
      (ContextualComputedFreshFrame.includeSource firing.update) _)
    rw [← firing.resultFrame_assignment]
    exact (ContextualConditionalNaturality.models_liftModel_iff firing.resultFrame candidate _).mpr model
  · rw [← firing.resultFrame_assignment]
    exact firing.resultFrame.liftModel_square candidate

theorem target_solvable (firing : Firing locals inners before) :
    ContextualConditionalExecution.Solvable firing.target.equations := by
  change ContextualConditionalExecution.Solvable (ContextualResidual.mapProblem
    (ContextualComputedFreshFrame.includeSource firing.update) _)
  rw [← firing.resultFrame_assignment]
  exact (ContextualConditionalNaturality.solvable_extension_iff firing.resultFrame _).mpr firing.execution.admitted.solvable

end Firing

/-- Source descriptors and binding admission construct an actual finite-
budget solver return. Schema conditions are not admission premises. -/
theorem realize
    (before : ContextualConditionalExecution.State (Expanded locals inners) O Γ sort)
    (sourceRule : ContextualConditionalTemplateSource.Rule locals inners before.declarations Γ sort)
    (selection : Selection O) (outputs : O → Term (signature S (Active locals inners before.declarations)) Γ sort)
    (admitted : ContextualConditionalExecution.Admitted (Expanded locals inners) before
      (sourceRule.code.lower locals inners before.declarations) selection outputs) (fuel : Nat) :
    ∃ firing : Firing locals inners before, firing.sourceRule = sourceRule ∧ firing.selection = selection ∧
      firing.execution.outputs = outputs ∧ firing.execution.fuel = fuel := by
  obtain ⟨execution, compiled, selected, values, flags, budget⟩ :=
    ContextualConditionalExecution.realize_at_fuel (Expanded locals inners) before
      (sourceRule.code.lower locals inners before.declarations) selection outputs
      (sourceRule.ordinaryFlags selection.made) admitted fuel
  refine ⟨⟨sourceRule, execution, compiled, ?_⟩, rfl, selected, values, budget⟩
  rw [flags, selected]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateExecution
