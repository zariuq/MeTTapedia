import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSource
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalNaturality

/-!
# Conditional template descriptors in an actual solver-backed publication

The source value grammar lowers through the existing template compiler.
Each schema descriptor additionally installs its own conditional row.
Production metadata is selected from the authored output port, and its
value is connected to the actual prepared production. Other outputs use
the existing ordinary/shared constructors. The physical update and global
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

/-- Authored template data before any execution has occurred. -/
structure TemplateInstance (before : ContextualConditionalExecution.State (Expanded locals inners) O Γ sort) where
  sourceRule : ContextualConditionalTemplateSource.Rule locals inners before.declarations Γ sort
  selection : Selection O
  outputs : O → Term (signature S (Active locals inners before.declarations)) Γ sort

/-- Schema recipes are computed from authored ports before admission or
solver execution. Ordinary and shared ports retain their existing policies. -/
def TemplateInstance.recipes {before : ContextualConditionalExecution.State (Expanded locals inners) O Γ sort}
    (authored : TemplateInstance locals inners before) (occurrence : O) :
    Option (ContextualConditionalPublication.Recipe (Expanded locals inners)
      (Active locals inners before.declarations)) :=
  match authored.sourceRule.outputsFor authored.selection.made occurrence with
  | some (origin, ⟨.schema _, conditions⟩) =>
      some (ContextualConditionalTemplates.recipe locals inners before.declarations
        (ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.rulePort authored.selection))
        origin conditions)
  | _ => none

omit [DecidableEq Local] [DecidableEq Inner] [DecidableEq S.Srt]
    [∀ result, DecidableEq (S.Op result)] in
theorem TemplateInstance.recipes_none_of_not_made
    {before : ContextualConditionalExecution.State (Expanded locals inners) O Γ sort}
    (authored : TemplateInstance locals inners before) (occurrence : O)
    (missing : occurrence ∉ authored.selection.made) :
    authored.recipes locals inners occurrence = none := by
  have absent : authored.sourceRule.outputsFor authored.selection.made occurrence = none := by
    cases found : authored.sourceRule.outputsFor authored.selection.made occurrence with
    | none => rfl
    | some description =>
        exact False.elim (missing (ContextualTemplateSource.assign_mem authored.selection.made
          authored.sourceRule.descriptions occurrence description found))
  simp only [TemplateInstance.recipes, absent]

/-- A template instance and the canonical published execution of its code. -/
abbrev CompiledTemplate (before : ContextualConditionalExecution.State (Expanded locals inners) O Γ sort) :=
  (authored : TemplateInstance locals inners before) ×
    ContextualConditionalExecution.Published (Expanded locals inners) before
      (authored.sourceRule.code.lower locals inners before.declarations) authored.selection authored.outputs
      (.all (authored.sourceRule.ordinaryFlags authored.selection.made))

namespace CompiledTemplate

variable {locals inners} {before : ContextualConditionalExecution.State (Expanded locals inners) O Γ sort}

abbrev sourceRule (firing : CompiledTemplate locals inners before) := firing.1.sourceRule

abbrev publication (firing : CompiledTemplate locals inners before) := firing.2

theorem reuse_intent (firing : CompiledTemplate locals inners before) :
    firing.publication.firing.reusable = firing.sourceRule.ordinaryFlags firing.publication.firing.selection.made := by
  rw [firing.publication.selected]
  exact firing.publication.intents

abbrev selection (firing : CompiledTemplate locals inners before) := firing.publication.firing.selection
abbrev update (firing : CompiledTemplate locals inners before) := firing.publication.firing.update

def scope (firing : CompiledTemplate locals inners before) :=
  ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.rulePort firing.selection)

def descriptor (firing : CompiledTemplate locals inners before) := firing.sourceRule.outputsFor firing.selection.made

theorem output_length (firing : CompiledTemplate locals inners before) :
    firing.selection.made.length = firing.sourceRule.code.produce.length := by
  have lengths := congrArg List.length firing.publication.firing.admitted.outputs
  rw [firing.publication.authored] at lengths
  simpa only [List.length_map, ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
    ContextualFreshening.ruleAt, RuleInstance.map, ContextualTemplateSource.Rule.lower, List.length_mapIdx] using lengths

theorem output_at_port (firing : CompiledTemplate locals inners before) (position : Fin firing.selection.made.length) :
    firing.publication.firing.outputs (firing.selection.made.get position) =
      (firing.sourceRule.code.produce.get ⟨position.val, firing.output_length ▸ position.isLt⟩).atScope
        locals inners before.declarations firing.scope position.val := by
  have values := congrArg (fun list => list[position.val]?) firing.publication.firing.admitted.outputs
  rw [firing.publication.authored] at values
  change (firing.selection.made.map firing.publication.firing.outputs)[position.val]? =
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

theorem output_of_descriptor (firing : CompiledTemplate locals inners before) (occurrence : O) (origin : Nat)
    (description : ContextualConditionalTemplateSource.Description locals inners before.declarations Γ sort)
    (selected : firing.descriptor occurrence = some (origin, description)) :
    firing.publication.firing.outputs occurrence = description.1.atScope locals inners before.declarations firing.scope origin := by
  have member := ContextualTemplateSource.assign_mem firing.selection.made firing.sourceRule.descriptions
    occurrence (origin, description) selected
  obtain ⟨position, same⟩ := List.mem_iff_get.mp member
  have source := firing.sourceRule.output_at_port firing.selection.made firing.publication.firing.admitted.output_distinct firing.output_length position
  rw [same] at source
  have entries := Option.some.inj (source.symm.trans selected)
  have ordinal := congrArg Prod.fst entries
  have production := congrArg (fun entry => entry.2.1) entries
  change position.val = origin at ordinal
  change firing.sourceRule.code.produce.get ⟨position.val, firing.output_length ▸ position.isLt⟩ = description.1 at production
  have value := firing.output_at_port position
  rw [same, production, ordinal] at value
  exact value

def publishedRows (firing : CompiledTemplate locals inners before) (occurrence : O) :
    Row (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration)
      firing.publication.firing.target.declarations Γ sort :=
  match firing.descriptor occurrence with
  | some (origin, ⟨.schema _, conditions⟩) =>
      ContextualConditionalPublication.extendPrivate (Expanded locals inners) firing.update.declaration _
        ((ContextualConditionalTemplates.recipe locals inners before.declarations firing.scope origin conditions).publish
          (ContextualComputedFreshFrame.includeSource firing.update) (firing.publication.firing.outputs occurrence))
  | _ => firing.publication.firing.target.rows occurrence

def target (firing : CompiledTemplate locals inners before) :
    ContextualConditionalExecution.State
      (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration) O Γ sort :=
  firing.publication.firing.target.withRows _ firing.publishedRows

/-- The observable rows are determined by the actual execution and the
pre-execution recipes. No authored body or arbitrary row callback is needed
at this boundary. -/
theorem publishedRows_from_recipes (firing : CompiledTemplate locals inners before) (occurrence : O) :
    firing.publishedRows occurrence =
      match firing.1.recipes locals inners occurrence with
      | some recipe => ContextualConditionalPublication.extendPrivate (Expanded locals inners)
          firing.update.declaration _
          (recipe.publish (ContextualComputedFreshFrame.includeSource firing.update)
            (firing.publication.firing.outputs occurrence))
      | none => firing.publication.firing.target.rows occurrence := by
  let compute (selection : Selection O) :=
    match firing.sourceRule.outputsFor selection.made occurrence with
    | some (origin, ⟨.schema _, conditions⟩) =>
        some (ContextualConditionalTemplates.recipe locals inners before.declarations
          (ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.rulePort selection))
          origin conditions)
    | _ => none
  have same := congrArg compute firing.publication.selected
  change firing.publishedRows occurrence =
    match compute firing.1.selection with
    | some recipe => ContextualConditionalPublication.extendPrivate _ _ _
        (recipe.publish (ContextualComputedFreshFrame.includeSource firing.update)
          (firing.publication.firing.outputs occurrence))
    | none => firing.publication.firing.target.rows occurrence
  rw [← same]
  dsimp only [compute, publishedRows, descriptor, scope]
  split <;> simp_all only [selection]

theorem schema_row (firing : CompiledTemplate locals inners before) (occurrence : O) (origin : Nat)
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
  rw [firing.output_of_descriptor occurrence origin _ selected]
  change ContextualConditionalPublication.extendPrivate _ _ _
    ((ContextualConditionalTemplates.recipe locals inners before.declarations firing.scope origin conditions).publish
      (ContextualComputedFreshFrame.includeSource firing.update)
      (instantiate (templateAt locals inners before.declarations firing.scope origin) body)) = _
  rw [ContextualConditionalTemplates.recipe_publish]
  rfl

theorem schema_matches_source (firing : CompiledTemplate locals inners before) (occurrence : O) (origin : Nat)
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

theorem ordinary_matches_source (firing : CompiledTemplate locals inners before) (occurrence : O) (origin : Nat)
    (value : Term (signature S (Actor locals before.declarations)) Γ sort)
    (selected : firing.descriptor occurrence = some (origin, ⟨.ordinary value, PUnit.unit⟩))
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment firing.target.declarations next)
    (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration)
        firing.target.declarations candidate pattern (firing.target.rows occurrence) ↔
      ContextualPublication.SourceInstances
        (ContextualConditionalExecution.information (Expanded locals inners) before.declarations before.occupied
          firing.selection firing.publication.firing.rule before.rows before.equations)
        (instantiate (actorAt locals inners before.declarations firing.scope) value) next pattern := by
  have made := ContextualTemplateSource.assign_mem firing.selection.made firing.sourceRule.descriptions
    occurrence (origin, ⟨.ordinary value, PUnit.unit⟩) selected
  have erased := firing.sourceRule.outputs_erase firing.selection.made occurrence
  change (firing.descriptor occurrence).map ContextualConditionalTemplateSource.Rule.eraseDescription = _ at erased
  rw [selected] at erased
  have ordinary : firing.publication.firing.reusable occurrence = true := by
    rw [firing.reuse_intent]
    unfold ContextualConditionalTemplateSource.Rule.ordinaryFlags
    rw [← erased]
    rfl
  change Matches _ _ candidate pattern (firing.publishedRows occurrence) ↔ _
  rw [publishedRows, selected]
  change Matches _ firing.publication.firing.target.declarations candidate pattern (firing.publication.firing.target.rows occurrence) ↔ _
  rw [firing.publication.firing.ordinary_matches_source occurrence made ordinary next candidate pattern,
    firing.output_of_descriptor occurrence origin _ selected]
  rfl

theorem shared_row (firing : CompiledTemplate locals inners before) (occurrence : O) (origin : Nat)
    (value : Term (signature S (Actor locals before.declarations)) Γ sort)
    (selected : firing.descriptor occurrence = some (origin, ⟨.shared value, PUnit.unit⟩)) :
    firing.target.rows occurrence = ofStored _ _ (.shared
      (instantiate (ContextualComputedFreshFrame.includeSource firing.update)
        (instantiate (actorAt locals inners before.declarations firing.scope) value))) := by
  have made := ContextualTemplateSource.assign_mem firing.selection.made firing.sourceRule.descriptions
    occurrence (origin, ⟨.shared value, PUnit.unit⟩) selected
  have erased := firing.sourceRule.outputs_erase firing.selection.made occurrence
  change (firing.descriptor occurrence).map ContextualConditionalTemplateSource.Rule.eraseDescription = _ at erased
  rw [selected] at erased
  have shared : firing.publication.firing.reusable occurrence = false := by
    rw [firing.reuse_intent]
    unfold ContextualConditionalTemplateSource.Rule.ordinaryFlags
    rw [← erased]
    rfl
  change firing.publishedRows occurrence = _
  rw [publishedRows, selected, firing.publication.firing.shared_row occurrence made shared,
    firing.output_of_descriptor occurrence origin _ selected]
  rfl

/-- The schema's body comes from the actual compiled production through
the existing binding-role decoder, rather than a supplied target value. -/
theorem schema_body_from_actual_production (firing : CompiledTemplate locals inners before) (occurrence : O) (origin : Nat)
    (body : Term (signature S (Blueprint locals inners before.declarations)) Γ sort)
    (conditions : ContextualResidual.Problem (Blueprint locals inners before.declarations))
    (selected : firing.descriptor occurrence = some (origin, ⟨.schema body, conditions⟩)) :
    instantiate (ContextualTemplatePublication.decoder locals inners before.declarations firing.update.declaration)
        (instantiate (ContextualComputedFreshFrame.includeSource firing.update) (firing.publication.firing.outputs occurrence)) =
      ContextualStoredRows.asTemplate (Expanded locals inners) firing.target.declarations
        (ContextualTemplateSource.stored locals inners before.declarations
          (ContextualTemplatePublication.captureValues locals inners before.declarations firing.update firing.scope) origin body) := by
  rw [firing.output_of_descriptor occurrence origin _ selected]
  exact ContextualTemplatePublication.stored_decodes_the_compiled_body locals inners before.declarations firing.update firing.scope origin body

theorem retained_row (firing : CompiledTemplate locals inners before) (occurrence : O)
    (notMade : occurrence ∉ firing.selection.made) : firing.target.rows occurrence = firing.publication.firing.target.rows occurrence := by
  have missing : firing.descriptor occurrence = none := by
    cases selected : firing.descriptor occurrence with
    | none => rfl
    | some entry =>
        exact False.elim (notMade (ContextualTemplateSource.assign_mem firing.selection.made firing.sourceRule.descriptions occurrence entry selected))
  change firing.publishedRows occurrence = _
  rw [publishedRows, missing]

theorem physical_result (firing : CompiledTemplate locals inners before) :
    firing.target.present = fire before.present (firing.selection.commit (T := Unit)) := rfl

theorem global_information (firing : CompiledTemplate locals inners before) :
    firing.target.equations = firing.publication.firing.target.equations := rfl


theorem every_native_model_projects (firing : CompiledTemplate locals inners before)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment firing.target.declarations next)
    (model : ContextualResidual.Models candidate firing.target.equations) :
    ContextualResidual.Models (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
      (ContextualConditionalExecution.information (Expanded locals inners) before.declarations before.occupied
        firing.selection firing.publication.firing.rule before.rows before.equations) :=
  firing.publication.firing.model_projects next candidate model

/-- Every given actor model, not just some solution, survives publication.
New solver declarations are supplied in a fresh extension of that model. -/
theorem every_actor_model_extends (firing : CompiledTemplate locals inners before)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment (Active locals inners before.declarations) next)
    (model : ContextualResidual.Models candidate
      (ContextualConditionalExecution.information (Expanded locals inners) before.declarations before.occupied
        firing.selection firing.publication.firing.rule before.rows before.equations)) :
    ∃ extension : ContextualGuardMatching.Extension next,
    ∃ realized : Assignment firing.target.declarations extension.declarations,
      ContextualResidual.Models realized firing.target.equations ∧
        Assignment.compose realized (ContextualComputedFreshFrame.includeSource firing.update) =
          Assignment.compose extension.assignment candidate := by
  exact firing.publication.firing.model_extends next candidate model

theorem target_solvable (firing : CompiledTemplate locals inners before) :
    ContextualConditionalExecution.Solvable firing.target.equations := by
  exact firing.publication.firing.target_solvable

end CompiledTemplate

/-- Source descriptors and binding admission construct an actual finite-
budget solver return. Schema conditions are not admission premises. -/
theorem realize
    (before : ContextualConditionalExecution.State (Expanded locals inners) O Γ sort)
    (sourceRule : ContextualConditionalTemplateSource.Rule locals inners before.declarations Γ sort)
    (selection : Selection O) (outputs : O → Term (signature S (Active locals inners before.declarations)) Γ sort)
    (admitted : ContextualConditionalExecution.Admitted (Expanded locals inners) before
      (sourceRule.code.lower locals inners before.declarations) selection outputs) (fuel : Nat) :
    ∃ firing : CompiledTemplate locals inners before, firing.sourceRule = sourceRule ∧ firing.selection = selection ∧
      firing.publication.firing.outputs = outputs ∧ firing.publication.firing.fuel = fuel := by
  obtain ⟨execution, compiled, selected, values, flags, budget⟩ :=
    ContextualConditionalExecution.realize_at_fuel (Expanded locals inners) before
      (sourceRule.code.lower locals inners before.declarations) selection outputs
      (sourceRule.ordinaryFlags selection.made) admitted fuel
  exact ⟨⟨⟨sourceRule, selection, outputs⟩, ⟨execution, compiled, selected, values, flags⟩⟩,
    rfl, selected, values, budget⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateExecution
