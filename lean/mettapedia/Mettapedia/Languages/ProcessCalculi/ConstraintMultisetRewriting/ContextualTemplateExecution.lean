import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication

/-!
# Constructed templates in the actual publication endpoint

The record retains the existing checked execution and its authored source
rule. Production metadata is selected by source port. Ordinary values use
the existing normalized reusable publication; shared values keep source
references; constructed templates install their private keys and explicit
captures in that same final inventory. No second resource transition is
introduced by installing the row metadata.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualTemplateSource ContextualScopeSupport ContextualWorldScopeLedger

variable {S : Signature} {Local Inner O : Type}
    (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
    [DecidableEq Local] [DecidableEq Inner] [DecidableEq O]
    [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {Γ : Ctx S} {sort : S.Srt}

structure Firing (before : ContextualExecution.Endpoint (Expanded locals inners) O Γ sort) where
  sourceRule : ContextualTemplateSource.Rule locals inners before.declarations Γ sort
  sourceTarget : ContextualExecution.Endpoint (Expanded locals inners) O Γ sort
  execution : ContextualExecution.Firing (Expanded locals inners) before sourceTarget
  compiled : execution.rule = sourceRule.lower locals inners before.declarations

namespace Firing

variable {locals inners} {before : ContextualExecution.Endpoint (Expanded locals inners) O Γ sort}

abbrev selection (firing : Firing locals inners before) := firing.execution.selection
abbrev update (firing : Firing locals inners before) := firing.execution.update

def scope (firing : Firing locals inners before) :=
  ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.rulePort firing.selection)

def descriptor (firing : Firing locals inners before) :=
  firing.sourceRule.outputsFor locals inners before.declarations firing.selection.made

private def ordinaryFlag (firing : Firing locals inners before) (occurrence : O) : Bool :=
  match firing.descriptor occurrence with
  | some (_, .ordinary _) => true
  | _ => false

private def defaultPublication (firing : Firing locals inners before) :
    ContextualPublication.Firing (before := before) :=
  ⟨firing.sourceTarget, firing.execution, ordinaryFlag firing⟩

theorem output_length (firing : Firing locals inners before) :
    firing.selection.made.length = firing.sourceRule.produce.length := by
  have lengths := congrArg List.length firing.execution.admitted.outputs
  rw [firing.compiled] at lengths
  simpa only [List.length_map, ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
    ContextualFreshening.ruleAt, RuleInstance.map, ContextualTemplateSource.Rule.lower,
    List.length_mapIdx] using lengths

theorem schema_covered (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (body : Term (signature S (Blueprint locals inners before.declarations)) Γ sort)
    (selected : firing.descriptor occurrence = some (origin, .schema body)) :
    row (Expanded locals inners)
      (Post locals inners before.declarations firing.update.declaration)
      (defaultPublication firing).target.scopes
      (stored locals inners before.declarations
        (captureValues locals inners before.declarations firing.update firing.scope) origin body) ⊆
      (defaultPublication firing).target.occupied := by
  obtain ⟨position, originEq, productionEq⟩ := firing.sourceRule.output_origin locals inners before.declarations
    firing.selection.made firing.execution.admitted.output_distinct firing.output_length occurrence origin (.schema body) selected
  have selectedRaw :
      (firing.sourceRule.produce.get position).lower locals inners before.declarations position.val ∈
        firing.execution.rule.produce := by
    rw [firing.compiled]
    exact (firing.sourceRule.lower_at_port locals inners before.declarations position) ▸ List.get_mem _ _
  simp only [productionEq, originEq, Production.lower] at selectedRaw
  have rawCovered := firing.execution.ruleCovered.produce _ selectedRaw
  have allocated : firing.scope ∈ ContextualActivationScopes.after before.occupied firing.selection :=
    ContextualActivationScopes.allocated_scopes_retained before.occupied firing.selection
      (ContextualActivationScopes.at_mem_reserved before.occupied firing.selection
        (ContextualActivationScopes.rulePort firing.selection))
  have activated := covered_termAt (Expanded locals inners) before.declarations before.scopes allocated
    (rawCovered.mono (ContextualActivationScopes.old_scopes_retained before.occupied firing.selection))
  change Covered (activeScopes before.scopes) (ContextualActivationScopes.after before.occupied firing.selection)
    (ContextualFreshening.termAt (Expanded locals inners) before.declarations firing.scope
      ((Production.schema body).lower locals inners before.declarations origin)) at activated
  erw [Production.freshened_lower] at activated
  apply stored_covered locals inners before.declarations firing.update firing.scope origin
    (defaultPublication firing).target.scopes (defaultPublication firing).target.occupied body
  exact covered_instantiate_of_respects (activeScopes before.scopes) _ _
    (ContextualComputedFreshFrame.includeSource firing.update)
    (ContextualFreshFrameScopeLedger.includeSource_respects firing.update (activeScopes before.scopes) _)
    (activated.mono (ContextualFreshFrameScopeLedger.old_scopes_retained
      (ContextualActivationScopes.after before.occupied firing.selection)))

def publishedRows (firing : Firing locals inners before) (occurrence : O) :
    ContextualStoredRows.Row (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration)
      (Post locals inners before.declarations firing.update.declaration) Γ sort :=
  match firing.descriptor occurrence with
  | some (origin, .schema body) =>
      ContextualPublication.extendPrivate (Expanded locals inners) firing.update.declaration
        (stored locals inners before.declarations
          (captureValues locals inners before.declarations firing.update firing.scope) origin body)
  | _ => (defaultPublication firing).target.inventory.rows occurrence

theorem publishedRows_covered (firing : Firing locals inners before) (occurrence : O)
    (present : occurrence ∈ (defaultPublication firing).target.inventory.configuration.present) :
    row (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration)
      (Post locals inners before.declarations firing.update.declaration)
      (defaultPublication firing).target.scopes (firing.publishedRows occurrence) ⊆
      (defaultPublication firing).target.occupied := by
  have unchanged := (defaultPublication firing).target.covered.rows occurrence present
  change row (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration)
    (Post locals inners before.declarations firing.update.declaration)
    (defaultPublication firing).target.scopes ((defaultPublication firing).target.inventory.rows occurrence) ⊆
      (defaultPublication firing).target.occupied at unchanged
  cases selected : firing.descriptor occurrence with
  | none => simpa only [publishedRows, selected] using unchanged
  | some entry =>
      rcases entry with ⟨origin, production⟩
      cases production with
      | ordinary value =>
          simpa only [publishedRows, selected] using unchanged
      | shared value =>
          simpa only [publishedRows, selected] using unchanged
      | schema body =>
          have extended := ContextualPublication.row_extendPrivate_covered (Expanded locals inners) firing.update.declaration
            (Post locals inners before.declarations firing.update.declaration) (defaultPublication firing).target.scopes
            (stored locals inners before.declarations
              (captureValues locals inners before.declarations firing.update firing.scope) origin body)
            (firing.schema_covered occurrence origin body selected)
          simpa only [publishedRows, selected] using extended

def target (firing : Firing locals inners before) :
    ContextualExecution.Endpoint
      (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration) O Γ sort :=
  { (defaultPublication firing).target with
    inventory := { (defaultPublication firing).target.inventory with rows := firing.publishedRows }
    covered := ⟨(defaultPublication firing).target.covered.equations, firing.publishedRows_covered,
      (defaultPublication firing).target.covered.retained, (defaultPublication firing).target.covered.templates⟩ }

theorem schema_row (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (body : Term (signature S (Blueprint locals inners before.declarations)) Γ sort)
    (selected : firing.descriptor occurrence = some (origin, .schema body)) :
    firing.target.inventory.rows occurrence =
      ContextualPublication.extendPrivate (Expanded locals inners) firing.update.declaration
        (stored locals inners before.declarations
          (captureValues locals inners before.declarations firing.update firing.scope) origin body) := by
  change firing.publishedRows occurrence = _
  rw [publishedRows, selected]

theorem ordinary_row (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (value : Term (signature S (Actor locals before.declarations)) Γ sort)
    (selected : firing.descriptor occurrence = some (origin, .ordinary value)) :
    firing.target.inventory.rows occurrence =
      ContextualPublication.ordinary (Expanded locals inners) firing.update.declaration
        (instantiate firing.update.answer (firing.execution.outputs occurrence)) := by
  have made := assign_mem firing.selection.made (firing.sourceRule.descriptors locals inners before.declarations)
    occurrence (origin, .ordinary value) selected
  change firing.publishedRows occurrence = _
  rw [publishedRows, selected]
  apply (defaultPublication firing).ordinary_row made
  change ordinaryFlag firing occurrence = true
  simp only [ordinaryFlag, selected]

theorem shared_row (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (value : Term (signature S (Actor locals before.declarations)) Γ sort)
    (selected : firing.descriptor occurrence = some (origin, .shared value)) :
    firing.target.inventory.rows occurrence = ContextualStoredRows.Row.shared
      (instantiate (ContextualComputedFreshFrame.includeSource firing.update) (firing.execution.outputs occurrence)) := by
  have made := assign_mem firing.selection.made (firing.sourceRule.descriptors locals inners before.declarations)
    occurrence (origin, .shared value) selected
  change firing.publishedRows occurrence = _
  rw [publishedRows, selected]
  apply (defaultPublication firing).shared_row made
  change ordinaryFlag firing occurrence = false
  simp only [ordinaryFlag, selected]

theorem retained_row (firing : Firing locals inners before) (occurrence : O)
    (notMade : occurrence ∉ firing.selection.made) :
    firing.target.inventory.rows occurrence = ContextualPublication.extendPrivate (Expanded locals inners)
      firing.update.declaration
      ((ContextualExecution.computedTarget (Expanded locals inners) before firing.execution.rule firing.selection
        firing.execution.outputs firing.execution.ruleCovered firing.execution.admitted firing.update).inventory.rows occurrence) := by
  have none : firing.descriptor occurrence = none := by
    cases found : firing.descriptor occurrence with
    | none => rfl
    | some value =>
        exact False.elim (notMade (assign_mem firing.selection.made
          (firing.sourceRule.descriptors locals inners before.declarations) occurrence value found))
  change firing.publishedRows occurrence = _
  rw [publishedRows, none]
  exact (defaultPublication firing).retained_row notMade

theorem schema_matches_source (firing : Firing locals inners before) (occurrence : O) (origin : Nat)
    (body : Term (signature S (Blueprint locals inners before.declarations)) Γ sort)
    (selected : firing.descriptor occurrence = some (origin, .schema body))
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    ContextualGuardMatching.Matches
        (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration)
        candidate pattern (firing.target.inventory.rows occurrence) ↔
      ContextualGuardMatching.Matches inners
        (Assignment.compose candidate (captureValues locals inners before.declarations firing.update firing.scope))
        pattern (.schema body) := by
  rw [firing.schema_row occurrence origin body selected]
  exact (ContextualPublication.extendPrivate_matches_iff (Expanded locals inners) firing.update.declaration
    candidate pattern _).trans
      (stored_matches_iff locals inners before.declarations _ origin candidate body pattern)

theorem physical_result (firing : Firing locals inners before) :
    firing.target.inventory.configuration.present =
      MeTTaCalculus.OccurrenceCommits.fire before.inventory.configuration.present
        (firing.selection.commit (T := Unit)) := rfl

theorem native_equations (firing : Firing locals inners before) :
    firing.target.inventory.configuration.equations =
      (ContextualTransportedActivation.result (Expanded locals inners) before.declarations
        (ContextualComputedFreshFrame.includeSource firing.update) before.occupied firing.selection firing.execution.rule
          before.inventory.rows before.inventory.configuration).equations := rfl

end Firing

/-- The authored rule and semantic admission construct an actual solver
execution with its template publication. No computed update is a premise. -/
theorem realize_source_publication
    (before : ContextualExecution.Endpoint (Expanded locals inners) O Γ sort)
    (rule : ContextualTemplateSource.Rule locals inners before.declarations Γ sort)
    (selection : Selection O)
    (outputs : O → Term (signature S (Active locals inners before.declarations)) Γ sort)
    (covered : RuleCovered (privateScopes before.scopes) before.occupied (rule.lower locals inners before.declarations))
    (admitted : ContextualGuardedStep.Valid (Expanded locals inners) before.declarations
      before.occupied selection (rule.lower locals inners before.declarations) before.inventory.rows
      before.inventory.configuration outputs)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem (Expanded locals inners) before.declarations before.occupied selection
        (rule.lower locals inners before.declarations) before.inventory.rows before.inventory.configuration))) :
    ∃ firing : Firing locals inners before, firing.sourceRule = rule ∧ firing.selection = selection ∧
      firing.execution.outputs = outputs := by
  obtain ⟨after, execution, compiled, selected, outputEq⟩ :=
    ContextualExecution.realize_semantic_admission (Expanded locals inners) before
      (rule.lower locals inners before.declarations) selection outputs covered admitted patterned
  exact ⟨⟨rule, after, execution, compiled⟩, rfl, selected, outputEq⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication
