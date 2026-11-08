import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplateExecution

/-!
# Located reach admission constructs selectively captured template outputs

The located source interpretation and the three-way output metadata meet
at the existing contextual execution owner. Read and write authority remain
the same admission obligations; constructing a template adds no permission
primitive or forwarding transition. Private declaration-bank extension is
an inventory reindexing with unchanged configurations and old row meanings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualTemplateSource

variable {S : Signature} {Local Inner O : Type}
    (locals : Local → MetaArity S) (inners : Inner → MetaArity S) {Γ : Ctx S} {sort : S.Srt}

def prepareEndpoint (before : ContextualExecution.Endpoint locals O Γ sort) :
    ContextualExecution.Endpoint (Expanded locals inners) O Γ sort where
  Names := before.Names
  equality := before.equality
  declarations := before.declarations
  scopes := before.scopes
  occupied := before.occupied
  inventory := ContextualPublication.extendInventory locals (Templates inners) before.declarations before.inventory
  covered := ContextualPublication.extendInventory_covered locals (Templates inners) before.declarations
    before.scopes before.inventory before.covered

theorem prepare_keeps_configuration (before : ContextualExecution.Endpoint locals O Γ sort) :
    (prepareEndpoint locals inners before).inventory.configuration = before.inventory.configuration := rfl

theorem prepare_keeps_row_instances (before : ContextualExecution.Endpoint locals O Γ sort)
    (occurrence : O) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment before.declarations next) (pattern : Term (signature S next) Γ sort) :
    ContextualGuardMatching.Matches (Expanded locals inners) candidate pattern
        ((prepareEndpoint locals inners before).inventory.rows occurrence) ↔
      ContextualGuardMatching.Matches locals candidate pattern (before.inventory.rows occurrence) :=
  ContextualPublication.extendPrivate_matches_iff locals (Templates inners) candidate pattern _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualTemplateSource

variable {S : Signature} {point : S.Srt} {Name Local Inner O : Type}
    (locals : Local → MetaArity (base S point Name)) (inners : Inner → MetaArity (base S point Name))
    [DecidableEq Name] [DecidableEq O] [DecidableEq Local] [DecidableEq Inner]
    [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

theorem realize_template_publication
    (before : ContextualExecution.Endpoint (Expanded locals inners) O [] point) (selection : Selection O)
    (addresses : O → Closed before.declarations)
    (payloads : O → ContextualStoredRows.Row (Expanded locals inners) before.declarations [] point)
    (located : before.inventory.rows = placedRows (Expanded locals inners) before.declarations addresses payloads)
    (sourceRule : ContextualTemplateSource.Rule locals inners before.declarations [] point)
    (locatedRule : NamedSpaces.LocatedRule
      (Closed (ContextualSelectionViews.source (Expanded locals inners) before.declarations)))
    (lowered : sourceRule.lower locals inners before.declarations = locatedRule.toRule
      (spaceTerms (ContextualSelectionViews.source (Expanded locals inners) before.declarations)))
    (known : Set (ActiveTerm (Expanded locals inners) before.declarations)) (written : Set Name)
    (outputs : O → ActiveTerm (Expanded locals inners) before.declarations)
    (covered : ContextualWorldScopeLedger.RuleCovered (ContextualScopeSupport.privateScopes before.scopes)
      before.occupied (sourceRule.lower locals inners before.declarations))
    (admitted : Admits (Expanded locals inners) before.declarations before.occupied selection known written addresses payloads
      before.inventory.configuration (freshLocated (Expanded locals inners) before.declarations before.occupied selection locatedRule)
      outputs)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (eventProblem (Expanded locals inners) before.declarations before.occupied selection addresses payloads
        before.inventory.configuration (freshLocated (Expanded locals inners) before.declarations before.occupied selection locatedRule)))) :
    ∃ firing : ContextualTemplatePublication.Firing locals inners before,
      firing.sourceRule = sourceRule ∧ firing.selection = selection ∧ firing.execution.outputs = outputs := by
  have semantic : ContextualGuardedStep.Valid (Expanded locals inners) before.declarations
      before.occupied selection (sourceRule.lower locals inners before.declarations) before.inventory.rows
      before.inventory.configuration outputs := by
    rw [lowered, located]
    exact admitted.semantic_admission
  apply ContextualTemplatePublication.realize_source_publication locals inners before sourceRule selection outputs covered semantic
  rw [lowered, located, ← event_problem_is_actual_preparation]
  exact patterned

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach
