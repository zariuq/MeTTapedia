import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationExecution

/-!
# Reach admission constructs reusable publication in the same event

Publication follows the existing completed activation. The located rule,
physical selection, source equations and guards are the same ones admitted
by actor reach. Reusable payload variables are copied from the computed
answer, while the destination remains the resolved space name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {point : S.Srt} {Name Local V Shared O : Type}
    (locals : Local → MetaArity (base S point Name))
    {declaration : V → MetaArity (base S point Name)}
    {captures : Shared → MetaArity (base S point Name)}

theorem ordinary_keeps_the_space_name (n : Name) (payload : Closed declaration) :
    (ContextualPublication.ordinary locals declaration (place (name n) payload) :
      ContextualStoredRows.Row _ captures [] point) =
      locatedRow (ContextualPublication.privateFamily locals declaration) captures (name n)
        (ContextualPublication.ordinary locals declaration payload) := rfl

theorem completed_resolves_destination
    {problem : EquationStore (Closed declaration)}
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem problem))
    (finished : update.remaining = []) {address : Closed declaration} {n : Name}
    (resolved : ResolvesTo problem address n) : instantiate update.answer address = name n :=
  resolved update.declaration update.answer
    ((ContextualResidual.models_observeProblem update.answer problem).mp (update.completed finished))

theorem ordinary_completed_destination
    {problem : EquationStore (Closed declaration)}
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem problem))
    (finished : update.remaining = []) {address : Closed declaration} (payload : Closed declaration) {n : Name}
    (resolved : ResolvesTo problem address n) :
    (ContextualPublication.ordinary locals update.declaration (instantiate update.answer (place address payload)) :
      ContextualStoredRows.Row _ captures [] point) =
      locatedRow (ContextualPublication.privateFamily locals update.declaration) captures (name n)
        (ContextualPublication.ordinary locals update.declaration (instantiate update.answer payload)) := by
  rw [instantiate_place,completed_resolves_destination update finished resolved]
  exact ordinary_keeps_the_space_name locals n _

variable [DecidableEq Name] [DecidableEq O] [DecidableEq Local]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- A source inventory's located interpretation and reach admission suffice
to build an actual publication firing; no solver return is supplied. -/
theorem realize_publication
    (before : ContextualExecution.Endpoint locals O [] point) (selection : Selection O)
    (addresses : O → Closed before.declarations)
    (payloads : O → ContextualStoredRows.Row locals before.declarations [] point)
    (located : before.inventory.rows = placedRows locals before.declarations addresses payloads)
    (rule : NamedSpaces.LocatedRule (Closed (ContextualSelectionViews.source locals before.declarations)))
    (known : Set (ActiveTerm locals before.declarations)) (written : Set Name)
    (outputs : O → ActiveTerm locals before.declarations) (reusable : O → Bool)
    (covered : ContextualWorldScopeLedger.RuleCovered (ContextualScopeSupport.privateScopes before.scopes)
      before.occupied (rule.toRule (spaceTerms (ContextualSelectionViews.source locals before.declarations))))
    (admitted : Admits locals before.declarations before.occupied selection known written addresses payloads
      before.inventory.configuration (freshLocated locals before.declarations before.occupied selection rule) outputs)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (eventProblem locals before.declarations before.occupied selection addresses payloads before.inventory.configuration
        (freshLocated locals before.declarations before.occupied selection rule)))) :
    ∃ firing : ContextualPublication.Firing (before := before),
      firing.rule = rule.toRule (spaceTerms (ContextualSelectionViews.source locals before.declarations)) ∧
        firing.selection = selection ∧ firing.outputs = outputs ∧ firing.reusable = reusable := by
  have semantic : ContextualGuardedStep.Valid locals before.declarations before.occupied selection
      (rule.toRule (spaceTerms (ContextualSelectionViews.source locals before.declarations)))
      before.inventory.rows before.inventory.configuration outputs := by
    rw [located]
    exact admitted.semantic_admission
  apply ContextualPublication.realize_publication locals before _ selection outputs reusable covered semantic
  rw [located,← event_problem_is_actual_preparation]
  exact patterned

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach
