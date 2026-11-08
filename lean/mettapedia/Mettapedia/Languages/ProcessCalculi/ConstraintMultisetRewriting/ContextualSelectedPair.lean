import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedNames

/-! # Complete inventories of both actual selected-firing orders -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualScopeSupport ContextualWorldScopeLedger
open ContextualSelectedNormalization ContextualExecutionCommutationNames
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt} {before : Endpoint locals O Γ sort}

namespace Interaction

def count (interaction : Interaction before) := ContextualActivationScopes.count interaction.selection

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem count_positive (interaction : Interaction before) : 0 < interaction.count := by
  simp [count, ContextualActivationScopes.count]

def earlierValue (interaction : Interaction before) (occurrence : O) :
    Term (signature S (twiceDeclarations locals before.declarations)) Γ sort :=
  instantiate (intoEarlier locals before.declarations (ContextualActivationScopes.start before.occupied))
    (interaction.value occurrence)

def laterValue (first second : Interaction before) (occurrence : O) :
    Term (signature S (twiceDeclarations locals before.declarations)) Γ sort :=
  instantiate (intoLater locals before.declarations
    (ContextualActivationScopes.start (ContextualSelectedScopes.advance before.occupied first.count)))
    (second.value occurrence)

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem rootValues_map {V W : Type} (source : V → MetaArity S) (target : W → MetaArity S)
    (change : Assignment source target)
    (values : Assignment (ContextualSelectionViews.source locals before.declarations) source)
    (interaction : Interaction before) :
    (interaction.rootValues source values).map (instantiateObservation change) =
      interaction.rootValues target (Assignment.compose change values) := by
  rw [rootValues, List.map_append, List.map_map, List.map_map]
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro value _member
    exact congrArg observe (Rigid.instantiate_include change value)
  · apply List.map_congr_left
    intro occurrence _member
    exact congrArg observe (Assignment.instantiate_compose change values (interaction.value occurrence)).symm

theorem after_rootValues (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) :
    (first.after second prior incoming survives).rootValues
        (twiceDeclarations locals before.declarations)
        (intoCreated locals (declarations locals before.declarations)
          (ContextualActivationScopes.start (ContextualSelectedScopes.advance before.occupied first.count))) =
      second.rootValues (twiceDeclarations locals before.declarations)
        (intoLater locals before.declarations
          (ContextualActivationScopes.start (ContextualSelectedScopes.advance before.occupied first.count))) := by
  apply congrArg₂ List.append rfl
  apply List.map_congr_left
  intro occurrence _member
  change observe (instantiate _ (instantiate _ _)) = _
  rw [← Assignment.instantiate_compose]
  exact congrArg (fun change => observe (instantiate change (second.value occurrence)))
    (captured_then_created locals before.declarations _)

theorem two_target_rows (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) (occurrence : O) :
    (first.twoTarget second prior incoming survives).inventory.rows occurrence =
      if occurrence ∈ second.made then .shared (first.laterValue second occurrence)
      else if occurrence ∈ first.made then .shared (first.earlierValue occurrence)
      else (before.inventory.rows occurrence).map locals (intoOldCaptures locals before.declarations) := by
  dsimp only [twoTarget]
  rw [target_rows]
  simp only [after]
  split_ifs with inSecond inFirst
  · change ContextualStoredRows.Row.shared (instantiate _ (instantiate _ _)) = _
    rw [← Assignment.instantiate_compose]
    exact congrArg (fun change => ContextualStoredRows.Row.shared (locals := locals)
      (instantiate change (second.value occurrence))) (captured_then_created locals before.declarations _)
  · rw [target_rows, if_pos inFirst]
    change ContextualStoredRows.Row.shared (instantiate _ (instantiate _ _)) = _
    rw [← Assignment.instantiate_compose]
    exact congrArg (fun change => ContextualStoredRows.Row.shared (locals := locals)
      (instantiate change (first.value occurrence))) (created_then_captured locals before.declarations _)
  · rw [target_rows, if_neg inFirst, ContextualStoredRows.Row.map_compose]
    exact congrArg (fun change => (before.inventory.rows occurrence).map locals change)
      (twice_captured locals before.declarations)

theorem two_target_equations (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) :
    (first.twoTarget second prior incoming survives).inventory.configuration.equations =
      diagonals (twiceDeclarations locals before.declarations) (second.terms (first.terms prior)) :=
  (first.after second prior incoming survives).target_equations _ (first.target_equations prior incoming)

theorem two_target_retained (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) :
    (first.twoTarget second prior incoming survives).inventory.retained =
      before.inventory.retained.map (instantiateObservation (intoOldCaptures locals before.declarations)) ++
        first.rootValues (twiceDeclarations locals before.declarations)
          (intoEarlier locals before.declarations (ContextualActivationScopes.start before.occupied)) ++
        second.rootValues (twiceDeclarations locals before.declarations)
          (intoLater locals before.declarations
            (ContextualActivationScopes.start (ContextualSelectedScopes.advance before.occupied first.count))) := by
  dsimp only [twoTarget]
  rw [target_retained, target_retained, List.map_append]
  apply congrArg₂ List.append
  · apply congrArg₂ List.append
    · rw [List.map_map]
      apply List.map_congr_left
      intro value _member
      rw [Function.comp_apply, instantiateObservation_comp]
      exact congrArg (fun change => instantiateObservation change value) (twice_captured locals before.declarations)
    · have moved := rootValues_map (declarations locals before.declarations) (twiceDeclarations locals before.declarations)
        (intoCapture locals (declarations locals before.declarations)) (intoCreated locals before.declarations first.scope) first
      exact moved.trans (congrArg (first.rootValues (twiceDeclarations locals before.declarations))
        (created_then_captured locals before.declarations _))
  · exact after_rootValues first second prior incoming survives

theorem two_target_templates (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) :
    (first.twoTarget second prior incoming survives).inventory.templates = before.inventory.templates.map
      (instantiateObservation (ContextualStoredRows.liftCaptures locals (intoOldCaptures locals before.declarations))) := by
  dsimp only [twoTarget]
  rw [target_templates, target_templates, List.map_map]
  apply List.map_congr_left
  intro value _member
  rw [Function.comp_apply, instantiateObservation_comp, ContextualStoredRows.liftCaptures_compose]
  exact congrArg (fun change => instantiateObservation (ContextualStoredRows.liftCaptures locals change) value)
    (twice_captured locals before.declarations)

theorem two_target_world (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) :
    (first.twoTarget second prior incoming survives).inventory.configuration.present =
      fire (fire before.inventory.configuration.present (first.selection.commit (T := Unit)))
        (second.selection.commit (T := Unit)) := rfl

theorem two_target_ledger (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) :
    (first.twoTarget second prior incoming survives).occupied =
      ContextualSelectedScopes.advance (ContextualSelectedScopes.advance before.occupied first.count) second.count := rfl

end Interaction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution
