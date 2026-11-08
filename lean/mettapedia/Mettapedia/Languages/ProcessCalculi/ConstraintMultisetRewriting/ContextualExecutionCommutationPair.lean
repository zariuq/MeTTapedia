import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationInventory

/-! # Both actual producer orders in their complete two-return declaration frame -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualWorldScopeLedger
open ContextualExecutionCommutationNames

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt} {before : Endpoint locals O Γ sort}

namespace Producer

def twoTarget (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) : Endpoint locals O Γ sort :=
  (first.after second empty separate).target (first.target_empty empty)

def earlierTerm (producer : Producer before) (occurrence : O) :
    Term (signature S (twiceDeclarations locals before.declarations)) Γ sort :=
  instantiate (intoEarlier locals before.declarations (ContextualActivationScopes.start before.occupied))
    (producer.value occurrence)

def laterTerm (producer : Producer before) (occurrence : O) :
    Term (signature S (twiceDeclarations locals before.declarations)) Γ sort :=
  instantiate (intoLater locals before.declarations (ContextualActivationScopes.start (nextLedger before.occupied)))
    (producer.value occurrence)

theorem two_target_rows (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) (occurrence : O) :
    (first.twoTarget second empty separate).inventory.rows occurrence =
      if occurrence ∈ second.made then .shared (second.laterTerm occurrence)
      else if occurrence ∈ first.made then .shared (first.earlierTerm occurrence)
      else (before.inventory.rows occurrence).map locals (intoOldCaptures locals before.declarations) := by
  dsimp only [twoTarget]
  rw [target_rows]
  simp only [after]
  split_ifs with inSecond inFirst
  · change ContextualStoredRows.Row.shared (instantiate _ (instantiate _ _)) = _
    rw [← Assignment.instantiate_compose]
    exact congrArg (fun change => ContextualStoredRows.Row.shared (locals := locals)
      (instantiate change (second.value occurrence)))
      (captured_then_created locals before.declarations (ContextualActivationScopes.start (nextLedger before.occupied)))
  · rw [target_rows, if_pos inFirst]
    change ContextualStoredRows.Row.shared (instantiate _ (instantiate _ _)) = _
    rw [← Assignment.instantiate_compose]
    exact congrArg (fun change => ContextualStoredRows.Row.shared (locals := locals)
      (instantiate change (first.value occurrence)))
      (created_then_captured locals before.declarations (ContextualActivationScopes.start before.occupied))
  · rw [target_rows, if_neg inFirst, ContextualStoredRows.Row.map_compose]
    exact congrArg (fun change => (before.inventory.rows occurrence).map locals change)
      (twice_captured locals before.declarations)

theorem two_target_world (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    (first.twoTarget second empty separate).inventory.configuration.present =
      before.inventory.configuration.present ∪ first.made.toFinset ∪ second.made.toFinset := by
  dsimp only [twoTarget]
  rw [target_world, target_world]
  rfl

theorem two_target_equations (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    (first.twoTarget second empty separate).inventory.configuration.equations = [] :=
  (first.after second empty separate).target_empty (first.target_empty empty)

theorem two_target_retained (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    (first.twoTarget second empty separate).inventory.retained =
      before.inventory.retained.map (instantiateObservation (intoOldCaptures locals before.declarations)) ++
        first.made.map (fun occurrence => observe (first.earlierTerm occurrence)) ++
          second.made.map (fun occurrence => observe (second.laterTerm occurrence)) := by
  dsimp only [twoTarget]
  rw [target_retained, target_retained, List.map_append]
  apply congrArg₂ List.append
  · apply congrArg₂ List.append
    · rw [List.map_map]
      apply List.map_congr_left
      intro value _member
      rw [Function.comp_apply, instantiateObservation_comp]
      exact congrArg (fun change => instantiateObservation change value) (twice_captured locals before.declarations)
    · rw [List.map_map]
      apply List.map_congr_left
      intro occurrence _member
      change observe (instantiate _ (instantiate _ _)) = _
      rw [← Assignment.instantiate_compose]
      exact congrArg (fun change => observe (instantiate change (first.value occurrence)))
        (created_then_captured locals before.declarations (ContextualActivationScopes.start before.occupied))
  · apply List.map_congr_left
    intro occurrence _member
    change observe (instantiate _ (instantiate _ _)) = _
    rw [← Assignment.instantiate_compose]
    exact congrArg (fun change => observe (instantiate change (second.value occurrence)))
      (captured_then_created locals before.declarations (ContextualActivationScopes.start (nextLedger before.occupied)))

theorem two_target_templates (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    (first.twoTarget second empty separate).inventory.templates = before.inventory.templates.map
      (instantiateObservation (ContextualStoredRows.liftCaptures locals (intoOldCaptures locals before.declarations))) := by
  dsimp only [twoTarget]
  rw [target_templates, target_templates, List.map_map]
  apply List.map_congr_left
  intro value _member
  rw [Function.comp_apply, instantiateObservation_comp, ContextualStoredRows.liftCaptures_compose]
  exact congrArg (fun change => instantiateObservation (ContextualStoredRows.liftCaptures locals change) value)
    (twice_captured locals before.declarations)

theorem two_target_ledger (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    (first.twoTarget second empty separate).occupied = nextLedger (nextLedger before.occupied) := rfl

end Producer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation
