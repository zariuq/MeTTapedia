import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRowOrigins
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching

/-!
# Fixed-scope contextual views commute with capture-interface transport

Private row and rule names keep their chosen use scopes. Captures follow the
given assignment, including values exported by earlier producers. These are
forward representation laws for arbitrary assignments, not reflection of
asks through binding substitutions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualViewNaturality

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

variable {S : Signature} {Local Shared Next : Type}
  (locals : Local → MetaArity S) {captures : Shared → MetaArity S} {next : Next → MetaArity S}

def activeLift (change : Assignment captures next) :
    Assignment (ContextualActivatedStep.target locals captures) (ContextualActivatedStep.target locals next) :=
  ContextualStoredRows.liftCaptures (fun name : ScopedVar Local => locals name.name) change

theorem capture_square (change : Assignment captures next) :
    Assignment.compose (activeLift locals change) (ContextualSelectionViews.capturedTarget locals captures) =
      Assignment.compose (ContextualSelectionViews.capturedTarget locals next) change := by
  funext name
  change instantiate (activeLift locals change)
      (generator (ContextualActivatedStep.target locals captures) (.inr name)) = _
  rw [instantiate_generator]
  rfl

theorem freshening_square (change : Assignment captures next) (scope : Nat) :
    Assignment.compose (activeLift locals change) (ContextualFreshening.assignment locals captures scope) =
      Assignment.compose (ContextualFreshening.assignment locals next scope) (ContextualStoredRows.liftCaptures locals change) := by
  funext name
  cases name with
  | inl name =>
      change instantiate (activeLift locals change)
          (generator (ContextualActivatedStep.target locals captures) (.inl (ScopedVar.at scope name))) =
        instantiate (ContextualFreshening.assignment locals next scope)
          (generator (ContextualActivatedStep.source locals next) (.inl name))
      rw [instantiate_generator, instantiate_generator]
      rfl
  | inr name =>
      change instantiate (activeLift locals change)
          (generator (ContextualActivatedStep.target locals captures) (.inr name)) =
        instantiate (ContextualFreshening.assignment locals next scope)
          (instantiate (ContextualSelectionViews.capturedSource locals next) (change name))
      rw [instantiate_generator]
      exact ContextualStoredRows.viewAt_eq_freshening locals next scope (.shared (change name))

theorem termAt_transport (change : Assignment captures next) (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (body : Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort) :
    instantiate (activeLift locals change) (ContextualFreshening.termAt locals captures scope body) =
      ContextualFreshening.termAt locals next scope
        (instantiate (ContextualStoredRows.liftCaptures locals change) body) := by
  unfold ContextualFreshening.termAt
  rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, freshening_square]

theorem viewAt_transport (change : Assignment captures next) (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    instantiate (activeLift locals change) (ContextualStoredRows.viewAt locals captures scope row) =
      ContextualStoredRows.viewAt locals next scope (row.map locals change) := by
  cases row with
  | schema body => exact termAt_transport locals change scope body
  | shared value =>
      exact ContextualStoredRows.liftCaptures_on_shared_value
        (fun name : ScopedVar Local => locals name.name) change value

theorem guardRows_transport {O : Type} (change : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    (fun occurrence => (ContextualGuardedStep.guardRows locals captures rows occurrence).map locals
      (activeLift locals change)) =
      ContextualGuardedStep.guardRows locals next (fun occurrence => (rows occurrence).map locals change) := by
  funext occurrence
  change ((rows occurrence).map locals (ContextualSelectionViews.capturedTarget locals captures)).map locals _ =
    ((rows occurrence).map locals change).map locals (ContextualSelectionViews.capturedTarget locals next)
  rw [ContextualStoredRows.Row.map_compose, ContextualStoredRows.Row.map_compose, capture_square]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualViewNaturality
