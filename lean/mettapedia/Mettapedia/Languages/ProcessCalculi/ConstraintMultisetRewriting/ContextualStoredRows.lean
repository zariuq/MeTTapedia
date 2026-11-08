import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViews
import Mettapedia.OSLF.Syntax.ContextualFamilyComposition

/-!
# Stored contextual schemas and shared values

Row metadata records whether a common binding term has private schematic
locals or already belongs to the shared capture frame. Opening a schema uses
one fresh scope for the whole term. Opening a shared value only embeds its
existing identities. This metadata introduces no new term constructors.

Changing the shared declaration frame transports retained shared values and the
captures of retained schemas. Schema locals stay private. In particular a
later schema may capture a variable created by an earlier rule activation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRows

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Local Shared Next Later : Type}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

inductive Row (context : Ctx S) (sort : S.Srt) where
  | schema : Term (signature S (ContextualSelectionViews.source locals captures)) context sort → Row context sort
  | shared : Term (signature S captures) context sort → Row context sort

def asTemplate {Γ : Ctx S} {sort : S.Srt} :
    Row locals captures Γ sort →
      Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort
  | .schema body => body
  | .shared value => instantiate (ContextualSelectionViews.capturedSource locals captures) value

def viewAt (scope : Nat) {Γ : Ctx S} {sort : S.Srt} :
    Row locals captures Γ sort →
      Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort
  | .schema body => ContextualFreshening.termAt locals captures scope body
  | .shared value => instantiate (ContextualSelectionViews.capturedTarget locals captures) value

theorem viewAt_eq_freshening (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (row : Row locals captures Γ sort) :
    viewAt locals captures scope row = ContextualFreshening.termAt locals captures scope
      (asTemplate locals captures row) := by
  cases row with
  | schema body => rfl
  | shared value =>
      symm
      dsimp only [viewAt, asTemplate, ContextualFreshening.termAt]
      rw [instantiate_comp]
      have same : (fun name => instantiate (ContextualFreshening.assignment locals captures scope)
          (ContextualSelectionViews.capturedSource locals captures name)) =
          ContextualSelectionViews.capturedTarget locals captures := by
        funext name
        exact instantiate_generator (ContextualFreshening.assignment locals captures scope) (Sum.inr name)
      rw [same]

variable {captures} {next : Next → MetaArity S} {later : Later → MetaArity S}

def liftCaptures (assignment : Assignment captures next) :
    Assignment (ContextualSelectionViews.source locals captures)
      (ContextualSelectionViews.source locals next)
  | .inl name => generator (ContextualSelectionViews.source locals next) (.inl name)
  | .inr name => instantiate (ContextualSelectionViews.capturedSource locals next) (assignment name)

theorem liftCaptures_on_shared_value (assignment : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S captures) Γ sort) :
    instantiate (liftCaptures locals assignment)
        (instantiate (ContextualSelectionViews.capturedSource locals captures) value) =
      instantiate (ContextualSelectionViews.capturedSource locals next) (instantiate assignment value) := by
  rw [instantiate_comp, instantiate_comp]
  congr 1
  funext name
  exact instantiate_generator (liftCaptures locals assignment) (Sum.inr name)

def Row.map (assignment : Assignment captures next) {Γ : Ctx S} {sort : S.Srt} :
    Row locals captures Γ sort → Row locals next Γ sort
  | .schema body => .schema (instantiate (liftCaptures locals assignment) body)
  | .shared value => .shared (instantiate assignment value)

theorem asTemplate_map (assignment : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    asTemplate locals next (row.map locals assignment) =
      instantiate (liftCaptures locals assignment) (asTemplate locals captures row) := by
  cases row with
  | schema body => rfl
  | shared value => exact (liftCaptures_on_shared_value locals assignment value).symm

theorem liftCaptures_identity :
    liftCaptures locals (generator captures) =
      generator (ContextualSelectionViews.source locals captures) := by
  funext name
  cases name with
  | inl name => rfl
  | inr name => exact instantiate_generator (ContextualSelectionViews.capturedSource locals captures) name

theorem liftCaptures_compose (first : Assignment captures next) (second : Assignment next later) :
    Assignment.compose (liftCaptures locals second) (liftCaptures locals first) =
      liftCaptures locals (Assignment.compose second first) := by
  funext name
  cases name with
  | inl name => exact instantiate_generator (liftCaptures locals second) (.inl name)
  | inr name => exact liftCaptures_on_shared_value locals second (first name)

theorem Row.map_identity {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    row.map locals (generator captures) = row := by
  cases row with
  | schema body => simp only [Row.map, liftCaptures_identity, instantiate_identity]
  | shared value => simp only [Row.map, instantiate_identity]

theorem Row.map_compose (first : Assignment captures next) (second : Assignment next later)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    (row.map locals first).map locals second = row.map locals (Assignment.compose second first) := by
  cases row with
  | schema body =>
      simp only [Row.map, instantiate_comp]
      congr 1
      exact congrArg (fun assignment => instantiate assignment body) (liftCaptures_compose locals first second)
  | shared value => exact congrArg Row.shared (instantiate_comp first second value)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRows
