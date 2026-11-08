import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationInventory
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldScopeLedger

/-!
# Publication retains the existing finite scope inventory

Extending the private bank transports existing templates and rows. New
private indices introduce no shared captures before a later use opens them.
A reusable solved value therefore needs no shared-variable scope of its own;
its rigid syntax, object binders and repeated private variables remain data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualScopeSupport ContextualWorldScopeLedger

universe u
variable {S : Signature} {Local V Shared : Type} {O : Type u}
    (locals : Local → MetaArity S) (declaration : V → MetaArity S)
    (captures : Shared → MetaArity S)

theorem asTemplate_extendPrivate {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    ContextualStoredRows.asTemplate (privateFamily locals declaration) captures (extendPrivate locals declaration row) =
      instantiate (includePrivate locals declaration) (ContextualStoredRows.asTemplate locals captures row) := by
  cases row with
  | schema body => rfl
  | shared value =>
      dsimp only [extendPrivate,ContextualStoredRows.asTemplate]
      rw [instantiate_comp]
      congr 1
      funext identity
      exact (instantiate_generator (includePrivate locals declaration) (.inr identity)).symm

theorem includePrivate_respects (scopes : Shared → Finset Nat) :
    Respects (privateScopes (Local := Local) scopes)
      (privateScopes (Local := Local ⊕ V) scopes) (includePrivate locals declaration (captures := captures)) := by
  intro identity
  cases identity with
  | inl identity =>
      change term (privateScopes scopes)
        (generator (ContextualSelectionViews.source (privateFamily locals declaration) captures) (.inl (.inl identity))) ⊆ ∅
      rw [term_generator]
      exact Finset.Subset.refl _
  | inr identity =>
      change term (privateScopes scopes)
        (generator (ContextualSelectionViews.source (privateFamily locals declaration) captures) (.inr identity)) ⊆ scopes identity
      rw [term_generator]
      exact Finset.Subset.refl _

theorem row_extendPrivate_covered (scopes : Shared → Finset Nat) {occupied : Finset Nat}
    {Γ : Ctx S} {sort : S.Srt} (value : ContextualStoredRows.Row locals captures Γ sort)
    (covered : row locals captures scopes value ⊆ occupied) :
    row (privateFamily locals declaration) captures scopes (extendPrivate locals declaration value) ⊆ occupied := by
  unfold row
  rw [asTemplate_extendPrivate]
  exact covered_instantiate_of_respects _ _ occupied _ (includePrivate_respects locals declaration captures scopes) covered

theorem ordinary_covered (scopes : Shared → Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S declaration) Γ sort) :
    row (privateFamily locals declaration) captures scopes (ordinary locals declaration value) ⊆ ∅ := by
  unfold row ordinary ContextualStoredRows.store ContextualStoredRows.asTemplate
  apply covered_instantiate (privateScopes scopes) ∅
  intro identity _
  change term (privateScopes scopes)
    (generator (ContextualSelectionViews.source (privateFamily locals declaration) captures) (.inl identity)) ⊆ ∅
  rw [term_generator]
  exact Finset.Subset.refl _

def extendInventory {Γ : Ctx S} {sort : S.Srt}
    (inventory : Inventory locals captures (O := O) Γ sort) :
    Inventory (privateFamily locals declaration) captures (O := O) Γ sort where
  configuration := inventory.configuration
  rows occurrence := extendPrivate locals declaration (inventory.rows occurrence)
  retained := inventory.retained
  templates := inventory.templates.map (instantiateObservation (includePrivate locals declaration))

theorem extendInventory_covered (scopes : Shared → Finset Nat) {occupied : Finset Nat}
    {Γ : Ctx S} {sort : S.Srt} (inventory : Inventory locals captures (O := O) Γ sort)
    (covered : CoveredWorld locals captures scopes occupied inventory) :
    CoveredWorld (privateFamily locals declaration) captures scopes occupied
      (extendInventory locals declaration captures inventory) := by
  refine ⟨covered.equations,?_,covered.retained,?_⟩
  · intro occurrence present
    exact row_extendPrivate_covered locals declaration captures scopes (inventory.rows occurrence)
      (covered.rows occurrence present)
  · exact observations_map _ _ occupied _ (includePrivate_respects locals declaration captures scopes)
      inventory.templates covered.templates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication
