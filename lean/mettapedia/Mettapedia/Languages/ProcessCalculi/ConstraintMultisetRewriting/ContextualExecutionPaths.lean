import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionEndpoints
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Mathlib paths present existing completed contextual admissions

Edges retain the original raw rule, selected physical rows, actual worklist
return and computed family-changing inventory target. Free paths add no
transition rule and identify no event orders. Physical selections and helper
reservations remain visible along composition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local : Type} (locals : Local → MetaArity S) (O : Type)
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}

instance graph : Quiver (Endpoint locals O Γ sort) where
  Hom := Firing locals

namespace Firing

variable {locals O} {before after : Endpoint locals O Γ sort}

theorem occupied_subset (firing : Firing locals before after) : before.occupied ⊆ after.occupied := by
  rw [firing.actual_helper_ledger]
  exact (ContextualActivationScopes.old_scopes_retained before.occupied firing.selection).trans
    (ContextualFreshFrameScopeLedger.old_scopes_retained _)

theorem physical_result (firing : Firing locals before after) :
    after.inventory.configuration.present =
      fire before.inventory.configuration.present
        (firing.selection.commit (T := Term (signature S after.declarations) Γ sort)) :=
  congrArg (fun endpoint => endpoint.inventory.configuration.present) firing.destination

end Firing

variable {locals O}

def selections {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    Quiver.Path source target → List (Selection O)
  | _, .nil => []
  | _, .cons past edge => selections past ++ [edge.selection]

def fuels {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    Quiver.Path source target → List Nat
  | _, .nil => []
  | _, .cons past edge => fuels past ++ [edge.fuel]

theorem selections_comp {source middle target : Endpoint locals O Γ sort}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    selections (first.comp second) = selections first ++ selections second := by
  induction second with
  | nil => simp [Quiver.Path.comp, selections]
  | cons past edge earlier => simp [Quiver.Path.comp, selections, earlier, List.append_assoc]

theorem fuels_comp {source middle target : Endpoint locals O Γ sort}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    fuels (first.comp second) = fuels first ++ fuels second := by
  induction second with
  | nil => simp [Quiver.Path.comp, fuels]
  | cons past edge earlier => simp [Quiver.Path.comp, fuels, earlier, List.append_assoc]

theorem occupied_monotone {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target) :
    source.occupied ⊆ target.occupied := by
  induction path with
  | nil => exact Finset.Subset.refl _
  | cons past edge earlier => exact earlier.trans edge.occupied_subset

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecution
