import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochAdmission
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesReady

/-! A complete finite O0 provider epoch has an empty free-name footprint.
The proof reads actual row typing and the existing compiled scope theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem values_closed {language : LanguageDef} {free : FreeTypeContext}
    {values : List Pattern} {types : List TypeExpr}
    (empty : ∀ name, free name = none) (typed : ValuesTyped language free [] values types) :
    values.flatMap Pattern.freeFvarNames = [] := by
  induction typed with
  | nil => rfl
  | @cons value values type types head tail ih =>
    have closed : value.freeFvarNames = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name member
      obtain ⟨type, found⟩ := HasType.freeType_of_mem_freeFvarNames_of_isObjectPattern head.1 head.2.2.1 member
      rw [empty] at found
      cases found
    simp only [List.flatMap_cons, closed, ih, List.nil_append]

theorem epoch_provider_names (prepared : Prepared) (table : ProviderSnapshot)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true) :
    providerFreeNames table = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨row, listed, occurs⟩ := List.mem_flatMap.mp member
  obtain ⟨signature, _, typed⟩ := checkProviderClosed_row _ _ table closed row listed
  have noNames := values_closed (fun _ => rfl) typed.2
  rw [noNames] at occurs
  cases occurs

theorem epoch_footprint (prepared : Prepared) (table : ProviderSnapshot)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true) :
    Complete.Footprint.declaredFootprint (epochPlan prepared table) = [] := by
  simp only [Complete.Footprint.declaredFootprint]
  change [] ++ (providerFreeNames table).filter _ = []
  rw [epoch_provider_names prepared table closed]
  rfl

theorem epoch_scope (prepared : Prepared) (table : ProviderSnapshot)
    (complete : (epochPlan prepared table).complete = true) (finite : table.dynamicRelations = []) :
    Complete.Footprint.Scope (epochPlan prepared table) [] := by
  have empty : (epochPlan prepared table).obligations = [] := List.isEmpty_iff.mp complete
  have pending : (epochPlan prepared table).obligations.filter (· != .childStratification) = [] := by rw [empty]; rfl
  have scope := (Complete.Footprint.compiled_scope pending finite).1
  have closed := (GeneralExecutionAdmission.complete_snapshot_checks complete).2.2.1
  change Complete.Footprint.Scope (epochPlan prepared table)
    (Complete.Footprint.declaredFootprint (epochPlan prepared table)) at scope
  rw [epoch_footprint prepared table closed] at scope
  exact scope

#print axioms epoch_provider_names
#print axioms epoch_footprint
#print axioms epoch_scope

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
