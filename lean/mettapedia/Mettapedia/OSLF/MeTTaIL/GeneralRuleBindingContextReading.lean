import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammarSoundness
import Mettapedia.GSLT.LanguageDef.SchemaTyping

/-! The inference algorithm's uniqueness lookup agrees with the schema's
ordinary first-match context when uniqueness succeeds. Thus occurrence
consistency supplies actual free-variable typing evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem unique?_all_equal {α : Type} [DecidableEq α] {items : List α} {actual : α}
    (found : unique? items = some actual) : ∀ item ∈ items, item = actual := by
  unfold unique? at found
  split at found
  next candidate shape =>
    cases Option.some.inj found
    intro item member
    have inUnique : item ∈ items.eraseDups := List.mem_eraseDups.mpr member
    rw [shape] at inUnique
    exact List.mem_singleton.mp inUnique
  next => contradiction

theorem lookupType_agrees {context : List (String × TypeExpr)} {name : String} {type : TypeExpr}
    (found : lookupType context name = some type) : FreeTypeContext.ofList context name = some type := by
  have member := lookupType_origin found
  have consistent : ∀ entry ∈ context, entry.1 = name → entry.2 = type := by
    intro entry present same
    have emitted : entry.2 ∈ context.filterMap (fun entry => if entry.1 == name then some entry.2 else none) :=
      List.mem_filterMap.mpr ⟨entry, present, by simp [same]⟩
    exact unique?_all_equal found _ emitted
  clear found
  induction context with
  | nil => cases member
  | cons first rest ih =>
      by_cases same : first.1 = name
      · have typeSame := consistent first List.mem_cons_self same
        simp [FreeTypeContext.ofList, same, typeSame]
      · have later : (name, type) ∈ rest := by
          rcases List.mem_cons.mp member with here | later
          · have bad := congrArg Prod.fst here
            exact False.elim (same bad.symm)
          · exact later
        simp only [FreeTypeContext.ofList, same, if_false]
        exact ih later (fun entry present named => consistent entry (List.mem_cons_of_mem first present) named)

theorem consistent_occurrence_typed (context : List (String × TypeExpr)) (rows : List Occurrence)
    (checked : consistent context rows = true) (row : Occurrence) (member : row ∈ rows) :
    FreeTypeContext.ofList context row.name = some row.result := by
  have checks := Bool.and_eq_true_iff.mp checked
  have rowChecked := List.all_eq_true.mp checks.1 row member
  exact lookupType_agrees (beq_iff_eq.mp rowChecked)

#print axioms lookupType_agrees

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar
