import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeMatchReadback
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderTyping
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderScopedInstance

/-! Typed subjects force the sorts of ordinary row captures. This derives
the sorted-substitution obligation from the actual match and source typing,
rather than asking its producer to supply it. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

theorem encode_canonical (term : Maude.Term) : (encode term).hasCanonicalBinderMetadata = true := by
  refine Maude.Term.rec
    (motive_1 := fun term => (encode term).hasCanonicalBinderMetadata = true)
    (motive_2 := fun terms => Pattern.hasCanonicalBinderMetadataList (terms.map encode) = true)
    ?_ ?_ ?_ ?_ term
  · intro name
    rw [encode, Pattern.hasCanonicalBinderMetadata]
  · intro id arguments ih
    simpa only [encode, Pattern.hasCanonicalBinderMetadata] using ih
  · rfl
  · intro first rest firstIH restIH
    simp only [List.map_cons, Pattern.hasCanonicalBinderMetadataList, firstIH, restIH, Bool.and_self]

theorem schema_freeContext (declarations : Maude.VariableContext) :
    FreeTypeContext.ofList (declarations.map fun entry => (entry.1, TypeExpr.base entry.2)) =
      freeContext declarations := by
  funext name
  induction declarations with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, sort⟩
      by_cases same : name = key
      · subst key
        simp [FreeTypeContext.ofList, freeContext]
      · have different : (name == key) = false := beq_eq_false_iff_ne.mpr same
        simpa only [List.map_cons, FreeTypeContext.ofList, Ne.symm same, if_false, freeContext,
          List.lookup_cons, different] using ih

theorem matched_row_sorted (prepared : Prepared) (ambient : Maude.VariableContext)
    (row : Maude.Row) (source : Maude.Term) (sort : String) {bindings : Bindings}
    (valid : prepared.language.validate = [])
    (checked : row.check prepared.source.signature = true) (inputs : row.inputsBound = true)
    (schemaTyped : Maude.HasSort prepared.source.signature row.usedContext row.left sort)
    (sourceTyped : Maude.HasSort prepared.source.signature ambient source sort)
    (matched : bindings ∈ matchPattern (encode row.left) (encode source)) :
    SortedBindingsIn prepared.language (freeContext ambient) (context row) bindings := by
  have schema : HasType prepared.language (FreeTypeContext.ofList (context row)) [] (encode row.left) (.base sort) := by
    change HasType prepared.language
      (FreeTypeContext.ofList (row.usedContext.map fun entry => (entry.1, TypeExpr.base entry.2))) [] _ _
    rw [schema_freeContext]
    exact (prepared_typing_iff prepared row.usedContext row.left sort).mpr schemaTyped
  have subject := (prepared_typing_iff prepared ambient source sort).mpr sourceTyped
  have captured := matching_captures_typed valid (encode_firstOrder row.left) (matchPattern_sound matched)
    schema subject (encode_canonical source) (encode_object source)
  have defined := raw_matching_defined (encode_firstOrder row.left) (matchPattern_sound matched)
  intro name type member
  obtain ⟨⟨key, valueSort⟩, listed, same⟩ := List.mem_map.mp member
  cases same
  have sourceLookup := context_lookup_of_mem (usedContext_distinct checked) listed
  have mappedLookup : (context row).lookup key = some (.base valueSort) := by
    rw [← context_ofList_lookup]
    change (FreeTypeContext.ofList (row.usedContext.map fun entry => (entry.1, TypeExpr.base entry.2))) key = _
    rw [schema_freeContext]
    simp [freeContext, sourceLookup]
  have occurs := usedContext_bound inputs listed
  rw [← encode_variables row.left] at occurs
  obtain ⟨value, found⟩ := defined key occurs
  obtain ⟨expected, declared, typed⟩ := captured (key, value) (raw_lookup_member found)
  have sameType : expected = .base valueSort := Option.some.inj (declared.symm.trans mappedLookup)
  subst expected
  simpa only [apply_variable, found, Option.getD_some] using And.intro typed.2.2.1 typed.1

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
