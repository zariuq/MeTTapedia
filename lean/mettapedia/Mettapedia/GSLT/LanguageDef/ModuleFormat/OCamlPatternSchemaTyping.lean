import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlGeneratedSchemaTyping

/-! Arbitrary nested source patterns produce sorted value schemas and
sorted binding lists. Fresh capture names are typed by their actual source
prefix, independently of any matcher or compiled plan.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem values_schema_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (items : List Pattern)
    (typed : ∀ item ∈ items, HasType language free bound item (.base "MlValue")) :
    HasType language free bound (values items) (.base "MlValues") := by
  induction items with
  | nil => exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  | cons first rest ih =>
      exact nonbare_constructor_typed terms [("head", .base "MlValue"), ("tail", .base "MlValues")] _
        (by decide +kernel) (.cons (typed first List.mem_cons_self)
          (.cons (ih (fun item member => typed item (List.mem_cons_of_mem first member))) .nil))

theorem pattern_schema_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (bound : List TypeExpr) (pattern : OCaml.MatchPattern) : ∀ start,
    HasType language captureContext bound (patternAt pattern start).term (.base "MlValue") ∧
      ∀ item ∈ (patternAt pattern start).bindings, HasType language captureContext bound item (.base "MlValue") := by
  refine OCaml.MatchPattern.rec
    (motive_1 := fun pattern => ∀ start,
      HasType language captureContext bound (patternAt pattern start).term (.base "MlValue") ∧
        ∀ item ∈ (patternAt pattern start).bindings, HasType language captureContext bound item (.base "MlValue"))
    (motive_2 := fun patterns => ∀ start,
      (∀ item ∈ (fieldsAt patterns start).1, HasType language captureContext bound item (.base "MlValue")) ∧
      (∀ item ∈ (fieldsAt patterns start).2, HasType language captureContext bound item (.base "MlValue")))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pattern
  · intro start
    refine ⟨pattern_capture_typed language bound start, ?_⟩
    simp only [patternAt_bind, List.mem_singleton]
    rintro item rfl
    exact pattern_capture_typed language bound start
  · intro start
    exact ⟨pattern_capture_typed language bound start,
      by simp only [patternAt_wildcard, List.not_mem_nil, false_implies, implies_true]⟩
  · intro datum start
    exact ⟨literal_typed language terms captureContext bound datum,
      by simp only [patternAt_literal, List.not_mem_nil, false_implies, implies_true]⟩
  · intro fields ih start
    obtain ⟨inputs, outputs⟩ := ih start
    exact ⟨nonbare_constructor_typed terms [("fields", .base "MlValues")] _ (by decide +kernel)
      (.cons (values_schema_typed language terms captureContext bound _ inputs) .nil), outputs⟩
  · intro head tail headIH tailIH start
    obtain ⟨headTyped, headOutputs⟩ := headIH start
    obtain ⟨tailTyped, tailOutputs⟩ := tailIH (patternAfter head start)
    refine ⟨nonbare_constructor_typed terms [("head", .base "MlValue"), ("tail", .base "MlValue")] _
      (by decide +kernel) (.cons headTyped (.cons tailTyped .nil)), ?_⟩
    intro item member
    rcases List.mem_append.mp member with first | rest
    · exact headOutputs item first
    · exact tailOutputs item rest
  · intro typeId constructor fields ih start
    obtain ⟨inputs, outputs⟩ := ih start
    exact ⟨nonbare_constructor_typed terms [("tag", .base "MlTag"), ("fields", .base "MlValues")] _
      (by decide +kernel) (.cons (tag_typed language terms captureContext bound typeId constructor)
        (.cons (values_schema_typed language terms captureContext bound _ inputs) .nil)), outputs⟩
  · intro start
    exact ⟨by simp [fieldsAt_nil], by simp [fieldsAt_nil]⟩
  · intro first rest firstIH restIH start
    obtain ⟨input, output⟩ := firstIH start
    obtain ⟨inputs, outputs⟩ := restIH (patternAfter first start)
    constructor
    · intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact input
      · exact inputs item member
    · intro item member
      rcases List.mem_append.mp member with here | later
      · exact output item here
      · exact outputs item later

#print axioms values_schema_typed
#print axioms pattern_schema_typed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
