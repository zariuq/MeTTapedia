import Mettapedia.OSLF.MeTTaIL.GeneralVectorAddressSoundness

/-! Generated binder-free rules obtain typed captures from their actual
grammar inference. The proof follows recorded occurrences into the sorted
source and reads the consistency-checked inferred context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding GeneralRuleBindingGrammar
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem inspect_name_typed {language : LanguageDef} {context : List (String × TypeExpr)} {schema : Pattern}
    {expected : TypeExpr} {rows : List Occurrence} (shape : VectorFirstOrder schema)
    (read : inspect language context .left [] expected schema = some rows) (name : String)
    (present : name ∈ schema.freeFvarNames) :
    ∃ row ∈ rows, row.name = name ∧ row.bound = [] ∧
      contextAt? language context [] expected schema row.path = some ([], row.result) ∧
      occurrenceAt? schema row.path = some name := by
  obtain ⟨address, member, named⟩ := vector_name_address shape name present .left []
  obtain ⟨row, rowMember, rowRead⟩ := option_mapM_member_image _ _ rows read address member
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at rowRead
  obtain ⟨⟨bound, result⟩, found, same⟩ := rowRead
  change some (Occurrence.mk address bound result) = some row at same
  cases Option.some.inj same
  have noBinders := contextAt?_binderFree language context [] expected schema address.path bound result
    (GeneralRuleBindingInference.vector_binderFree shape) found
  subst bound
  obtain ⟨suffix, samePath, occurs⟩ := vector_address_sound shape .left [] address member
  simp only [List.nil_append] at samePath
  rw [← samePath, named] at occurs
  exact ⟨_, rowMember, named, rfl, found, occurs⟩

theorem inferred_input_lookup_typed {language : LanguageDef} {free : FreeTypeContext}
    {rule : RewriteRule} {inference : Inference} {assignment : Bindings} {expected : TypeExpr}
    (labels : LabelDeterministic language) (choices : CollectionChoiceDeterministic language)
    (shape : VectorFirstOrder rule.left)
    (inferred : infer? language rule = some inference)
    (head : headType? language rule.typeContext [] rule.left = some expected)
    (sourceTyped : HasType language free [] (applyBindings assignment rule.left) expected)
    (name : String) (present : name ∈ rule.left.freeFvarNames) :
    ∃ type, FreeTypeContext.ofList (elaborate rule inference).typeContext name = some type ∧
      HasType language free [] (applyBindings assignment (.fvar name)) type := by
  simp only [infer?, Option.bind_eq_bind, Option.bind_eq_some_iff] at inferred
  obtain ⟨actualExpected, headRead, leftRows, leftRead, rightRows, _, premiseRows, _, result⟩ := inferred
  have sameExpected := Option.some.inj (headRead.symm.trans head)
  subst actualExpected
  split at result
  next accepted =>
    cases Option.some.inj result
    obtain ⟨row, rowMember, named, _, location, occurs⟩ := inspect_name_typed shape leftRead name present
    have allRowsMember : row ∈ leftRows ++ rightRows ++ premiseRows.flatten := List.mem_append_left _ (List.mem_append_left _ rowMember)
    have consistent := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1).1
    have declared := consistent_occurrence_typed _ _ consistent row allRowsMember
    rw [named] at declared
    refine ⟨row.result, declared, ?_⟩
    exact vector_occurrence_instance_typed labels choices shape location occurs sourceTyped
  next => contradiction

#print axioms inferred_input_lookup_typed

theorem vector_output_canonical {schema : Pattern} (shape : VectorFirstOrder schema) (assignment : Bindings)
    (canonical : (applyBindings assignment schema).hasCanonicalBinderMetadata = true)
    (objects : Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern (applyBindings assignment schema) = true) :
    ∀ name ∈ schema.freeFvarNames,
      (applyBindings assignment (.fvar name)).hasCanonicalBinderMetadata = true ∧
      Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern (applyBindings assignment (.fvar name)) = true := by
  cases shape with
  | metavariable actual =>
      intro name member
      have same : name = actual := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using member
      subst name
      exact ⟨canonical, objects⟩
  | constructor label arguments children =>
      simp only [applyBindings, Pattern.hasCanonicalBinderMetadata, isObjectPattern] at canonical objects
      intro name member
      obtain ⟨schema, present, member⟩ := List.mem_flatMap.mp
        (by simpa only [Pattern.freeFvarNames] using member)
      have selected := list_canonical_object_at canonical objects (List.mem_map_of_mem present)
      exact vector_output_canonical (children schema present) assignment selected.1 selected.2 name member
  | vector arguments children =>
      simp only [applyBindings, List.append_nil, Pattern.hasCanonicalBinderMetadata, isObjectPattern,
        Option.isNone_none, Bool.true_and] at canonical objects
      intro name member
      obtain ⟨schema, present, member⟩ := List.mem_flatMap.mp
        (by simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using member)
      have selected := list_canonical_object_at canonical objects (List.mem_map_of_mem present)
      exact vector_output_canonical (children schema present) assignment selected.1 selected.2 name member
termination_by sizeOf schema

where
  list_canonical_object_at {items : List Pattern} {item : Pattern}
      (canonical : Pattern.hasCanonicalBinderMetadataList items = true)
      (objects : isObjectPatternList items = true) (member : item ∈ items) :
      item.hasCanonicalBinderMetadata = true ∧ isObjectPattern item = true := by
    induction items with
    | nil => cases member
    | cons first rest ih =>
        have firstCanonical := Bool.and_eq_true_iff.mp canonical
        have firstObjects := Bool.and_eq_true_iff.mp objects
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨firstCanonical.1, firstObjects.1⟩
        · exact ih firstCanonical.2 firstObjects.2 later

theorem inferred_vector_typed_match {language : LanguageDef} {free : FreeTypeContext}
    {rule : RewriteRule} {inference : Inference} {assignment : Bindings} {expected : TypeExpr}
    (labels : LabelDeterministic language) (choices : CollectionChoiceDeterministic language)
    (shape : VectorFirstOrder rule.left)
    (inferred : infer? language rule = some inference)
    (head : headType? language rule.typeContext [] rule.left = some expected)
    (sourceTyped : OpenPatternWellSorted language free [] expected (applyBindings assignment rule.left))
    (defined : Defined assignment rule.left.freeFvarNames) :
    ∃ captures, CapturesTyped language free [] (elaborate rule inference).typeContext captures ∧
      Defined captures rule.left.freeFvarNames ∧ applyBindings captures rule.left = applyBindings assignment rule.left := by
  obtain ⟨captures, _, compatible, _, names⟩ := vector_match_instance assignment shape defined
  have capturesDefined : Defined captures rule.left.freeFvarNames := by
    intro name member
    exact (lookup_some_iff_mem_names captures name).mpr ((names name).mpr member)
  have capturesTyped : CapturesTyped language free [] (elaborate rule inference).typeContext captures := by
    intro entry member
    have present : entry.1 ∈ rule.left.freeFvarNames := (names entry.1).mp (List.mem_map_of_mem member)
    obtain ⟨type, declared, sorted⟩ := inferred_input_lookup_typed labels choices shape inferred head sourceTyped.1 entry.1 present
    have found := compatible entry member
    have same : applyBindings assignment (.fvar entry.1) = entry.2 := by
      simp only [apply_variable, found, Option.getD_some]
    have metadata := vector_output_canonical shape assignment sourceTyped.2.1 sourceTyped.2.2.1 entry.1 present
    rw [same] at sorted metadata
    exact ⟨type, (context_ofList_lookup _ _) ▸ declared, sorted, metadata.1, metadata.2, sorted.isWellScopedAt⟩
  refine ⟨captures, capturesTyped, capturesDefined, ?_⟩
  apply vector_output_agreement shape
  intro name member
  obtain ⟨actual, found⟩ := capturesDefined name member
  have original := compatible (name, actual) (raw_lookup_member found)
  simp only [apply_variable, found, original, Option.getD_some]

#print axioms inferred_vector_typed_match

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
