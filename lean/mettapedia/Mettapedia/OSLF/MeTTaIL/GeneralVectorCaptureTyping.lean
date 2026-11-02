import Mettapedia.OSLF.MeTTaIL.GeneralVectorTypedMatch

/-! Constructor/vector match typing needs only unambiguous constructor
labels and collection roles. Selecting operational rules does not alter
these grammar properties.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match MatchSpec RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

mutual
theorem vector_matching_captures_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)} {schema target : Pattern}
    {type : TypeExpr} {bindings : Bindings}
    (labels : LabelDeterministic language) (choices : CollectionChoiceDeterministic language)
    (shape : VectorFirstOrder schema) (matched : MatchRel schema target bindings)
    (schemaTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
      language (FreeTypeContext.ofList context) [] schema type)
    (targetOpen : OpenPatternWellSorted language free bound type target) :
    CapturesTyped language free bound context bindings := by
  cases shape with
  | metavariable name =>
      cases matched
      cases schemaTyped with
      | fvar declared =>
          intro entry member
          cases List.mem_singleton.mp member
          exact ⟨type, (context_ofList_lookup context name) ▸ declared, targetOpen⟩
  | constructor label schemas children =>
      cases matched with
      | apply arguments _ =>
          cases schemaTyped with
          | constructor schemaMember _ schemasTyped =>
              obtain ⟨actual, actualMember, actualLabel, _, targetsTyped⟩ := application_typing targetOpen.1
              have same := labels schemaMember actualMember actualLabel.symm
              subst actual
              exact vector_arguments_captures_typed labels choices children arguments schemasTyped targetsTyped
                targetOpen.2.1 targetOpen.2.2.1
  | vector schemas children =>
      cases matched with
      | collection nonvector _ => exact False.elim (nonvector rfl)
      | vector arguments =>
          obtain ⟨elementType, schemasTyped, _, targetsTyped⟩ :=
            recursive_collection_element_roles choices schemaTyped targetOpen.1
          apply vector_elements_captures_typed labels choices children arguments schemasTyped targetsTyped
          · exact targetOpen.2.1
          · exact (Bool.and_eq_true_iff.mp targetOpen.2.2.1).2
termination_by sizeOf schema

theorem vector_arguments_captures_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)} {schemas targets : List Pattern}
    {parameters : List TermParam} {bindings : Bindings}
    (labels : LabelDeterministic language) (choices : CollectionChoiceDeterministic language)
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema) (matched : MatchArgsRel schemas targets bindings)
    (schemasTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.ArgumentsHaveTypes
      language (FreeTypeContext.ofList context) [] schemas parameters)
    (targetsTyped : ArgumentsHaveTypes language free bound targets parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList targets = true) (objects : isObjectPatternList targets = true) :
    CapturesTyped language free bound context bindings := by
  cases schemas with
  | nil => cases matched; exact fun _ member => False.elim (List.not_mem_nil member)
  | cons schema schemas =>
      cases matched with
      | cons first rest merged =>
          cases schemasTyped with
          | cons _ expected schemaType schemasType =>
              cases targetsTyped with
              | cons _ actual targetType targetsType =>
                  have same := Option.some.inj (expected.symm.trans actual)
                  subst same
                  simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at canonical
                  simp only [isObjectPatternList, Bool.and_eq_true] at objects
                  exact capturesTyped_merge
                    (vector_matching_captures_typed labels choices (shapes schema List.mem_cons_self) first schemaType
                      ⟨targetType, canonical.1, objects.1, targetType.isWellScopedAt⟩)
                    (vector_arguments_captures_typed labels choices
                      (fun child member => shapes child (List.mem_cons_of_mem _ member)) rest schemasType targetsType canonical.2 objects.2) merged
termination_by sizeOf schemas

theorem vector_elements_captures_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {context : List (String × TypeExpr)} {schemas targets : List Pattern}
    {elementType : TypeExpr} {bindings : Bindings}
    (labels : LabelDeterministic language) (choices : CollectionChoiceDeterministic language)
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema) (matched : MatchArgsRel schemas targets bindings)
    (schemasTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType
      language (FreeTypeContext.ofList context) [] schemas elementType)
    (targetsTyped : ElementsHaveType language free bound targets elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList targets = true) (objects : isObjectPatternList targets = true) :
    CapturesTyped language free bound context bindings := by
  cases schemas with
  | nil => cases matched; exact fun _ member => False.elim (List.not_mem_nil member)
  | cons schema schemas =>
      cases matched with
      | cons first rest merged =>
          cases schemasTyped with
          | cons schemaType schemasType =>
              cases targetsTyped with
              | cons targetType targetsType =>
                  simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at canonical
                  simp only [isObjectPatternList, Bool.and_eq_true] at objects
                  exact capturesTyped_merge
                    (vector_matching_captures_typed labels choices (shapes schema List.mem_cons_self) first schemaType
                      ⟨targetType, canonical.1, objects.1, targetType.isWellScopedAt⟩)
                    (vector_elements_captures_typed labels choices
                      (fun child member => shapes child (List.mem_cons_of_mem _ member)) rest schemasType targetsType canonical.2 objects.2) merged
termination_by sizeOf schemas
end

theorem vector_source_typed_match {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {context : List (String × TypeExpr)} {schema source : Pattern} {type : TypeExpr} {assignment : Bindings}
    (labels : LabelDeterministic language) (choices : CollectionChoiceDeterministic language)
    (shape : VectorFirstOrder schema)
    (schemaTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
      language (FreeTypeContext.ofList context) [] schema type)
    (sourceTyped : OpenPatternWellSorted language free bound type source)
    (defined : Defined assignment schema.freeFvarNames)
    (input : applyBindings assignment schema = source) :
    ∃ captures, CapturesTyped language free bound context captures ∧ Defined captures schema.freeFvarNames ∧
      applyBindings captures schema = source := by
  obtain ⟨captures, matched, compatible, _, names⟩ := vector_match_instance assignment shape defined
  rw [input] at matched
  have typed := vector_matching_captures_typed labels choices shape matched schemaTyped sourceTyped
  have capturesDefined : Defined captures schema.freeFvarNames := by
    intro name member
    exact (lookup_some_iff_mem_names captures name).mpr ((names name).mpr member)
  have sameAtInput : applyBindings captures schema = applyBindings assignment schema := by
    apply vector_output_agreement shape
    intro name member
    obtain ⟨actual, found⟩ := capturesDefined name member
    have original := compatible (name, actual) (raw_lookup_member found)
    simp only [apply_variable, found, original, Option.getD_some]
  exact ⟨captures, typed, capturesDefined, sameAtInput.trans input⟩

theorem vector_source_root_construct {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {index : Nat} {assignment : Bindings}
    {source target : Pattern}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    (labels : LabelDeterministic environment.language) (choices : CollectionChoiceDeterministic environment.language)
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (schemaTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
      environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.left type)
    (premiseFree : rule.premises = [])
    (rightBound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames)
    (defined : Defined assignment rule.left.freeFvarNames)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
    (targetTyped : OpenPatternWellSorted environment.language environment.free bound type target)
    (input : applyBindings assignment rule.left = source)
    (output : applyBindings assignment rule.right = target) :
    ∃ trace captured, GeneralPremise.RootFiring environment bound type source index trace captured captured [] target := by
  obtain ⟨captures, typed, capturesDefined, capturesInput⟩ :=
    vector_source_typed_match labels choices leftShape schemaTyped sourceTyped defined input
  have capturesOutput : applyBindings captures rule.right = target := by
    rw [← output]
    exact vector_rule_output_unique leftShape rightShape rightBound captures assignment (capturesInput.trans input.symm)
  exact vector_rootFiring_construct declared specified admitted zero leftShape rightShape premiseFree rightBound
    capturesDefined typed sourceTyped targetTyped capturesInput capturesOutput

#print axioms vector_matching_captures_typed
#print axioms vector_source_root_construct

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
