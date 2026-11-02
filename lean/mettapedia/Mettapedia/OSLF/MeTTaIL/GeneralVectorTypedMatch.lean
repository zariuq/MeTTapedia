import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootConstruction
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderTyping

/-! Ordinary constructor/vector instances recover typed captures from the
authored schema and sorted source. The constructed match drops unrelated
bindings rather than requiring the caller's entire substitution to be typed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem vector_typed_match {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {context : List (String × TypeExpr)} {schema source : Pattern} {type : TypeExpr} {assignment : Bindings}
    (valid : language.validate = []) (choices : CollectionChoiceDeterministic language)
    (shape : VectorFirstOrder schema)
    (schemaTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
      language (FreeTypeContext.ofList context) [] schema type)
    (sourceTyped : OpenPatternWellSorted language free bound type source)
    (defined : Defined assignment schema.freeFvarNames)
    (input : applyBindings assignment schema = source) :
    ∃ captures, MatchSpec.MatchRel schema source captures ∧
      CapturesTyped language free bound context captures ∧ Defined captures schema.freeFvarNames ∧
      applyBindings captures schema = source := by
  obtain ⟨captures, matched, compatible, _, names⟩ := vector_match_instance assignment shape defined
  rw [input] at matched
  have typed := matching_recursive_captures_typed valid choices (GeneralRuleBindingInference.vector_binderFree shape)
    matched schemaTyped sourceTyped
  have capturesDefined : Defined captures schema.freeFvarNames := by
    intro name member
    exact (lookup_some_iff_mem_names captures name).mpr ((names name).mpr member)
  have sameAtInput : applyBindings captures schema = applyBindings assignment schema := by
    apply vector_output_agreement shape
    intro name member
    obtain ⟨actual, found⟩ := capturesDefined name member
    have actualMember := raw_lookup_member found
    have original := compatible (name, actual) actualMember
    simp only [apply_variable, found, original, Option.getD_some]
  exact ⟨captures, matched, typed, capturesDefined, sameAtInput.trans input⟩

theorem vector_rootFiring_construct_from_source {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {index : Nat} {assignment : Bindings}
    {source target : Pattern}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    (valid : environment.language.validate = []) (choices : CollectionChoiceDeterministic environment.language)
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
  obtain ⟨captures, _, typed, capturesDefined, capturesInput⟩ :=
    vector_typed_match valid choices leftShape schemaTyped sourceTyped defined input
  have capturesOutput : applyBindings captures rule.right = target := by
    rw [← output]
    exact vector_rule_output_unique leftShape rightShape rightBound captures assignment (capturesInput.trans input.symm)
  exact vector_rootFiring_construct declared specified admitted zero leftShape rightShape premiseFree rightBound
    capturesDefined typed sourceTyped targetTyped capturesInput capturesOutput

#print axioms vector_typed_match
#print axioms vector_rootFiring_construct_from_source

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
