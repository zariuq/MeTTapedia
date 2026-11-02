import Mettapedia.OSLF.MeTTaIL.GeneralInferredVectorCaptures
import Mettapedia.OSLF.MeTTaIL.GeneralVectorDefinedInput
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammarFirstOrder
import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootConstruction

/-! Actual grammar-inferred root rules realize their ordinary instances.
Capture typing is obtained from the source and the recorded occurrence
contexts, retaining the elaborated rule and its actual binding specification.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding ScopedRuleMatching GeneralRuleBindingGrammar
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem inferred_vector_root_construct {environment : GeneralPremise.Environment} {rule : RewriteRule}
    {inference : Inference} {index : Nat} {assignment : Bindings} {type : TypeExpr} {source target : Pattern}
    (declared : environment.language.rewrites[index]? = some (elaborate rule inference))
    (specified : GeneralPremise.specification? environment index = some inference.spec)
    (inferred : infer? environment.language rule = some inference)
    (labels : LabelDeterministic environment.language) (choices : CollectionChoiceDeterministic environment.language)
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (head : headType? environment.language rule.typeContext [] rule.left = some type)
    (premiseFree : rule.premises = [])
    (rightBound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames)
    (sourceClosed : source.freeFvarNames = [])
    (sourceTyped : OpenPatternWellSorted environment.language environment.free [] type source)
    (targetTyped : OpenPatternWellSorted environment.language environment.free [] type target)
    (input : applyBindings assignment rule.left = source)
    (output : applyBindings assignment rule.right = target) :
    ∃ trace captured, GeneralPremise.RootFiring environment [] type source index trace captured captured [] target := by
  have defined := vector_defined_of_closed_input leftShape assignment input sourceClosed
  obtain ⟨captures, typed, capturesDefined, sameInput⟩ := inferred_vector_typed_match labels choices leftShape
    inferred head (input ▸ sourceTyped) defined
  have capturesInput : applyBindings captures rule.left = source := sameInput.trans input
  have capturesOutput : applyBindings captures rule.right = target := by
    rw [← output]
    exact vector_rule_output_unique leftShape rightShape rightBound captures assignment sameInput
  have admitted := (infer_admitted inferred).1
  have zero := infer_binderFree_zero environment.language rule inference
    (GeneralRuleBindingInference.vector_binderFree leftShape) (GeneralRuleBindingInference.vector_binderFree rightShape)
    premiseFree inferred
  exact vector_rootFiring_construct declared specified admitted zero leftShape rightShape premiseFree rightBound
    capturesDefined typed sourceTyped targetTyped capturesInput capturesOutput

#print axioms inferred_vector_root_construct

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
