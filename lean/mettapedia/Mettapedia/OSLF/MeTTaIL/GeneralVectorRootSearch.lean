import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootConstruction
import Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot

/-! The existing complete root search realizes typed constructor/vector
rule instances. Published targets reflect to the same ordinary instance;
every such instance is eventually published with an actual receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem vector_root_search_iff {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {index : Nat} {bindings : Bindings}
    {source target : Pattern}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (premiseFree : rule.premises = [])
    (rightBound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames)
    (defined : Defined bindings rule.left.freeFvarNames)
    (typed : CapturesTyped environment.language environment.free bound rule.typeContext bindings)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
    (outputTyped : OpenPatternWellSorted environment.language environment.free bound type (applyBindings bindings rule.right))
    (input : applyBindings bindings rule.left = source) :
    (∃ work firing, firing ∈ (Complete.DeepRoot.run ⟨environment, bound, type, source, index⟩ work
      (Complete.DeepRoot.start ⟨environment, bound, type, source, index⟩)).publication ∧ firing.target = target) ↔
      target = applyBindings bindings rule.right := by
  constructor
  · rintro ⟨work, firing, published, rfl⟩
    have valid := Complete.DeepRoot.sound ⟨environment, bound, type, source, index⟩ work firing published
    exact (vector_rootFiring_target declared specified zero leftShape rightShape premiseFree rightBound input valid).2.2
  · rintro rfl
    obtain ⟨trace, captured, valid⟩ := vector_rootFiring_construct declared specified admitted zero leftShape rightShape
      premiseFree rightBound defined typed sourceTyped outputTyped input rfl
    let firing : Complete.DeepRoot.Firing := ⟨trace, captured, captured, [], applyBindings bindings rule.right⟩
    obtain ⟨work, published⟩ := Complete.DeepRoot.complete_in_limit (request := ⟨environment, bound, type, source, index⟩)
      (firing := firing) valid
    exact ⟨work, firing, published, rfl⟩

#print axioms vector_root_search_iff

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
