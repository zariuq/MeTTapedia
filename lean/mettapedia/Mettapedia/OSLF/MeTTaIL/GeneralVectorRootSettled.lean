import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootSearch

/-! A completed shared root search contains every admitted typed ordinary
constructor/vector instance. Empty publications can certify absence only
after the search completes and the candidate instance is well typed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem vector_root_settled_iff {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {index work : Nat} {bindings : Bindings}
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
    (input : applyBindings bindings rule.left = source)
    (done : (Complete.DeepRoot.run ⟨environment, bound, type, source, index⟩ work
      (Complete.DeepRoot.start ⟨environment, bound, type, source, index⟩)).complete = true) :
    (∃ firing, firing ∈ (Complete.DeepRoot.run ⟨environment, bound, type, source, index⟩ work
      (Complete.DeepRoot.start ⟨environment, bound, type, source, index⟩)).publication ∧ firing.target = target) ↔
      target = applyBindings bindings rule.right := by
  constructor
  · rintro ⟨firing, published, rfl⟩
    have valid := Complete.DeepRoot.sound ⟨environment, bound, type, source, index⟩ work firing published
    exact (vector_rootFiring_target declared specified zero leftShape rightShape premiseFree rightBound input valid).2.2
  · rintro rfl
    obtain ⟨trace, captured, valid⟩ := vector_rootFiring_construct declared specified admitted zero leftShape rightShape
      premiseFree rightBound defined typed sourceTyped outputTyped input rfl
    let firing : Complete.DeepRoot.Firing := ⟨trace, captured, captured, [], applyBindings bindings rule.right⟩
    exact ⟨firing, Complete.DeepRoot.exact_of_complete _ work done valid, rfl⟩

theorem vector_root_settled_nonempty {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {index work : Nat} {bindings : Bindings}
    {source : Pattern}
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
    (input : applyBindings bindings rule.left = source)
    (done : (Complete.DeepRoot.run ⟨environment, bound, type, source, index⟩ work
      (Complete.DeepRoot.start ⟨environment, bound, type, source, index⟩)).complete = true) :
    (Complete.DeepRoot.run ⟨environment, bound, type, source, index⟩ work
      (Complete.DeepRoot.start ⟨environment, bound, type, source, index⟩)).publication ≠ [] := by
  obtain ⟨firing, present, _⟩ := (vector_root_settled_iff declared specified admitted zero leftShape rightShape premiseFree
    rightBound defined typed sourceTyped outputTyped input done).mpr rfl
  intro empty
  rw [empty] at present
  cases present

#print axioms vector_root_settled_iff
#print axioms vector_root_settled_nonempty

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
