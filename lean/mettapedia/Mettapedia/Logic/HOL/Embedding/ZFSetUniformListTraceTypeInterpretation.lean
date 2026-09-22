import Mettapedia.Logic.HOL.Embedding.ZFSetListClosure
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTypeInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts
import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListModel

/-!
# Trace-coded types for the uniform HOL list theory

The ground codes are the actual element, encoded-list, and natural-index
sets used by `ZFSetUniformListModel`.  Every arrow is an Aczel trace product.
Consequently decoding lands in the existing full-domain HOL model while the
function codes have the same representation used by the dependent trace
model.  This is a change of representation, not a second list model.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceTypeInterpretation

open UniformListInduction
open ZFSetDependentProducts ZFSetTraceProducts ZFSetUniverseClosure
open ZFSetHOLTypeInterpretation (truthCode truth holds truth_holds holds_truth
  truthCode_mem functionEquiv)
open ZFSetIndexedClosure ZFSetListClosure

universe u

/-- The proposition-code equivalence at the same set universe as the three
uniform-list ground carriers. -/
noncomputable def propositionEquiv :
    Elements truthCode.{u} ≃ ULift.{u + 1} Prop where
  toFun := fun value => .up (holds value)
  invFun := fun value => truth value.down
  left_inv := truth_holds
  right_inv := by
    intro value
    apply ULift.ext
    exact propext (holds_truth value.down)

@[reducible] noncomputable def typeCode (a : ZFSet.{u}) :
    Ty BaseSort → ZFSet.{u}
  | .prop => truthCode
  | .base .element => a
  | .base .sequence => ZFSetList.listCode a
  | .base .count => finiteRankIndex
  | .arr A B => tracePiSet (typeCode a A) (fun _ => typeCode a B)

abbrev Value (a : ZFSet.{u}) (A : Ty BaseSort) := Elements (typeCode a A)

noncomputable def decode (a : ZFSet.{u}) : (A : Ty BaseSort) →
    Value a A ≃ Ty.denote.{0, u + 1} (ZFSetUniformListModel.carrier a) A
  | .prop => propositionEquiv
  | .base .element => Equiv.refl _
  | .base .sequence => Equiv.refl _
  | .base .count => Equiv.refl _
  | .arr A B => (tracePiEquiv (typeCode a A) (fun _ => typeCode a B)).trans
      (functionEquiv (decode a A) (decode a B))

theorem typeCode_mem {U a : ZFSet.{u}} (closed : Closed U)
    (carrierMember : a ∈ U) (indicesMember : finiteRankIndex ∈ U)
    (A : Ty BaseSort) : typeCode a A ∈ U := by
  induction A with
  | prop => exact truthCode_mem closed carrierMember
  | base sort =>
      cases sort with
      | element => exact carrierMember
      | sequence => exact listCode_mem closed carrierMember indicesMember
      | count => exact indicesMember
  | arr A B ihA ihB =>
      exact closed.tracePiSet_mem ihA _ (fun _ _ => ihB)

noncomputable def lam {a : ZFSet.{u}} {A B : Ty BaseSort}
    (body : Value a A → Value a B) : Value a (A ⇒ B) :=
  traceEncode (a := typeCode a A) (b := fun _ => typeCode a B) body

noncomputable def app {a : ZFSet.{u}} {A B : Ty BaseSort}
    (function : Value a (A ⇒ B)) (argument : Value a A) : Value a B :=
  traceValue (a := typeCode a A) (b := fun _ => typeCode a B) function argument

@[simp] theorem app_lam {a : ZFSet.{u}} {A B : Ty BaseSort}
    (body : Value a A → Value a B) (argument : Value a A) :
    app (lam body) argument = body argument :=
  congrFun (trace_beta (a := typeCode a A) (b := fun _ => typeCode a B) body) argument

theorem lam_eta {a : ZFSet.{u}} {A B : Ty BaseSort}
    (function : Value a (A ⇒ B)) :
    lam (fun argument => app function argument) = function :=
  trace_eta (a := typeCode a A) (b := fun _ => typeCode a B) function

theorem decode_app {a : ZFSet.{u}} {A B : Ty BaseSort}
    (function : Value a (A ⇒ B)) (argument : Value a A) :
    decode a B (app function argument) =
      decode a (A ⇒ B) function (decode a A argument) := by
  change decode a B (traceValue function argument) =
    decode a B (traceValue function ((decode a A).symm (decode a A argument)))
  rw [Equiv.symm_apply_apply]

theorem decode_lam {a : ZFSet.{u}} {A B : Ty BaseSort}
    (body : Value a A → Value a B) :
    decode a (A ⇒ B) (lam body) =
      fun x => decode a B (body ((decode a A).symm x)) := by
  funext x
  change decode a B (app (lam body) ((decode a A).symm x)) = _
  rw [app_lam]

theorem decode_truth {a : ZFSet.{u}} (p : Prop) :
    decode a .prop (truth p) = ULift.up p := by
  apply ULift.ext
  exact propext (holds_truth p)

theorem equality_decode {a : ZFSet.{u}} {A : Ty BaseSort}
    (left right : Value a A) :
    left = right ↔ (ZFSetUniformListModel.model a).Eqv A
      (decode a A left) (decode a A right) := by
  constructor
  · rintro rfl
    exact (ZFSetUniformListModel.model a).eqv_refl
      (ZFSetUniformListModel.fullDomains a A _)
  · intro equal
    apply (decode a A).injective
    exact (ZFSetUniformListModel.model a).eq_of_eqv_of_fullDomains
      (ZFSetUniformListModel.fullDomains a) equal

/-! ## Trace-coded constants and literal agreement with the retained model -/

noncomputable def constant (a : ZFSet.{u}) :
    {A : Ty BaseSort} → Symbol A → Value a A
  | _, .nil => ZFSetList.nil a
  | _, .cons => lam (fun x => lam (fun xs => ZFSetList.cons x xs))
  | _, .map => lam (fun f => lam (fun xs =>
      ZFSetUniformListModel.mapValue (decode a mapping f) xs))
  | _, .length => lam (ZFSetUniformListModel.lengthValue (a := a))
  | _, .zero => ZFSetUniformListModel.encodeCount 0
  | _, .succ => lam (fun n =>
      ZFSetUniformListModel.encodeCount (ZFSetUniformListModel.decodeCount n + 1))

theorem decode_constant {a : ZFSet.{u}} {A : Ty BaseSort} (c : Symbol A) :
    decode a A (constant a c) = ZFSetUniformListModel.constant a c := by
  cases c with
  | nil => rfl
  | cons =>
      rw [constant, decode_lam]
      funext x
      rw [decode_lam]
      funext xs
      rfl
  | map =>
      rw [constant, decode_lam]
      funext f
      rw [decode_lam]
      funext xs
      rw [Equiv.apply_symm_apply]
      rfl
  | length =>
      rw [constant, decode_lam]
      funext xs
      rfl
  | zero => rfl
  | succ =>
      rw [constant, decode_lam]
      funext n
      rfl

/-! ## Nontrivial representation controls -/

theorem higher_order_beta {a : ZFSet.{u}}
    (f : Value a mapping) (x : Value a element) :
    app (app (lam (fun g => lam (fun y => app g (app g y)))) f) x =
      app f (app f x) := by
  simp

#print axioms propositionEquiv
#print axioms decode
#print axioms typeCode_mem
#print axioms app_lam
#print axioms lam_eta
#print axioms decode_app
#print axioms decode_lam
#print axioms equality_decode
#print axioms decode_constant
#print axioms higher_order_beta

end Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceTypeInterpretation
