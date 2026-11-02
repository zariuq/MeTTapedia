import Mettapedia.Logic.HOL.ContinuationPayloadBoundary
import Mettapedia.Logic.HOL.FiniteConstructorEncoding
import Mettapedia.Logic.HOL.ConstructorInjectivity
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# A full-model boundary for shared-carrier constructor payloads

The actual payload type for one three-field constructor is a continuation
over those fields. When the middle field has the recursive result carrier,
full payload injectivity would embed its powerset back into that carrier.
The obstruction uses a fixed tag and a fixed child array. It does not apply
to injectivity restricted to valid encoded payloads, or assert that every
Henkin interpretation has full function domains.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorPayloadBoundary
open FiniteConstructorEncoding ContinuationPayloadBoundary
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (Carrier : Base → Type (max (u+1) w)) (number element : Ty Base)

theorem payload_denotation : Ty.denote Carrier (payloadType [[number,element,number]]) =
    Payload (Ty.denote Carrier number) (Ty.denote Carrier element) (Ty.denote Carrier .prop) := rfl

theorem no_full_payload_embedding (zero : Ty.denote Carrier number)
    (encode : Ty.denote Carrier (payloadType [[number,element,number]]) → Ty.denote Carrier element) :
    ¬ Function.Injective encode := by
  apply ContinuationPayloadBoundary.no_full_payload_embedding zero
    (ULift.up True : Ty.denote Carrier .prop) (ULift.up False : Ty.denote Carrier .prop) _ encode
  intro same
  have impossible : True = False := congrArg ULift.down same
  exact Eq.mp impossible True.intro

theorem no_same_carrier_payload_injectivity (zero : Ty.denote Carrier number) (bottom : Ty.denote Carrier element)
    (construct : Ty.denote Carrier (number ⇒ payloadType [[number,element,number]] ⇒ (number ⇒ element) ⇒ element)) :
    ¬ Function.Injective (fun payload => construct zero payload (fun _ => bottom)) :=
  no_full_payload_embedding Carrier number element zero _

theorem full_injectivity_statement_refused (model : HenkinModel.{u,v,w} Base Const)
    (full : model.FullDomains) (zero : Ty.denote model.Carrier number) (bottom : Ty.denote model.Carrier element)
    (construct : Term Const Γ (number ⇒ payloadType [[number,element,number]] ⇒ (number ⇒ element) ⇒ element))
    (values : model.Valuation Γ) :
    ¬ (model.denote (ConstructorInjectivity.statement construct) values).down := by
  intro assumed
  apply no_same_carrier_payload_injectivity model.Carrier number element zero bottom (model.denote construct values)
  intro first second same
  have compared := assumed zero (full _ _) first (full _ _) (fun _ => bottom) (full _ _)
    zero (full _ _) second (full _ _) (fun _ => bottom) (full _ _)
  simp only [ConstructorProjections.apply,
    HenkinModel.denote,PreModel.denote,Soundness.denote_weaken,PreModel.extend,PreModel.Eqv] at compared
  have returnSame : model.Eqv element
      (model.denote construct values zero first (fun _ => bottom))
      (model.denote construct values zero second (fun _ => bottom)) := by
    exact Eq.mp (congrArg (fun result : Ty.denote model.Carrier element =>
      model.Eqv element (model.denote construct values zero first (fun _ => bottom)) result) same)
      (model.eqv_refl (full _ _))
  have fieldSame : model.Eqv (payloadType [[number,element,number]]) first second := by
    exact (compared.mp returnSame).2.1
  exact model.eq_of_eqv_of_fullDomains full fieldSame

#print axioms full_injectivity_statement_refused
end Mettapedia.Logic.HOL.FiniteConstructorPayloadBoundary
