import Mettapedia.Logic.HOL.FiniteConstructorEncoding
import Mettapedia.TypeTheory.FiniteConstructorNaturalRealization

/-!
# Natural constructor realization of the actual HOL payload encoding

The existing payload equivalence connects typed HOL function values to the
represented source data. The natural constructor uses that same equivalence;
its source computation law follows from the actual encoding's denotation.
Countability and natural-valued children are explicit. Instantiating an outer
source constructor symbol with this meaning remains a separate model step.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding.NaturalRealization
open Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}
    (model : HenkinModel.{u,v,w} Base Const) (signature : List (List (Ty Base)))
    [Encodable (Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) signature)]
    (arity : Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) signature → Nat)

noncomputable def construct (tag : Nat) (payload : Ty.denote model.Carrier (payloadType signature))
    (children : Nat → Nat) : Nat :=
  Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.construct (Ty.denote model.Carrier) signature arity tag
    (payloadEquivalence model signature payload) children

def Admitted (allowed : Nat → Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) signature →
    (Nat → Nat) → Prop) (tag : Nat) (payload : Ty.denote model.Carrier (payloadType signature)) (children : Nat → Nat) : Prop :=
  Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.Admitted (Ty.denote model.Carrier) signature arity allowed tag
    (payloadEquivalence model signature payload) children

theorem construct_source {Γ : Ctx Base} (tag : Nat) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) (values : model.Valuation Γ) (children : Nat → Nat) :
    construct model signature arity tag (model.denote (encode signature occurrence arguments) values) children =
      Nat.succ (Encodable.encode (tag,
        (⟨occurrence,denoteArguments model _ arguments values⟩ : Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) signature),
        Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.snapshot (arity ⟨occurrence,denoteArguments model _ arguments values⟩) children)) := by
  unfold construct
  rw [encode_denote]
  exact Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.construct_encode _ _ _ _ _ _

omit [Encodable (Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) signature)] in
theorem admitted_source {Γ : Ctx Base}
    (allowed : Nat → Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) signature → (Nat → Nat) → Prop)
    (tag : Nat) (occurrence : Fin signature.length) (arguments : Arguments Const Γ (signature.get occurrence))
    (values : model.Valuation Γ) (children : Nat → Nat)
    (permitted : allowed tag ⟨occurrence,denoteArguments model _ arguments values⟩ children)
    (canonical : (Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.slots (arity ⟨occurrence,denoteArguments model _ arguments values⟩)).Canonical 0 children) :
    Admitted model signature arity allowed tag (model.denote (encode signature occurrence arguments) values) children := by
  unfold Admitted
  rw [encode_denote]
  exact Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.admitted_encode _ _ _ _ _ _ _ permitted canonical

theorem fields_of_eq
    (allowed : Nat → Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) signature → (Nat → Nat) → Prop)
    (firstTag secondTag : Nat) (firstPayload secondPayload : Ty.denote model.Carrier (payloadType signature))
    (firstChildren secondChildren : Nat → Nat)
    (firstAdmitted : Admitted model signature arity allowed firstTag firstPayload firstChildren)
    (secondAdmitted : Admitted model signature arity allowed secondTag secondPayload secondChildren)
    (same : construct model signature arity firstTag firstPayload firstChildren =
      construct model signature arity secondTag secondPayload secondChildren) :
    firstTag = secondTag ∧ firstPayload = secondPayload ∧ firstChildren = secondChildren := by
  have recovered := Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.fields_of_eq (Ty.denote model.Carrier) signature arity allowed _ _ _ _ _ _
    firstAdmitted secondAdmitted same
  exact ⟨recovered.1,(payloadEquivalence model signature).injective recovered.2.1,recovered.2.2⟩

#print axioms construct_source
#print axioms fields_of_eq
end Mettapedia.Logic.HOL.FiniteConstructorEncoding.NaturalRealization
