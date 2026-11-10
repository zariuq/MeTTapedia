import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFramesBody
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameCoding

/-! # Encoded indexed frames satisfy the eleven operational laws

The argument uses the existing indexed action laws and explicit raw-validity
proofs. Carrier equivalences transport values; they do not quotient morphism
representatives or add category equations on those representatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFramesCoding

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLFramesBody HOLFrameCoding

universe w uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)

def objectsValue : HOL.Ty.denote.{0,w+1} model.Carrier objectsType :=
  fun a => ULift.up (HOLFrameEncoding.objects (code.objects a))

def identityValue : HOL.Ty.denote.{0,w+1} model.Carrier identityType :=
  fun a => code.morphisms.symm (HOLFrameEncoding.identity X (code.objects a))

noncomputable def compositionValue : HOL.Ty.denote.{0,w+1} model.Carrier compositionType :=
  fun second first => code.morphisms.symm (HOLFrameEncoding.comp X (code.morphisms second) (code.morphisms first))

theorem lawful : Laws model (objectsValue model code) (termsValue model code) (homValue model code)
    (equalValue model X code) (actionValue model X code) (identityValue model X code)
    (compositionValue model X code) := by
  simp only [Laws, objectsValue, termsValue, homValue, equalValue, actionValue,
    identityValue, compositionValue, Equiv.apply_symm_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a t valid
    exact HOLFrameEncoding.terms_object valid
  · intro a b f valid
    exact HOLFrameEncoding.hom_objects valid
  · intro a valid
    exact HOLFrameEncoding.identity_valid X valid
  · intro a b c f g valid
    exact HOLFrameEncoding.comp_valid X valid.1 valid.2
  · intro a b f t valid
    exact HOLFrameEncoding.act_valid X valid.1 valid.2
  · intro a t valid
    apply code.terms.injective
    simp only [Equiv.apply_symm_apply]
    exact HOLFrameEncoding.act_identity_valid X valid
  · intro a b c f g t valid
    apply code.terms.injective
    simp only [Equiv.apply_symm_apply]
    exact HOLFrameEncoding.act_composition_valid X valid.1 valid.2.1 valid.2.2
  · intro a t valid
    exact HOLFrameEncoding.equal_reflexive_valid X valid
  · intro a x y valid
    exact HOLFrameEncoding.equal_symmetric X valid.2.2
  · intro a x y z valid
    exact HOLFrameEncoding.equal_transitive X valid.2.2.2.1 valid.2.2.2.2
  · intro a b f x y valid
    exact HOLFrameEncoding.action_preserves_valid X valid.1 valid.2.2.2

#print axioms lawful

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFramesCoding
