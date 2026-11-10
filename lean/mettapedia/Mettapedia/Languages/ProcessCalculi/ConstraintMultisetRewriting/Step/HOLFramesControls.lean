import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFramesSpecialization

/-! # Action laws do not identify morphism representations

Two Boolean morphisms act identically on every natural-number term. Composition
chooses the false representative, so a representation-level identity equation
fails. The actual loaded frame predicate nevertheless holds, as required by
the indexed action interface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFramesControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLFrameCoding HOLFramesCoding

def terms (_ : Unit) := Nat
def maps (_ _ : Unit) := Bool

def frame : Frames terms maps where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act _ term := term
  id _ := false
  comp _ _ := false
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by intro a b f x y same; exact same

theorem action_agrees (term : Nat) :
    frame.act (a := ()) (b := ()) false term = frame.act (a := ()) (b := ()) true term := rfl

theorem representation_identity_fails :
    frame.comp (a := ()) (b := ()) (c := ()) (frame.id ()) true ≠ true := by
  change (false : Bool) ≠ true
  decide

theorem loaded_frame_without_representation_identity
    (other : TypeFamilySemantics.OperatorFamilies.{0}) (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (code : Coding actual Unit terms maps),
      HOLFramesSpecialization.Agreement actual frame code ∧
      compositionValue actual frame code (identityValue actual frame code (code.objects.symm (some ())))
        (code.morphisms.symm (HOLFrameEncoding.encodeHom (Hom := maps) (a := ()) (b := ()) true)) ≠
        code.morphisms.symm (HOLFrameEncoding.encodeHom (Hom := maps) (a := ()) (b := ()) true) := by
  obtain ⟨actual, code, _, agreement⟩ :=
    HOLFramesSpecialization.constructed_agreement frame Nat other prior
  refine ⟨actual, code, agreement, ?_⟩
  intro wrong
  have encoded := congrArg code.morphisms wrong
  simp only [compositionValue, identityValue, Equiv.apply_symm_apply,
    HOLFrameEncoding.identity_encoded, HOLFrameEncoding.comp_encoded] at encoded
  exact representation_identity_fails (HOLFrameEncoding.morphism_identity_retained () () encoded)

#print axioms representation_identity_fails
#print axioms loaded_frame_without_representation_identity

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFramesControls
