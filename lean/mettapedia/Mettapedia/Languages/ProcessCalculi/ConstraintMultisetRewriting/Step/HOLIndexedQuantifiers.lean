import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFramesCoding

/-! # Quantification over encoded valid morphisms

A valid outgoing map determines an actual target frame and an inhabitant
of its indexed hom fibre. This extracts data from validity evidence; it
does not require every fibre to have a map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLIndexedQuantifiers

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOLModelsBody HOLFrameCoding HOLFramesCoding

universe w uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)

theorem valid_map_values {b : Obj}
    (c : HOL.Ty.denote.{0,w+1} model.Carrier objectType)
    (sigma : HOL.Ty.denote.{0,w+1} model.Carrier mapType)
    (valid : (homValue model code (code.objects.symm (some b)) c sigma).down) :
    ∃ (target : Obj) (map : Hom b target),
      c = code.objects.symm (some target) ∧ sigma = code.morphisms.symm (HOLFrameEncoding.encodeHom map) := by
  have raw : HOLFrameEncoding.hom (some b) (code.objects c) (code.morphisms sigma) := by
    simpa only [homValue, Equiv.apply_symm_apply] using valid
  cases targetEq : code.objects c with
  | none => simp [targetEq, HOLFrameEncoding.hom] at raw
  | some target =>
      rw [targetEq] at raw
      obtain ⟨map, encoded⟩ := raw
      refine ⟨target, map, ?_, ?_⟩
      · apply code.objects.injective
        simpa only [Equiv.apply_symm_apply] using targetEq
      · apply code.morphisms.injective
        simpa only [Equiv.apply_symm_apply, HOLFrameEncoding.encodeHom] using encoded

theorem composition_encoded {a b c : Obj} (second : Hom b c) (first : Hom a b) :
    compositionValue model X code (code.morphisms.symm (HOLFrameEncoding.encodeHom second))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom first)) =
      code.morphisms.symm (HOLFrameEncoding.encodeHom (X.comp second first)) := by
  simp only [compositionValue, Equiv.apply_symm_apply, HOLFrameEncoding.comp_encoded]

#print axioms valid_map_values
#print axioms composition_encoded

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLIndexedQuantifiers
