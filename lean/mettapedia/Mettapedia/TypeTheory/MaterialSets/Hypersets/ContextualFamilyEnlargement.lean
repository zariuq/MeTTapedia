import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseEnlargement
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialFamilies

/-!
# Whole-family decoding at larger material bounds

Enlargement retains every native family value, restriction and natural
section. Its actual material member functor uses the constructed bounded
inverse of the embedding. No representative of a quotient or member of a
merely inhabited fibre is selected.

The comparison works over an arbitrary category of parameters and is
stable under precomposition. It concerns an enlarged interpretation of a
given family; independent upper formation is a separate comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualFamilyEnlargement

open CategoryTheory

universe u v w z q

def model {T : Type u} (original : PresentedType T) : PresentedType (ULift.{v,u} T) where
  graph := original.graph.enlarge
  decode := (HSet.enlargedMembersEquiv.{u,v} original.carrier).symm.trans
    (original.decode.trans Equiv.ulift.symm)

theorem model_carrier {T : Type u} (original : PresentedType T) :
    (model.{u,v} original).carrier = HSet.enlarge original.carrier := rfl

theorem model_value {T : Type u} (original : PresentedType T) (term : ULift.{v,u} T) :
    (model.{u,v} original).value term = HSet.enlarge (original.value term.down) := rfl

theorem model_decode_enlarge {T : Type u} (original : PresentedType T)
    (member : {value : HSet.{u} // value ∈ original.carrier}) :
    (model.{u,v} original).decode (HSet.enlargedMembersEquiv original.carrier member) =
      ULift.up (original.decode member) := by
  change ULift.up (original.decode ((HSet.enlargedMembersEquiv.{u,v} original.carrier).symm
    (HSet.enlargedMembersEquiv original.carrier member))) = _
  rw [Equiv.symm_apply_apply]

variable {E : Type w} [Category.{z} E]
variable (family : E ⥤ Type u) (models : (point : E) → PresentedType (family.obj point))

def native : E ⥤ Type (max u v) where
  obj point := ULift.{v,u} (family.obj point)
  map step := TypeCat.ofHom fun term => ULift.up (family.map step term.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro term
    exact congrArg ULift.up (family.map_id_apply point term.down)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    intro term
    exact congrArg ULift.up (family.map_comp_apply first later term.down)

def members : E ⥤ Type (max u v + 1) where
  obj point := {value : HSet.{max u v} // value ∈ HSet.enlarge (models point).carrier}
  map {first second} step := TypeCat.ofHom fun member =>
    (model (models second)).decode.symm
      ((native family).map step ((model (models first)).decode member))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro member
    change (model (models point)).decode.symm
      ((native family).map (𝟙 point) ((model (models point)).decode member)) = member
    exact (congrArg (model (models point)).decode.symm
      ((native family).map_id_apply point ((model (models point)).decode member))).trans
        ((model (models point)).decode.symm_apply_apply member)
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro member
    change (model (models last)).decode.symm
      ((native family).map (earlier ≫ later) ((model (models first)).decode member)) =
      (model (models last)).decode.symm
        ((native family).map later ((model (models middle)).decode
          ((model (models middle)).decode.symm
            ((native family).map earlier ((model (models first)).decode member)))))
    have composite := (native family).map_comp_apply earlier later ((model (models first)).decode member)
    have inverse := (model (models middle)).decode.apply_symm_apply
      ((native family).map earlier ((model (models first)).decode member))
    exact (congrArg (model (models last)).decode.symm composite).trans
      (congrArg (fun term => (model (models last)).decode.symm ((native family).map later term)) inverse).symm

theorem member_decode {first second : E} (step : first ⟶ second)
    (member : (members.{u,v} family models).obj first) :
    (model (models second)).decode ((members family models).map step member) =
      (native family).map step ((model (models first)).decode member) :=
  (model (models second)).decode.apply_symm_apply _

theorem member_encode {first second : E} (step : first ⟶ second)
    (term : family.obj first) :
    (members.{u,v} family models).map step
        ((model (models first)).decode.symm (ULift.up term)) =
      (model (models second)).decode.symm (ULift.up (family.map step term)) := by
  change (model (models second)).decode.symm
    ((native family).map step ((model (models first)).decode
      ((model (models first)).decode.symm (ULift.up term)))) = _
  rw [Equiv.apply_symm_apply]
  rfl

def sectionEquiv : family.sections ≃ (members.{u,v} family models).sections where
  toFun term := ⟨fun point => (model (models point)).decode.symm (ULift.up (term.val point)), by
    intro first second step
    exact (member_encode family models step (term.val first)).trans
      (congrArg (fun value => (model (models second)).decode.symm (ULift.up value)) (term.property step))⟩
  invFun term := ⟨fun point => ((model (models point)).decode (term.val point)).down, by
    intro first second step
    exact (congrArg ULift.down (member_decode family models step (term.val first))).symm.trans
      (congrArg (fun member => ((model (models second)).decode member).down) (term.property step))⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    exact congrArg ULift.down ((model (models point)).decode.apply_symm_apply (ULift.up (term.val point)))
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (model (models point)).decode.symm_apply_apply (term.val point)

theorem sectionEquiv_value (term : family.sections) (point : E) :
    ((sectionEquiv.{u,v} family models term).val point).val =
      HSet.enlarge ((models point).value (term.val point)) := rfl

theorem sectionEquiv_decode (term : family.sections) (point : E) :
    (model (models point)).decode ((sectionEquiv.{u,v} family models term).val point) =
      ULift.up (term.val point) := (model (models point)).decode.apply_symm_apply _

/-- Whole natural sections at two material bounds, compared through their
actual native values. Enlarging a carrier does not introduce new members. -/
def cumulativeSections :
    (members.{u,v} family models).sections ≃ (members.{u,max v q} family models).sections :=
  (sectionEquiv.{u,v} family models).symm.trans (sectionEquiv.{u,max v q} family models)

theorem cumulativeSections_value (term : (members.{u,v} family models).sections) (point : E) :
    ((cumulativeSections.{u,v,w,z,q} family models term).val point).val =
      HSet.enlarge.{max u v,q} (term.val point).val := by
  change HSet.enlarge.{u,max v q}
    ((models point).value (((model.{u,v} (models point)).decode (term.val point)).down)) = _
  have restored := congrArg Subtype.val
    ((model.{u,v} (models point)).decode.symm_apply_apply (term.val point))
  change HSet.enlarge.{u,v}
    ((models point).value (((model.{u,v} (models point)).decode (term.val point)).down)) =
      (term.val point).val at restored
  exact (HSet.enlarge_comp.{u,v,q} _).symm.trans (congrArg HSet.enlarge.{max u v,q} restored)

universe r

theorem cumulativeSections_comp (term : (members.{u,v} family models).sections) :
    cumulativeSections.{u,max v q,w,z,r} family models
      (cumulativeSections.{u,v,w,z,q} family models term) =
        cumulativeSections.{u,v,w,z,max q r} family models term := by
  apply Subtype.ext
  funext point
  apply Subtype.ext
  rw [cumulativeSections_value, cumulativeSections_value, cumulativeSections_value]
  exact HSet.enlarge_comp _

section Restriction

variable {F : Type q} [Category.{z} F] (change : F ⥤ E)

def pullSection (term : family.sections) : (Mettapedia.TypeTheory.ContextualSmallFamilyUniverse.restrict change family).sections :=
  ⟨fun point => term.val (change.obj point), fun step => term.property (change.map step)⟩

theorem members_restrict :
    members.{u,v} (Mettapedia.TypeTheory.ContextualSmallFamilyUniverse.restrict change family) (fun point => models (change.obj point)) =
      Mettapedia.TypeTheory.ContextualSmallFamilyUniverse.restrict change (members.{u,v} family models) := rfl

theorem section_restrict (term : family.sections) (point : F) :
    (sectionEquiv.{u,v} (Mettapedia.TypeTheory.ContextualSmallFamilyUniverse.restrict change family) (fun point => models (change.obj point))
      (pullSection family change term)).val point =
        (sectionEquiv.{u,v} family models term).val (change.obj point) := rfl

end Restriction

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualFamilyEnlargement
