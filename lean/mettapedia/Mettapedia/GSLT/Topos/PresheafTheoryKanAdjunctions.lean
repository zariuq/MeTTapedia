import Mettapedia.GSLT.Topos.PresheafTheoryActionCoherence
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Both Kan adjoints of theory inverse image

The set carrier includes the object and hom universes of both base
categories. Thus every actual comma diagram has its limit and colimit
in that carrier; existence of the Kan extensions is derived from these
constructions rather than supplied as a model assumption.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Topos.PresheafTheoryAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- Pointwise left Kan extension exists for every presheaf in the common
set carrier, including independently sized source and target categories. -/
instance leftKan_exists (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) :
    F.op.HasPointwiseLeftKanExtension P := fun _ => inferInstance

/-- The right Kan extension is obtained from actual comma-category limits. -/
instance rightKan_exists (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) :
    F.op.HasPointwiseRightKanExtension P := fun _ => inferInstance

def leftKan (F : C ⥤ D) :
    (Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) ⥤ (Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) := F.op.lan

def rightKan (F : C ⥤ D) :
    (Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) ⥤ (Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) := F.op.ran

def leftAdjunction (F : C ⥤ D) :
    leftKan F ⊣ (inverseImage F : (Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) ⥤ _) :=
  F.op.lanAdjunction _

def rightAdjunction (F : C ⥤ D) :
    (inverseImage F : (Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) ⥤ _) ⊣ rightKan F :=
  F.op.ranAdjunction _

def leftHomEquiv (F : C ⥤ D) (P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w))
    (Q : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) :
    ((leftKan F).obj P ⟶ Q) ≃ (P ⟶ (inverseImage F).obj Q) :=
  (leftAdjunction F).homEquiv P Q

def rightHomEquiv (F : C ⥤ D) (Q : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w))
    (P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) :
    ((inverseImage F).obj Q ⟶ P) ≃ (Q ⟶ (rightKan F).obj P) :=
  (rightAdjunction F).homEquiv Q P

/-- Universal left elimination extends the supplied map, with its complete
restriction readout equal to that same map. -/
theorem left_extension_readout (F : C ⥤ D)
    {P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)}
    {Q : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)} (map : P ⟶ (inverseImage F).obj Q) :
    (leftAdjunction F).unit.app P ≫
      (inverseImage F).map ((leftHomEquiv F P Q).symm map) = map := by
  exact ((leftAdjunction F).homEquiv_unit P Q _).symm.trans
    ((leftHomEquiv F P Q).apply_symm_apply map)

theorem left_extension_unique (F : C ⥤ D)
    {P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)}
    {Q : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)} (map : P ⟶ (inverseImage F).obj Q)
    (extension : (leftKan F).obj P ⟶ Q)
    (readout : (leftAdjunction F).unit.app P ≫ (inverseImage F).map extension = map) :
    extension = (leftHomEquiv F P Q).symm map := by
  apply (leftHomEquiv F P Q).injective
  rw [Equiv.apply_symm_apply]
  exact ((leftAdjunction F).homEquiv_unit P Q extension).trans readout

/-- Universal right introduction recovers the supplied map by the counit. -/
theorem right_extension_readout (F : C ⥤ D)
    {Q : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)}
    {P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)} (map : (inverseImage F).obj Q ⟶ P) :
    (inverseImage F).map (rightHomEquiv F Q P map) ≫
      (rightAdjunction F).counit.app P = map := by
  exact ((rightAdjunction F).homEquiv_counit Q P _).symm.trans
    ((rightHomEquiv F Q P).symm_apply_apply map)

theorem right_extension_unique (F : C ⥤ D)
    {Q : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)}
    {P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)} (map : (inverseImage F).obj Q ⟶ P)
    (extension : Q ⟶ (rightKan F).obj P)
    (readout : (inverseImage F).map extension ≫ (rightAdjunction F).counit.app P = map) :
    extension = rightHomEquiv F Q P map := by
  apply (rightHomEquiv F Q P).symm.injective
  rw [Equiv.symm_apply_apply]
  exact ((rightAdjunction F).homEquiv_counit Q P extension).trans readout

/-- The adjunction supplies all limits, independently of pointwise preservation. -/
theorem preservesLimitsFromLeftAdjunction (F : C ⥤ D) :
    PreservesLimitsOfSize.{max u₁ u₂ v₁ v₂ w,max u₁ u₂ v₁ v₂ w}
      (inverseImage F : (Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) ⥤ _) :=
  (leftAdjunction F).rightAdjoint_preservesLimits

/-- The other adjunction independently supplies all colimits and pushouts. -/
theorem preservesColimitsFromRightAdjunction (F : C ⥤ D) :
    PreservesColimitsOfSize.{max u₁ u₂ v₁ v₂ w,max u₁ u₂ v₁ v₂ w}
      (inverseImage F : (Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) ⥤ _) :=
  (rightAdjunction F).leftAdjoint_preservesColimits

end Mettapedia.GSLT.Topos.PresheafTheoryAction
