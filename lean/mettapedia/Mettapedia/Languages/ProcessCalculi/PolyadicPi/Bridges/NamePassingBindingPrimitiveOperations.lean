import Mettapedia.OSLF.Syntax.BindingClosedGeneratedModel
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperations

/-!
# Ordinary source constructors from complete binding operator domains

The source's independent value and term objects are retained. Empty-binder
arguments are supplied through currying, and the full one-value body is
precomposed with the actual right unitor. This recovers the five ordinary
constructor arrows without imposing a continuation representation on the
source objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingPrimitiveOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingContinuationOperations
open NamePassingBindingClosedOperations (generated emptyValue empty_curry boundValue)

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (binding : ClosedPresentation.Operations NamePassing.Presentation.signature C)

def names : C := binding.sort .nm
def terms : C := binding.sort .tm
def bodies : C := names binding ⟶[C] terms binding

def plain (result : NamePassing.Presentation.Srt) :
    binding.sort result ⟶ (𝟙_ C ⟶[C] binding.sort result) :=
  MonoidalClosed.curry (snd (𝟙_ C) (binding.sort result))

def bound : bodies binding ⟶ ((names binding ⊗ 𝟙_ C) ⟶[C] terms binding) :=
  (MonoidalClosed.pre (ρ_ (names binding)).hom).app (terms binding)

def reference : names binding ⟶ terms binding :=
  lift (plain binding .nm) (toUnit _) ≫ binding.operation NamePassing.Presentation.Operator.reference

def abstraction : bodies binding ⟶ terms binding :=
  lift (bound binding) (toUnit _) ≫ binding.operation NamePassing.Presentation.Operator.abstraction

def application : terms binding ⊗ names binding ⟶ terms binding :=
  lift (fst _ _ ≫ plain binding .tm)
    (lift (snd _ _ ≫ plain binding .nm) (toUnit _)) ≫ binding.operation NamePassing.Presentation.Operator.application

def definition : terms binding ⊗ bodies binding ⟶ terms binding :=
  lift (fst _ _ ≫ plain binding .tm)
    (lift (snd _ _ ≫ bound binding) (toUnit _)) ≫ binding.operation NamePassing.Presentation.Operator.definition

def carrier : names binding ⊗ (terms binding ⊗ terms binding) ⟶ terms binding :=
  lift (fst _ _ ≫ plain binding .nm)
    (lift (snd _ _ ≫ fst _ _ ≫ plain binding .tm)
      (lift (snd _ _ ≫ snd _ _ ≫ plain binding .tm) (toUnit _))) ≫
        binding.operation NamePassing.Presentation.Operator.carrier

theorem plain_recovers (result : NamePassing.Presentation.Srt) :
    plain binding result ≫ emptyValue (binding.sort result) = 𝟙 (binding.sort result) := by
  simpa only [plain, Category.comp_id] using empty_curry (𝟙 (binding.sort result))

@[reassoc] theorem unit_recovers (object : C) :
    MonoidalClosed.curry (snd (𝟙_ C) object) ≫ emptyValue object = 𝟙 object := by
  simpa only [Category.comp_id] using empty_curry (𝟙 object)

variable (primitives : Operations C)

theorem generated_bound_recovers : bound (generated primitives) ≫ boundValue primitives =
    𝟙 primitives.boundBodyObject := by
  change (MonoidalClosed.pre (ρ_ primitives.names).hom).app primitives.termObject ≫
    (MonoidalClosed.pre (ρ_ primitives.names).inv).app primitives.termObject = _
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.inv_hom_id,
    MonoidalClosed.pre_id]
  rfl

theorem generated_reference : reference (generated primitives) = primitives.reference := by
  change lift (MonoidalClosed.curry (snd (𝟙_ C) primitives.names)) (toUnit primitives.names) ≫
    fst _ _ ≫ emptyValue primitives.names ≫ primitives.reference = _
  rw [lift_fst_assoc, ← Category.assoc, unit_recovers, Category.id_comp]

theorem generated_abstraction : abstraction (generated primitives) = primitives.abstraction := by
  have read := generated_bound_recovers primitives
  change (MonoidalClosed.pre (ρ_ primitives.names).hom).app primitives.termObject ≫
    boundValue primitives = 𝟙 primitives.boundBodyObject at read
  change lift ((MonoidalClosed.pre (ρ_ primitives.names).hom).app primitives.termObject)
    (toUnit primitives.boundBodyObject) ≫ fst _ _ ≫ boundValue primitives ≫ primitives.abstraction = _
  rw [lift_fst_assoc, ← Category.assoc, read, Category.id_comp]

theorem generated_application : application (generated primitives) = primitives.application := by
  change lift (fst primitives.termObject primitives.names ≫ MonoidalClosed.curry (snd (𝟙_ C) primitives.termObject))
    (lift (snd primitives.termObject primitives.names ≫ MonoidalClosed.curry (snd (𝟙_ C) primitives.names))
      (toUnit _)) ≫
      (lift (fst _ _ ≫ emptyValue primitives.termObject)
        (snd _ _ ≫ fst _ _ ≫ emptyValue primitives.names) ≫ primitives.application) = _
  rw [← Category.assoc, comp_lift]
  simp only [Category.assoc, lift_fst_assoc, lift_snd_assoc]
  rw [unit_recovers, unit_recovers]
  simp only [Category.comp_id, lift_fst_snd, Category.id_comp]

theorem generated_definition : definition (generated primitives) = primitives.definition := by
  have read := generated_bound_recovers primitives
  change (MonoidalClosed.pre (ρ_ primitives.names).hom).app primitives.termObject ≫
    boundValue primitives = 𝟙 primitives.boundBodyObject at read
  change lift (fst primitives.termObject primitives.boundBodyObject ≫ MonoidalClosed.curry (snd (𝟙_ C) primitives.termObject))
    (lift (snd primitives.termObject primitives.boundBodyObject ≫
      (MonoidalClosed.pre (ρ_ primitives.names).hom).app primitives.termObject) (toUnit _)) ≫
      (lift (fst _ _ ≫ emptyValue primitives.termObject)
        (snd _ _ ≫ fst _ _ ≫ boundValue primitives) ≫ primitives.definition) = _
  rw [← Category.assoc, comp_lift]
  simp only [Category.assoc, lift_fst_assoc, lift_snd_assoc]
  rw [unit_recovers, read]
  simp only [Category.comp_id, lift_fst_snd, Category.id_comp]

theorem generated_carrier : carrier (generated primitives) = primitives.carrier := by
  change lift (fst primitives.names (primitives.termObject ⊗ primitives.termObject) ≫
      MonoidalClosed.curry (snd (𝟙_ C) primitives.names))
    (lift (snd primitives.names (primitives.termObject ⊗ primitives.termObject) ≫ fst _ _ ≫
      MonoidalClosed.curry (snd (𝟙_ C) primitives.termObject))
      (lift (snd primitives.names (primitives.termObject ⊗ primitives.termObject) ≫ snd _ _ ≫
        MonoidalClosed.curry (snd (𝟙_ C) primitives.termObject)) (toUnit _))) ≫
      (lift (fst _ _ ≫ emptyValue primitives.names)
        (lift (snd _ _ ≫ fst _ _ ≫ emptyValue primitives.termObject)
          (snd _ _ ≫ snd _ _ ≫ fst _ _ ≫ emptyValue primitives.termObject)) ≫ primitives.carrier) = _
  rw [← Category.assoc, comp_lift, comp_lift]
  simp only [Category.assoc, lift_fst_assoc, lift_snd_assoc]
  rw [unit_recovers, unit_recovers]
  simp only [Category.comp_id, ← comp_lift, lift_fst_snd, Category.id_comp]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingPrimitiveOperations
