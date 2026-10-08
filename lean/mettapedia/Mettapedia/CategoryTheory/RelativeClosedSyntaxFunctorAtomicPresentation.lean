import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationCells

/-!
# Independently selected primitive presentations of a weak closed map

An actual natural isomorphism on the embedded base and an isomorphism at
each fresh object select their independent target meanings. Other raw
objects retain their original images. The resulting functor is constructed
by actual isomorphism conjugation; its complete natural comparison, base
readout, finite-limit preservation and closedness are consequences.

No arrow declaration, expression interpretation or extension universal
property is part of this primitive presentation data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.AtomicPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable (mapping : Object signature ⥤ D) (meanings : Assignment C symbols D)

structure PrimitiveImages where
  base : baseFunctor signature ⋙ mapping ≅ meanings.base
  object (origin : symbols.ObjectName) : mapping.obj (namedObject origin) ≅ meanings.object origin

variable (images : PrimitiveImages mapping meanings)

def image (source : Object signature) : ObjectImage mapping source := by
  rcases source with ⟨code, formed⟩
  cases code with
  | base object => exact ⟨meanings.base.obj object, images.base.app object⟩
  | name origin => exact ⟨meanings.object origin, images.object origin⟩
  | terminal => exact ⟨mapping.obj ⟨.terminal, formed⟩, Iso.refl _⟩
  | product first second => exact ⟨mapping.obj ⟨.product first second, formed⟩, Iso.refl _⟩
  | exponential argument result => exact ⟨mapping.obj ⟨.exponential argument result, formed⟩, Iso.refl _⟩
  | equalizer source target first second =>
      exact ⟨mapping.obj ⟨.equalizer source target first second, formed⟩, Iso.refl _⟩

def functor : Object signature ⥤ D :=
  mapping.copyObj (fun source => (image mapping meanings images source).value)
    (fun source => (image mapping meanings images source).comparison)

def comparison : mapping ≅ functor mapping meanings images :=
  mapping.isoCopyObj (fun source => (image mapping meanings images source).value)
    (fun source => (image mapping meanings images source).comparison)

theorem image_base (object : C) : image mapping meanings images (baseObject signature object) =
    ⟨meanings.base.obj object, images.base.app object⟩ := rfl

theorem image_name (origin : symbols.ObjectName) : image mapping meanings images (namedObject origin) =
    ⟨meanings.object origin, images.object origin⟩ := rfl

@[simp] theorem functor_base_object (object : C) :
    (functor mapping meanings images).obj (baseObject signature object) = meanings.base.obj object := rfl

@[simp] theorem functor_named_object (origin : symbols.ObjectName) :
    (functor mapping meanings images).obj (namedObject origin) = meanings.object origin := rfl

theorem functor_map {source target : Object signature} (arrow : source ⟶ target) :
    (functor mapping meanings images).map arrow =
      (image mapping meanings images source).comparison.inv ≫ mapping.map arrow ≫
        (image mapping meanings images target).comparison.hom := rfl

theorem comparison_hom_base (object : C) :
    (comparison mapping meanings images).hom.app (baseObject signature object) = images.base.hom.app object := rfl

theorem comparison_hom_name (origin : symbols.ObjectName) :
    (comparison mapping meanings images).hom.app (namedObject origin) = (images.object origin).hom := rfl

theorem functor_base : baseFunctor signature ⋙ functor mapping meanings images = meanings.base := by
  refine _root_.CategoryTheory.Functor.ext (fun object => functor_base_object mapping meanings images object) ?_
  intro source target arrow
  change images.base.inv.app source ≫ mapping.map (baseArrow arrow) ≫ images.base.hom.app target =
    𝟙 _ ≫ meanings.base.map arrow ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  have natural := images.base.hom.naturality arrow
  change mapping.map (baseArrow arrow) ≫ images.base.hom.app target =
    images.base.hom.app source ≫ meanings.base.map arrow at natural
  rw [natural, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]

instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor mapping meanings images) :=
  preservesFiniteLimits_of_natIso (comparison mapping meanings images)

instance functor_closed : MonoidalClosedFunctor (functor mapping meanings images) :=
  CartesianClosedFunctorCoherence.closed_of_naturalIso (comparison mapping meanings images).symm

end Mettapedia.CategoryTheory.RelativeClosedSyntax.AtomicPresentation
