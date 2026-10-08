import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalization

/-!
# Readouts of constructor-built native choices

These equations retain both the complete target object and its comparison
with the supplied functor image. In particular, a displayed equalizer is
normalized using its actual two authored arrows rather than replacing their
raw presentations by independently selected representatives.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping]

theorem objectImage_base (object : C) :
    objectImage mapping (baseObject signature object) =
      ⟨mapping.obj (baseObject signature object), Iso.refl _⟩ := by
  rw [objectImage]
  rfl

theorem objectImage_named (origin : symbols.ObjectName) :
    objectImage mapping (namedObject origin) =
      ⟨mapping.obj (namedObject origin), Iso.refl _⟩ := by
  rw [objectImage]
  rfl

theorem objectImage_terminal :
    objectImage mapping (terminal signature) =
      ⟨𝟙_ D, asIso (CartesianMonoidalCategory.terminalComparison mapping)⟩ := by
  rw [objectImage]
  rfl

theorem objectImage_product (first second : Object signature) :
    objectImage mapping (product first second) =
      ⟨(objectImage mapping first).value ⊗ (objectImage mapping second).value,
        asIso (CartesianMonoidalCategory.prodComparison mapping first second) ≪≫
          tensorIso (objectImage mapping first).comparison
            (objectImage mapping second).comparison⟩ := by
  rw [objectImage]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem objectImage_exponential (argument result : Object signature) :
    objectImage mapping (exponentialObject argument result) =
      ⟨(objectImage mapping argument).value ⟶[D] (objectImage mapping result).value,
        asIso ((expComparison mapping argument).natTrans.app result) ≪≫
          functionIso (objectImage mapping argument).comparison
            (objectImage mapping result).comparison⟩ := by
  rw [objectImage]
  rfl

theorem objectImage_equalizer {source target : Object signature}
    (first second : RawHom source target) :
    objectImage mapping (PresentedEqualizer.object first second) =
      ⟨equalizer ((normalizedFunctor mapping).map (classOf first))
          ((normalizedFunctor mapping).map (classOf second)),
        mappedPresentedIso mapping first second ≪≫
          equalizerTransport (mapping.map (classOf first)) (mapping.map (classOf second))
            (objectImage mapping source).comparison
              (objectImage mapping target).comparison⟩ := by
  rw [objectImage]
  rfl

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
