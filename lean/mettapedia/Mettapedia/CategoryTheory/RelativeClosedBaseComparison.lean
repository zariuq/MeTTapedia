import Mettapedia.CategoryTheory.RelativeClosedBaseComparisonSignature
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Actual isomorphisms from the authored base comparison diagrams

Each local inverse declaration and its two generated equations yield a real
category isomorphism. In the terminal and product cases its forward map is
the canonical comparison, earning preservation rather than assuming it.
Equalizer comparisons retain the authored defining arrows. Exponential
comparisons retain the product transport preceding the supplied evaluation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe u v

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

def formalObject (choice : Choice C) : Object (signature (C := C)) :=
  ⟨sourceCode choice, ⟨sourceFormation choice⟩⟩

def oldObject (choice : Choice C) : Object (signature (C := C)) :=
  baseObject (signature (C := C)) (selected choice)

def forwardRaw (choice : Choice C) : RawHom (oldObject choice) (formalObject choice) :=
  ⟨forwardCode choice, ⟨forwardTyped choice⟩⟩

def inverseRaw (choice : Choice C) : RawHom (formalObject choice) (oldObject choice) :=
  ⟨.name choice, ⟨inverseTyped choice⟩⟩

def comparison (choice : Choice C) : oldObject choice ≅ formalObject choice where
  hom := classOf (forwardRaw choice)
  inv := classOf (inverseRaw choice)
  hom_inv_id := Quotient.sound ⟨.declaredEquation (signature := signature (C := C))
    (choice, false) (leftTyped (choice, false)) (rightTyped (choice, false))⟩
  inv_hom_id := Quotient.sound ⟨.declaredEquation (signature := signature (C := C))
    (choice, true) (leftTyped (choice, true)) (rightTyped (choice, true))⟩

abbrev base : C ⥤ Object (signature (C := C)) := baseFunctor (signature (C := C))

theorem terminal_comparison_hom :
    (comparison (C := C) .terminal).hom = CartesianMonoidalCategory.terminalComparison (base (C := C)) := by
  apply toTerminal_unique

instance terminalComparison_isIso :
    IsIso (CartesianMonoidalCategory.terminalComparison (base (C := C))) := by
  rw [← terminal_comparison_hom]
  exact (comparison (C := C) .terminal).isIso_hom

instance base_preservesTerminal : PreservesLimit (Functor.empty.{0} C) (base (C := C)) :=
  CartesianMonoidalCategory.preservesLimit_empty_of_isIso_terminalComparison (base (C := C))

@[simp] theorem product_comparison_first (first second : C) :
    (comparison (.product first second)).hom ≫
      GeneratedCategory.first ((base (C := C)).obj first) ((base (C := C)).obj second) =
        (base (C := C)).map (CartesianMonoidalCategory.fst first second) :=
  Quotient.sound ⟨.firstBeta (.baseObject first) (.baseObject second)
    (.baseArrow (CartesianMonoidalCategory.fst first second))
    (.baseArrow (CartesianMonoidalCategory.snd first second))⟩

@[simp] theorem product_comparison_second (first second : C) :
    (comparison (.product first second)).hom ≫
      GeneratedCategory.second ((base (C := C)).obj first) ((base (C := C)).obj second) =
        (base (C := C)).map (CartesianMonoidalCategory.snd first second) :=
  Quotient.sound ⟨.secondBeta (.baseObject first) (.baseObject second)
    (.baseArrow (CartesianMonoidalCategory.fst first second))
    (.baseArrow (CartesianMonoidalCategory.snd first second))⟩

theorem product_comparison_hom (first second : C) :
    (comparison (.product first second)).hom =
      CartesianMonoidalCategory.prodComparison (base (C := C)) first second := by
  apply product_joint_cancel (source := (base (C := C)).obj (first ⊗ second))
    (left := (base (C := C)).obj first) (right := (base (C := C)).obj second)
  · exact (product_comparison_first first second).trans
      (CartesianMonoidalCategory.prodComparison_fst (base (C := C)) first second).symm
  · exact (product_comparison_second first second).trans
      (CartesianMonoidalCategory.prodComparison_snd (base (C := C)) first second).symm

instance productComparison_isIso (first second : C) :
    IsIso (CartesianMonoidalCategory.prodComparison (base (C := C)) first second) := by
  rw [← product_comparison_hom]
  exact (comparison (.product first second)).isIso_hom

instance base_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (base (C := C)) :=
  CartesianMonoidalCategory.preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison
    (base (C := C))

instance base_preservesEmpty : PreservesLimitsOfShape (Discrete PEmpty.{1}) (base (C := C)) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal (base (C := C))

instance base_preservesFiniteProducts : PreservesFiniteProducts (base (C := C)) :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal (base (C := C))

def equalizerBefore {source target : C} (before : source ⟶ target) :
    RawHom ((base (C := C)).obj source) ((base (C := C)).obj target) :=
  ⟨.base before, ⟨.baseArrow before⟩⟩

def equalizerPresentation {source target : C} (before after : source ⟶ target) :
    formalObject (.equalizer before after) ≅
      equalizerObject ((base (C := C)).map before) ((base (C := C)).map after) :=
  PresentedEqualizer.chosenComparison (equalizerBefore before) (equalizerBefore after)

def completeEqualizerComparison {source target : C} (before after : source ⟶ target) :
    (base (C := C)).obj (Limits.equalizer before after) ≅
      equalizerObject ((base (C := C)).map before) ((base (C := C)).map after) :=
  comparison (.equalizer before after) ≪≫ equalizerPresentation before after

theorem equalizer_comparison_inclusion {source target : C} (before after : source ⟶ target) :
    (comparison (.equalizer before after)).hom ≫
      PresentedEqualizer.inclusion (equalizerBefore before) (equalizerBefore after) =
        (base (C := C)).map (equalizer.ι before after) :=
  Quotient.sound ⟨.equalizerBeta (.baseObject source) (.baseObject target)
    (.baseObject (Limits.equalizer before after)) (.baseArrow before) (.baseArrow after)
    (.baseArrow (equalizer.ι before after)) (baseEqualizerCondition before after)⟩

@[simp] theorem completeEqualizerComparison_inclusion {source target : C}
    (before after : source ⟶ target) :
    (completeEqualizerComparison before after).hom ≫
      equalizerInclusion ((base (C := C)).map before) ((base (C := C)).map after) =
        (base (C := C)).map (equalizer.ι before after) := by
  have read : (equalizerPresentation before after).hom ≫
      equalizerInclusion ((base (C := C)).map before) ((base (C := C)).map after) =
        PresentedEqualizer.inclusion (equalizerBefore before) (equalizerBefore after) :=
    PresentedEqualizer.chosenComparison_hom_inclusion (equalizerBefore before) (equalizerBefore after)
  exact (Category.assoc (comparison (.equalizer before after)).hom
    (equalizerPresentation before after).hom
    (equalizerInclusion ((base (C := C)).map before) ((base (C := C)).map after))).trans
      ((congrArg (fun outgoing : formalObject (.equalizer before after) ⟶ (base (C := C)).obj source =>
        (comparison (.equalizer before after)).hom ≫ outgoing) read).trans
          (equalizer_comparison_inclusion before after))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons
