import Mettapedia.OSLF.Syntax.FiniteLimitShapes
import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedYoneda
import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Yoneda

/-!
# Formal finite-limit objects of a small category

The standard route to free finite limits takes the opposite of the
finite-colimit closure of covariant representables. This file constructs that
object category, its finite limits, and the fully faithful base embedding.
Its functor-extension universal property is a separate obligation.

This differs from closing contravariant representables under limits in a
presheaf category: that latter construction preserves limits which happened
to exist already in the base, and is useful as an ambient semantic model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.FormalFiniteLimits

open CategoryTheory
open CategoryTheory.Limits
open Mettapedia.OSLF.Binding

variable (C : Type) [SmallCategory C]

abbrev CovariantPresheaf := C ⥤ Type

/-- The large empty index matches the empty cocone used by `IsInitial`;
the small empty index is the one used by `HasInitial`. Both present the
same mathematical empty diagram. -/
inductive FiniteColimitShape where
  | initialSmall | initial | binaryCoproduct | coequalizer

def finiteColimitDiagram : FiniteColimitShape → Type _
  | .initialSmall => Discrete PEmpty
  | .initial => Discrete PEmpty.{1}
  | .binaryCoproduct => Discrete WalkingPair
  | .coequalizer => WalkingParallelPair

instance (shape : FiniteColimitShape) : Category (finiteColimitDiagram shape) := by
  cases shape <;> dsimp [finiteColimitDiagram] <;> infer_instance

def Corepresentable : ObjectProperty (CovariantPresheaf C) :=
  fun F => F.IsCorepresentable

def FiniteColimitGenerated : ObjectProperty (CovariantPresheaf C) :=
  (Corepresentable C).colimitsClosure finiteColimitDiagram

/-- The object category with the variance required for formal finite limits. -/
abbrev Objects := (FiniteColimitGenerated C).FullSubcategoryᵒᵖ

theorem corepresented (X : Cᵒᵖ) :
    FiniteColimitGenerated C (coyoneda.obj X) := by
  apply ObjectProperty.colimitsClosure.of_mem
  change (coyoneda.obj X).IsCorepresentable
  infer_instance

instance : HasInitial (FiniteColimitGenerated C).FullSubcategory := by
  change HasColimitsOfShape (finiteColimitDiagram FiniteColimitShape.initialSmall)
    (FiniteColimitGenerated C).FullSubcategory
  have : (FiniteColimitGenerated C).IsClosedUnderColimitsOfShape
      (finiteColimitDiagram FiniteColimitShape.initialSmall) := by
    unfold FiniteColimitGenerated
    infer_instance
  exact hasColimitsOfShape_of_closedUnderColimits
    (finiteColimitDiagram FiniteColimitShape.initialSmall) (FiniteColimitGenerated C)

instance : HasBinaryCoproducts (FiniteColimitGenerated C).FullSubcategory := by
  change HasColimitsOfShape (finiteColimitDiagram FiniteColimitShape.binaryCoproduct)
    (FiniteColimitGenerated C).FullSubcategory
  have : (FiniteColimitGenerated C).IsClosedUnderColimitsOfShape
      (finiteColimitDiagram FiniteColimitShape.binaryCoproduct) := by
    unfold FiniteColimitGenerated
    infer_instance
  exact hasColimitsOfShape_of_closedUnderColimits
    (finiteColimitDiagram FiniteColimitShape.binaryCoproduct) (FiniteColimitGenerated C)

instance : HasCoequalizers (FiniteColimitGenerated C).FullSubcategory := by
  change HasColimitsOfShape (finiteColimitDiagram FiniteColimitShape.coequalizer)
    (FiniteColimitGenerated C).FullSubcategory
  have : (FiniteColimitGenerated C).IsClosedUnderColimitsOfShape
      (finiteColimitDiagram FiniteColimitShape.coequalizer) := by
    unfold FiniteColimitGenerated
    infer_instance
  exact hasColimitsOfShape_of_closedUnderColimits
    (finiteColimitDiagram FiniteColimitShape.coequalizer) (FiniteColimitGenerated C)

theorem hasFiniteColimits :
    HasFiniteColimits (FiniteColimitGenerated C).FullSubcategory := by
  have : HasFiniteCoproducts (FiniteColimitGenerated C).FullSubcategory :=
    hasFiniteCoproducts_of_has_binary_and_initial
  exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

instance : HasFiniteColimits (FiniteColimitGenerated C).FullSubcategory :=
  hasFiniteColimits C

instance : HasFiniteLimits (Objects C) := by
  dsimp [Objects]
  infer_instance

/-- The covariant Yoneda embedding, restricted to the generated objects. -/
def restrictedCoyoneda :
    Cᵒᵖ ⥤ (FiniteColimitGenerated C).FullSubcategory :=
  (FiniteColimitGenerated C).lift coyoneda (fun X => corepresented C X)

/-- The formal base embedding reverses the covariant Yoneda variance. -/
abbrev base : C ⥤ Objects C := (restrictedCoyoneda C).rightOp

instance : (restrictedCoyoneda C).Faithful := by
  dsimp [restrictedCoyoneda]
  infer_instance

instance : (restrictedCoyoneda C).Full := by
  dsimp [restrictedCoyoneda]
  infer_instance

instance : (base C).Faithful := by
  dsimp [base]
  infer_instance

instance : (base C).Full := by
  dsimp [base]
  infer_instance

/-- No covariant representable is initial: its identity element cannot map
to the empty covariant presheaf. -/
theorem corepresentable_not_initial (X : C) :
    IsInitial (coyoneda.obj (Opposite.op X) : CovariantPresheaf C) → False := by
  intro initial
  let empty : CovariantPresheaf C := (Functor.const C).obj PEmpty
  have impossible : PEmpty := (initial.to empty).app X (𝟙 X)
  exact impossible.elim

private def emptyFunctor : CovariantPresheaf C := (Functor.const C).obj PEmpty

private theorem empty_in_generated : FiniteColimitGenerated C (emptyFunctor C) := by
  have : (FiniteColimitGenerated C).IsClosedUnderColimitsOfShape
      (finiteColimitDiagram FiniteColimitShape.initial) := by
    unfold FiniteColimitGenerated
    infer_instance
  exact (FiniteColimitGenerated C).prop_of_isColimit
    (J := finiteColimitDiagram FiniteColimitShape.initial)
    (Functor.isInitialConst C (Types.isInitialPEmpty : IsInitial (PEmpty : Type)))
    (fun j => j.as.elim)

private def emptyObject : (FiniteColimitGenerated C).FullSubcategory :=
  ⟨emptyFunctor C, empty_in_generated C⟩

/-- The formal embedding does not turn a base object into a terminal object.
Thus it need not preserve an existing terminal object of the base. -/
theorem base_object_not_terminal (X : C) :
    IsTerminal ((base C).obj X) → False := by
  intro terminal
  have initial : IsInitial ((restrictedCoyoneda C).obj (Opposite.op X)) :=
    terminal.unop
  have impossible : PEmpty := (initial.to (emptyObject C)).hom.app X (𝟙 X)
  exact impossible.elim

/-- Even if the base already has a terminal object, the formal embedding
does not force that object to remain terminal. -/
theorem base_not_preserves_terminal [HasTerminal C] :
    ¬ PreservesLimit (Functor.empty.{0} C) (base C) := by
  intro preserves
  have : PreservesLimit (Functor.empty.{0} C) (base C) := preserves
  exact base_object_not_terminal C (⊤_ C)
    (isLimitOfHasTerminalOfPreservesLimit (base C))

/-- The earlier ambient Yoneda closure cannot have the ordinary free
finite-limit universal property over all context functors: the genuine formal
embedding is a concrete source functor for which no such lex extension exists. -/
theorem no_lex_extension_from_ambient [HasTerminal C]
    (extension : (Mettapedia.OSLF.FiniteLimitYoneda.Generated C).FullSubcategory
      ⥤ Objects C)
    [PreservesFiniteLimits extension]
    (comparison :
      Mettapedia.OSLF.FiniteLimitYoneda.intoGenerated C ⋙ extension ≅ base C) :
    False := by
  have : PreservesFiniteProducts
      (Mettapedia.OSLF.FiniteLimitYoneda.intoGenerated C) :=
    Mettapedia.OSLF.FiniteLimitYoneda.intoGenerated_preservesFiniteProducts C
  have : PreservesLimit (Functor.empty.{0} C)
      (Mettapedia.OSLF.FiniteLimitYoneda.intoGenerated C ⋙ extension) := by
    infer_instance
  exact base_not_preserves_terminal C
    (preservesLimit_of_natIso (Functor.empty.{0} C) comparison)

/-- Minimality is an object-level property; extension of functors requires a
separate universal-property proof. -/
theorem least (Q : ObjectProperty (CovariantPresheaf C))
    [Q.IsClosedUnderIsomorphisms]
    [∀ shape, Q.IsClosedUnderColimitsOfShape (finiteColimitDiagram shape)]
    (h : Corepresentable C ≤ Q) : FiniteColimitGenerated C ≤ Q :=
  ObjectProperty.colimitsClosure_le h

end Mettapedia.OSLF.FormalFiniteLimits
