import Mettapedia.OSLF.Syntax.CategoricalBindingTargetCoherence
import Mettapedia.OSLF.Syntax.CategoricalBindingClosedTargetChange
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Diagonal change of target

The diagonal functor sends every object and arrow to two copies. It preserves
limits and every selected exponential. The exponential universal property is
verified at arbitrary pairs of stages, including pairs outside the image of
this functor.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingDiagonalTargetControl

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel

universe u v w w'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- The terminal object in the product category, chosen componentwise. -/
def productTerminal : IsTerminal (𝟙_ (D × D)) :=
  IsTerminal.ofUniqueHom (fun X => (toUnit X.1, toUnit X.2)) (by
    intro X m
    exact Prod.hom_ext (toUnit_unique _ _) (toUnit_unique _ _))

/-- Binary products in the product category are chosen componentwise. -/
instance productCartesian : CartesianMonoidalCategory (D × D) where
  toMonoidalCategory := MonoidalCategory.prodMonoidal D D
  isTerminalTensorUnit := productTerminal
  fst X Y := (fst X.1 Y.1, fst X.2 Y.2)
  snd X Y := (snd X.1 Y.1, snd X.2 Y.2)
  fst_def X Y := by
    apply Prod.hom_ext <;> dsimp [productTerminal, IsTerminal.ofUniqueHom]
    · exact fst_def _ _
    · exact fst_def _ _
  snd_def X Y := by
    apply Prod.hom_ext <;> dsimp [productTerminal, IsTerminal.ofUniqueHom]
    · exact snd_def _ _
    · exact snd_def _ _
  tensorProductIsBinaryProduct X Y :=
    BinaryFan.isLimitMk
      (fun s => (lift s.fst.1 s.snd.1, lift s.fst.2 s.snd.2))
      (fun s => Prod.hom_ext (lift_fst _ _) (lift_fst _ _))
      (fun s => Prod.hom_ext (lift_snd _ _) (lift_snd _ _))
      (by
        intro s m hf hs
        apply Prod.hom_ext
        · apply hom_ext
          · exact (congrArg (fun f => f.1) hf).trans (lift_fst _ _).symm
          · exact (congrArg (fun f => f.1) hs).trans (lift_snd _ _).symm
        · apply hom_ext
          · exact (congrArg (fun f => f.2) hf).trans (lift_fst _ _).symm
          · exact (congrArg (fun f => f.2) hs).trans (lift_snd _ _).symm)

/-- A target change sending each object and morphism to two copies. -/
def diagonal (D : Type u) [Category.{v} D] : D ⥤ D × D where
  obj X := (X, X)
  map f := (f, f)

variable {J : Type w} [Category.{w'} J]

/-- The diagonal preserves a limit by using its two universal lifts. -/
def diagonalMapLimit {F : J ⥤ D} {c : Cone F} (hc : IsLimit c) :
    IsLimit ((diagonal D).mapCone c) where
  lift s := (hc.lift ((CategoryTheory.Prod.fst D D).mapCone s), hc.lift ((CategoryTheory.Prod.snd D D).mapCone s))
  fac s j := Prod.hom_ext (hc.fac _ j) (hc.fac _ j)
  uniq s m hm := by
    apply Prod.hom_ext
    · apply hc.uniq ((CategoryTheory.Prod.fst D D).mapCone s) m.1
      intro j
      exact congrArg (fun f => f.1) (hm j)
    · apply hc.uniq ((CategoryTheory.Prod.snd D D).mapCone s) m.2
      intro j
      exact congrArg (fun f => f.2) (hm j)

instance diagonalPreservesLimit (F : J ⥤ D) : PreservesLimit F (diagonal D) :=
  PreservesLimit.mk (fun hc => ⟨diagonalMapLimit hc⟩)

instance diagonalPreservesLimitsOfShape : PreservesLimitsOfShape J (diagonal D) where
  preservesLimit := inferInstance

instance diagonalPreservesLimits : PreservesLimitsOfSize.{w', w} (diagonal D) where
  preservesLimitsOfShape := inferInstance

/-- The product comparison of the diagonal is the actual identity arrow. -/
@[simp] theorem diagonal_productComparison (C P : D) :
    CartesianMonoidalCategory.prodComparison (diagonal D) C P = 𝟙 (C ⊗ P, C ⊗ P) := by
  apply hom_ext <;> apply Prod.hom_ext <;> simp [CartesianMonoidalCategory.prodComparison, diagonal] <;> rfl

/-- The inverse product comparison is also the actual identity. -/
@[simp] theorem diagonal_productComparison_inv (C P : D) :
    inv (CartesianMonoidalCategory.prodComparison (diagonal D) C P) = 𝟙 (C ⊗ P, C ⊗ P) :=
  IsIso.inv_eq_of_inv_hom_id
    (f := CartesianMonoidalCategory.prodComparison (diagonal D) C P)
    (by rw [diagonal_productComparison]; exact Category.id_comp _)

/-- The terminal comparison sends the chosen pair of units to itself. -/
@[simp] theorem diagonal_terminalComparison :
    CartesianMonoidalCategory.terminalComparison (diagonal D) = 𝟙 (𝟙_ D, 𝟙_ D) := by
  apply Prod.hom_ext <;> exact toUnit_unique _ _

/-- The inverse terminal comparison is the actual identity. -/
@[simp] theorem diagonal_terminalComparison_inv :
    inv (CartesianMonoidalCategory.terminalComparison (diagonal D)) = 𝟙 (𝟙_ D, 𝟙_ D) :=
  IsIso.inv_eq_of_inv_hom_id
    (f := CartesianMonoidalCategory.terminalComparison (diagonal D))
    (by rw [diagonal_terminalComparison]; exact Category.id_comp _)

/-- A selected exponential transported along the diagonal, evaluated and
curried componentwise at any pair of stages. -/
def diagonalExponential {C T P : D} (E : Exponential C T P) :
    Exponential ((diagonal D).obj C) ((diagonal D).obj T) ((diagonal D).obj P) where
  eval := (E.eval, E.eval)
  curry f := (E.curry f.1, E.curry f.2)
  curry_eval f := Prod.hom_ext (E.curry_eval f.1) (E.curry_eval f.2)
  curry_unique f g h := Prod.hom_ext
    (E.curry_unique f.1 g.1 (congrArg (fun f => f.1) h))
    (E.curry_unique f.2 g.2 (congrArg (fun f => f.2) h))

/-- The diagonal qualifies uniformly for every selected exponential. -/
instance diagonalExponentialPreservation : ExponentialPreservation (diagonal D) where
  image E := diagonalExponential E
  eval_image {C T P} E := by
    have inverse : inv (CartesianMonoidalCategory.prodComparison (diagonal D) C P) = 𝟙 _ :=
      (IsIso.inv_eq_of_inv_hom_id (f := CartesianMonoidalCategory.prodComparison (diagonal D) C P)
        (by rw [diagonal_productComparison]; exact Category.id_comp _))
    rw [inverse]
    exact Prod.hom_ext (Category.id_comp _).symm (Category.id_comp _).symm

/-- The image evaluation is two copies of the original evaluation. -/
@[simp] theorem diagonal_image_eval {C T P : D} (E : Exponential C T P) :
    (imageExponential (diagonal D) E).eval = (E.eval, E.eval) := rfl

section Boolean

/-- The selected Boolean function object, with its actual evaluation. -/
def booleanExponential : Exponential (Bool : Type) Bool (Bool ⟶ Bool) :=
  Exponential.closed Bool Bool

/-- The transported Boolean function object has two function components. -/
def booleanImage : Exponential ((Bool : Type), (Bool : Type)) (Bool, Bool)
    ((Bool ⟶ Bool), (Bool ⟶ Bool)) :=
  imageExponential (diagonal (Type)) booleanExponential

/-- Evaluation in the two components applies the corresponding function. -/
theorem booleanImage_eval (b₁ b₂ : Bool) (f₁ f₂ : Bool ⟶ Bool) :
    booleanImage.eval.1 (b₁, f₁) = f₁ b₁ ∧
      booleanImage.eval.2 (b₂, f₂) = f₂ b₂ := by
  constructor <;> rfl

/-- This evaluation is the mapped evaluation after the actual product comparison. -/
theorem booleanImage_product_eval :
    booleanImage.eval =
      inv (CartesianMonoidalCategory.prodComparison (diagonal (Type)) Bool (Bool ⟶ Bool)) ≫
        (diagonal (Type)).map booleanExponential.eval :=
  imageExponential_eval (diagonal (Type)) booleanExponential

/-- A generalized stage with unequal components need not be a diagonal image. -/
def mixedStageArrow : ((Bool : Type), (Bool : Type)) ⊗ ((PUnit : Type), (Bool : Type)) ⟶
    ((Bool : Type), (Bool : Type)) :=
  (↾fun bz => bz.1, ↾fun bz => bz.1 && bz.2)

/-- Currying is checked at a genuinely mixed stage, rather than only at images. -/
theorem booleanImage_mixed_curry (b z : Bool) :
    (booleanImage.curry mixedStageArrow).1 PUnit.unit b = b ∧
      (booleanImage.curry mixedStageArrow).2 z b = (b && z) := by
  constructor <;> rfl

/-- The two mixed-stage components can yield different functions. -/
theorem booleanImage_mixed_components_differ :
    (booleanImage.curry mixedStageArrow).1 PUnit.unit true ≠
      (booleanImage.curry mixedStageArrow).2 false true := by
  decide

/-- A target arrow may act differently on its two components. -/
def mixedBooleanEndomorphism : ((Bool : Type), (Bool : Type)) ⟶ (Bool, Bool) :=
  (↾Bool.not, 𝟙 Bool)

/-- The actual target change is not full: this mixed arrow is not an image. -/
theorem mixedBooleanEndomorphism_not_diagonal (f : (Bool : Type) ⟶ Bool) :
    (diagonal (Type)).map f ≠ mixedBooleanEndomorphism := by
  intro same
  have first := congrArg (fun g => g.1 true) same
  have second := congrArg (fun g => g.2 true) same
  have impossible : false = true := first.symm.trans second
  cases impossible

/-- A Boolean binding signature with a unary operator taking one binder body. -/
def booleanBinding : Signature where
  Srt := Unit
  Op _ := Unit
  arity _ := [([()], ())]

/-- This binder operator tests the body at both Boolean arguments. -/
def booleanOperator : (((Bool × PUnit.{1}) ⟶ (Bool : Type)) × PUnit.{1}) ⟶ (Bool : Type) :=
  ↾fun args => args.1.hom (false, PUnit.unit) && args.1.hom (true, PUnit.unit)

/-- An actual binding model, with a nonconstant Boolean quantifier operator. -/
def booleanModel : Model booleanBinding (Type) :=
  ofClosed (fun _ => (Bool : Type)) (fun _ => booleanOperator)

/-- The diagonal target change maps the Boolean sort to two copies. -/
theorem booleanModel_sort :
    (mapModel (diagonal (Type)) booleanModel).sort () = ((Bool : Type), (Bool : Type)) := rfl

/-- Its binder body object is the pair of actual source function objects. -/
theorem booleanModel_power :
    (mapModel (diagonal (Type)) booleanModel).power [()] () =
      (((Bool × PUnit.{1}) ⟶ (Bool : Type)), ((Bool × PUnit.{1}) ⟶ (Bool : Type))) := rfl

/-- The singleton binder context comparison is two identity maps. -/
theorem booleanModel_contextComparison :
    (contextComparison (diagonal (Type)) booleanModel.sort [()]).hom =
      ((𝟙 (Bool × PUnit.{1}) : TypeCat.Hom (Bool × PUnit.{1}) (Bool × PUnit.{1})),
        (𝟙 (Bool × PUnit.{1}) : TypeCat.Hom (Bool × PUnit.{1}) (Bool × PUnit.{1}))) := by
  simp only [contextComparison, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom,
    productComparisonIso_inv, diagonal_productComparison_inv, asIso_inv,
    diagonal_terminalComparison_inv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The binder evaluation compares with both actual source evaluations. -/
theorem booleanModel_eval (b₁ b₂ : Bool × PUnit.{1})
    (f₁ f₂ : (Bool × PUnit.{1}) ⟶ (Bool : Type)) :
    ((mapModel (diagonal (Type)) booleanModel).eval [()] ()).1 (b₁, f₁) = f₁ b₁ ∧
      ((mapModel (diagonal (Type)) booleanModel).eval [()] ()).2 (b₂, f₂) = f₂ b₂ := by
  rw [mapModel_eval, booleanModel_contextComparison, diagonal_productComparison_inv]
  constructor <;> rfl

/-- The singleton operator-argument comparison is two identity maps. -/
theorem booleanModel_familyComparison :
    (familyComparison (diagonal (Type)) booleanModel.power [([()], ())]).hom =
      (𝟙 ((((Bool × PUnit.{1}) ⟶ (Bool : Type)) × PUnit.{1})),
        𝟙 ((((Bool × PUnit.{1}) ⟶ (Bool : Type)) × PUnit.{1}))) := by
  simp only [familyComparison, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom,
    productComparisonIso_inv, diagonal_productComparison_inv, asIso_inv,
    diagonal_terminalComparison_inv]
  rfl

/-- The mapped operator acts as the original binder operator in each component. -/
theorem booleanModel_op (f₁ f₂ : (Bool × PUnit.{1}) ⟶ (Bool : Type)) :
    ((mapModel (diagonal (Type)) booleanModel).op (s := ()) ()).1 (f₁, PUnit.unit) =
      booleanOperator (f₁, PUnit.unit) ∧
    ((mapModel (diagonal (Type)) booleanModel).op (s := ()) ()).2 (f₂, PUnit.unit) =
      booleanOperator (f₂, PUnit.unit) := by
  change ((familyComparison (diagonal (Type)) booleanModel.power [([()], ())]).hom ≫
      (diagonal (Type)).map booleanOperator).1 _ = _ ∧
    ((familyComparison (diagonal (Type)) booleanModel.power [([()], ())]).hom ≫
      (diagonal (Type)).map booleanOperator).2 _ = _
  rw [booleanModel_familyComparison]
  constructor <;> rfl

/-- The operator is genuinely sensitive to the binder body. -/
theorem booleanOperator_controls :
    booleanOperator (↾fun _ => true, PUnit.unit) = true ∧
      booleanOperator (↾fun bz => bz.1, PUnit.unit) = false := by
  constructor <;> rfl

end Boolean

end Mettapedia.OSLF.Binding.CategoricalBindingDiagonalTargetControl
