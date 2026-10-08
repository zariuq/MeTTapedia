import Mettapedia.CategoryTheory.RelativeClosedBaseInterpretation
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!+# Complete values and a rejected base comparison declaration

The native consistency interpretation recovers both coordinates of a supplied
product and both values of a supplied nonconstant function. It also recovers a
nonidentity old base map. A separate assignment gives the product inverse the
actual coordinate exchange: its headers are formed, but its declared inverse
equation is false. Thus arbitrary meanings for the inverse names do not earn
the base preservation diagrams.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.Controls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Interpretation GeneratedCategory

def diagram := NativeDiagram.interpretation (C := Type)

theorem product_comparison_value :
    diagram.map (comparison (.product Bool Bool)).hom = 𝟙 (Bool ⊗ Bool) :=
  rawArrowValue_unique (NativeDiagram.assignment (C := Type))
    (NativeDiagram.realization (C := Type)) (forwardRaw (.product Bool Bool)) _
    (NativeDiagram.forward_read (.product Bool Bool))

theorem both_product_coordinates_retained :
    diagram.map (comparison (.product Bool Bool)).hom (false, true) = (false, true) := by
  rw [product_comparison_value]
  rfl

theorem coordinate_erasure_rejected :
    diagram.map (comparison (.product Bool Bool)).hom (false, true) ≠ (false, false) := by
  rw [both_product_coordinates_retained]
  intro same
  exact Bool.false_ne_true (congrArg Prod.snd same).symm

def negation : Bool ⟶ Bool := TypeCat.ofHom Bool.not

theorem exponential_comparison_value :
    diagram.map (comparison (.exponential Bool Bool)).hom = 𝟙 (Bool ⟶[Type] Bool) :=
  rawArrowValue_unique (NativeDiagram.assignment (C := Type))
    (NativeDiagram.realization (C := Type)) (forwardRaw (.exponential Bool Bool)) _
    (NativeDiagram.forward_read (.exponential Bool Bool))

def retainedFunction : Bool ⟶ Bool :=
  diagram.map (comparison (.exponential Bool Bool)).hom negation

theorem whole_nonconstant_function_retained :
    retainedFunction false = true ∧ retainedFunction true = false := by
  unfold retainedFunction
  rw [exponential_comparison_value]
  exact ⟨rfl, rfl⟩

theorem constant_function_rejected : retainedFunction false ≠ retainedFunction true := by
  rw [whole_nonconstant_function_retained.1, whole_nonconstant_function_retained.2]
  exact fun same => Bool.false_ne_true same.symm

theorem nonidentity_old_arrow_retained :
    diagram.map (baseArrow (signature := signature (C := Type)) negation) = negation :=
  functor_base_arrow (NativeDiagram.assignment (C := Type))
    (NativeDiagram.realization (C := Type)) negation

theorem supplied_old_arrow_changes_value :
    diagram.map (baseArrow (signature := signature (C := Type)) negation) false = true := by
  rw [nonidentity_old_arrow_retained]
  rfl

def exchange : Bool ⊗ Bool ⟶ Bool ⊗ Bool :=
  TypeCat.ofHom (fun pair => (pair.2, pair.1))

def wrongInverseAssignment : Assignment (Type) (symbols (Type)) (Type) := by
  classical
  exact
    { base := Functor.id (Type)
      object origin := origin.down.elim
      arrow choice := if choice = .product Bool Bool then
          ⟨Bool ⊗ Bool, Bool ⊗ Bool, exchange⟩
        else ⟨selected choice, selected choice, 𝟙 (selected choice)⟩ }

theorem wrong_source_read (choice : Choice (Type)) :
    wrongInverseAssignment.evaluateObject (sourceCode choice) = some (selected choice) := by
  cases choice with
  | terminal => rfl
  | product first second => exact wrongInverseAssignment.evaluate_product rfl rfl
  | equalizer before after =>
      exact wrongInverseAssignment.evaluate_equalizer before after rfl rfl rfl rfl
  | exponential argument result => exact wrongInverseAssignment.evaluate_exponential rfl rfl

theorem wrong_target_read (choice : Choice (Type)) :
    wrongInverseAssignment.evaluateObject (targetCode choice) = some (selected choice) := rfl

theorem wrong_product_meaning :
    wrongInverseAssignment.arrow (.product Bool Bool) =
      ⟨Bool ⊗ Bool, Bool ⊗ Bool, exchange⟩ := by
  classical
  change (if Choice.product Bool Bool = .product Bool Bool then _ else _) = _
  exact if_pos rfl

theorem unchanged_meaning (choice : Choice (Type)) (different : choice ≠ .product Bool Bool) :
    wrongInverseAssignment.arrow choice =
      ⟨selected choice, selected choice, 𝟙 (selected choice)⟩ := by
  classical
  change (if choice = .product Bool Bool then _ else _) = _
  exact if_neg different

theorem wrong_inverse_headers_are_formed (choice : Choice (Type)) :
    wrongInverseAssignment.evaluateObject ((signature (C := Type)).source choice) =
      some (wrongInverseAssignment.arrow choice).source ∧
    wrongInverseAssignment.evaluateObject ((signature (C := Type)).target choice) =
      some (wrongInverseAssignment.arrow choice).target := by
  classical
  change wrongInverseAssignment.evaluateObject (sourceCode choice) =
      some (wrongInverseAssignment.arrow choice).source ∧
    wrongInverseAssignment.evaluateObject (targetCode choice) =
      some (wrongInverseAssignment.arrow choice).target
  by_cases same : choice = .product Bool Bool
  · subst choice
    rw [wrong_product_meaning]
    exact ⟨wrong_source_read (.product Bool Bool), wrong_target_read (.product Bool Bool)⟩
  · rw [unchanged_meaning choice same]
    exact ⟨wrong_source_read choice, wrong_target_read choice⟩

theorem wrong_product_forward_read :
    wrongInverseAssignment.evaluateArrow (forwardCode (.product Bool Bool)) =
      some ⟨Bool ⊗ Bool, Bool ⊗ Bool, 𝟙 (Bool ⊗ Bool)⟩ := by
  simpa only [forwardCode, CartesianMonoidalCategory.lift_fst_snd] using
    wrongInverseAssignment.evaluate_pair (CartesianMonoidalCategory.fst Bool Bool)
      (CartesianMonoidalCategory.snd Bool Bool) rfl rfl

theorem wrong_product_inverse_read :
    wrongInverseAssignment.evaluateArrow (.name (.product Bool Bool)) =
      some ⟨Bool ⊗ Bool, Bool ⊗ Bool, exchange⟩ := by
  exact (wrongInverseAssignment.evaluate_arrow_name (.product Bool Bool)).trans
    (congrArg some wrong_product_meaning)

theorem wrong_old_inverse_diagram_read :
    wrongInverseAssignment.evaluateArrow (leftCode (.product Bool Bool, false)) =
      some ⟨Bool ⊗ Bool, Bool ⊗ Bool, exchange⟩ := by
  simpa only [leftCode, Bool.false_eq_true, ↓reduceIte, Category.id_comp] using
    wrongInverseAssignment.evaluate_compose _ _
      wrong_product_forward_read wrong_product_inverse_read

theorem wrong_old_identity_read :
    wrongInverseAssignment.evaluateArrow (rightCode (.product Bool Bool, false)) =
      some ⟨Bool ⊗ Bool, Bool ⊗ Bool, 𝟙 (Bool ⊗ Bool)⟩ :=
  wrongInverseAssignment.evaluate_identity rfl

theorem exchanged_inverse_cannot_realize_diagrams :
    ¬ Realization (signature (C := Type)) wrongInverseAssignment := by
  intro realized
  obtain ⟨value, _, _, left, right⟩ := realized.equation (.product Bool Bool, false)
  have complete := (wrong_old_inverse_diagram_read.symm.trans left).trans
    (right.symm.trans wrong_old_identity_read)
  have same : exchange = 𝟙 (Bool ⊗ Bool) :=
    ArrowValue.arrow_injective (Option.some.inj complete)
  have impossible : true = false :=
    congrArg (fun arrow : Bool ⊗ Bool ⟶ Bool ⊗ Bool => (arrow (false, true)).1) same
  exact Bool.false_ne_true impossible.symm

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.Controls
