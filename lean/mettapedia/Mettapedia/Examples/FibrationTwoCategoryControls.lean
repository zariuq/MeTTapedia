import Mettapedia.CategoryTheory.FibrationCodomainCoherence
import Mettapedia.GSLT.Core.LambdaTheoryStructuredControls

/-!+# Cartesian preservation and compatible-cell controls

An actual nonidentity closed finite-limit functor maps the codomain and
predicate fibrations, and its noninvertible transformation supplies both
total and base components. A different square retains the same base
functor but extends only the codomain of each display. It strictly commutes
and sends a real Cartesian arrow to a non-Cartesian one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Examples.FibrationTwoCategoryControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Bicategory
open Mettapedia.CategoryTheory
open FibrationTwoCategory
open Mettapedia.GSLT.Core.LambdaTheoryStructuredControls

abbrev suppliedFibration : Fibration.{0,0} := codomain Bool
abbrev suppliedPredicates : Fibration.{0,0} := predicates Bool

def selected : Arrow Bool := Arrow.mk (homOfLE (show false ≤ true from le_top))

def accepted : suppliedFibration ⟶ suppliedFibration := codomainMap topFunctor

def acceptedPredicate : suppliedPredicates ⟶ suppliedPredicates := predicateMap topFunctor

def selectedPredicate : MonoArrowImageAdjunction.Predicate Bool :=
  ⟨selected, by change Mono selected.hom; infer_instance⟩

theorem mapped_predicate_retains_display :
    ((acceptedPredicate.square.left.toFunctor.obj selectedPredicate).obj.left) = true ∧
      ((acceptedPredicate.square.left.toFunctor.obj selectedPredicate).obj.right) = true :=
  ⟨rfl, rfl⟩

theorem comprehension_retains_source_display :
    (comprehensionMap Bool).square.left.toFunctor.obj selectedPredicate = selected := rfl

def predicateChange : predicateMap (𝟭 Bool) ⟶ predicateMap topFunctor := predicateCell grow

theorem predicate_cell_retains_actual_components :
    ((predicateChange.hom.left.toNatTrans.app selectedPredicate).hom.left : false ⟶ true) =
      homOfLE (show false ≤ true from le_top) ∧
    predicateChange.hom.right.toNatTrans.app false =
      homOfLE (show false ≤ true from le_top) := ⟨rfl, rfl⟩

theorem complete_comprehension_cell_square :
    (predicateChange ▷ comprehensionMap Bool) ≫ eqToHom (comprehension_naturality topFunctor) =
      eqToHom (comprehension_naturality (𝟭 Bool)) ≫
        (comprehensionMap Bool ◁ codomainCell (F := 𝟭 Bool) (G := topFunctor) grow) :=
  comprehensionCell_naturality (F := 𝟭 Bool) (G := topFunctor) grow

theorem mapped_display_readout :
    (accepted.square.left.toFunctor.obj selected).left = true ∧
      (accepted.square.left.toFunctor.obj selected).right = true := ⟨rfl, rfl⟩

theorem map_is_nonidentity : accepted ≠ 𝟙 suppliedFibration := by
  intro same
  have readout := congrArg (fun route : suppliedFibration ⟶ suppliedFibration =>
    (route.square.left.toFunctor.obj selected).left) same
  change true = false at readout
  cases readout

def acceptedCell : codomainMap (𝟭 Bool) ⟶ codomainMap topFunctor := codomainCell grow

theorem accepted_cell_retains_both :
    ((acceptedCell.hom.left.toNatTrans.app selected).left : false ⟶ true) =
      homOfLE (show false ≤ true from le_top) ∧
    acceptedCell.hom.right.toNatTrans.app false =
      homOfLE (show false ≤ true from le_top) := ⟨rfl, rfl⟩

theorem accepted_cell_noninvertible : ¬ IsIso acceptedCell := by
  intro invertible
  let backward : codomainMap topFunctor ⟶ codomainMap (𝟭 Bool) :=
    @inv (suppliedFibration ⟶ suppliedFibration)
      (Fibration.homCategory suppliedFibration suppliedFibration)
      (codomainMap (𝟭 Bool)) (codomainMap topFunctor) acceptedCell invertible
  let impossible : (true : Bool) ⟶ false := backward.hom.right.toNatTrans.app false
  exact (not_le_of_gt Bool.false_lt_true) impossible.le

def sourceDisplay : Arrow Bool := Arrow.mk (𝟙 false)
def targetDisplay : Arrow Bool := Arrow.mk (𝟙 true)

def selectedLift : sourceDisplay ⟶ targetDisplay :=
  Arrow.homMk (homOfLE (show false ≤ true from le_top))
    (homOfLE (show false ≤ true from le_top)) (by apply Subsingleton.elim)

instance selectedLift_cartesian :
    Arrow.rightFunc.IsCartesian selectedLift.right selectedLift :=
  (CodomainComprehension.cartesian_iff_pullback selectedLift).mpr
    IsPullback.of_id_snd

theorem accepted_preserves_complete_lift :
    suppliedFibration.functor.IsCartesian
      (accepted.square.right.toFunctor.map selectedLift.right)
      (accepted.square.left.toFunctor.map selectedLift) := by
  let : suppliedFibration.functor.IsCartesian selectedLift.right selectedLift :=
    selectedLift_cartesian
  exact Fibration.map_lifted_cartesian accepted selectedLift.right selectedLift

/-- Extend only the codomain. Its domain map still retains the supplied
display evidence, which prevents this square from preserving Cartesian lifts. -/
def codomainExtension : Arrow Bool ⥤ Arrow Bool where
  obj object := Arrow.mk (homOfLE (show object.left ≤ true from le_top))
  map square := Arrow.homMk square.left (𝟙 true) (by apply Subsingleton.elim)
  map_id object := by apply Arrow.hom_ext <;> rfl
  map_comp first second := by apply Arrow.hom_ext <;> rfl

def commutingSquare : suppliedFibration.projection ⟶ suppliedFibration.projection where
  left := codomainExtension.toCatHom
  right := topFunctor.toCatHom
  comm := by apply Cat.ext; rfl

theorem actual_square_commutes :
    suppliedFibration.projection.arrow ≫ commutingSquare.right =
      commutingSquare.left ≫ suppliedFibration.projection.arrow := commutingSquare.comm

theorem changed_lift_not_cartesian :
    ¬ Arrow.rightFunc.IsCartesian (𝟙 true) (codomainExtension.map selectedLift) := by
  intro cartesian
  let := cartesian
  have invertible : IsIso (codomainExtension.map selectedLift) :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso Arrow.rightFunc (𝟙 true) _
  let : IsIso (codomainExtension.map selectedLift) := invertible
  let backward := inv (codomainExtension.map selectedLift)
  let impossible : (true : Bool) ⟶ false := backward.left
  exact (not_le_of_gt Bool.false_lt_true) impossible.le

/-- A complete strictly commuting square need not be an admitted fibration map. -/
theorem commuting_does_not_preserve_cartesian :
    ¬ Fibration.PreservesCartesian commutingSquare := by
  intro preservation
  exact changed_lift_not_cartesian (preservation selectedLift selectedLift_cartesian)

theorem no_admitted_square_with_these_maps :
    ¬ ∃ route : suppliedFibration ⟶ suppliedFibration, route.square = commutingSquare := by
  rintro ⟨route, same⟩
  exact commuting_does_not_preserve_cartesian (same ▸ route.cartesian)

end Mettapedia.Examples.FibrationTwoCategoryControls
