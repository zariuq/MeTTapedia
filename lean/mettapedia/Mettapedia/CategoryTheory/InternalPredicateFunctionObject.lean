import Mettapedia.CategoryTheory.InternalConjunctiveObject
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Internal predicate functions with their actual conjunctive structure

The exponential into an independently supplied conjunctive object carries
pointwise truth and conjunction. Their finite diagrams follow from the
original diagrams and the exponential adjunction. Complete evaluation
identifies the order on function sections with the predicate order on the
whole value/parameter context; substitution retains that complete context.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateFunctionObject

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalConjunctiveObject

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (original : Operations C)

abbrev power (value : C) : C := (ihom value).obj original.proposition

def read {value parameter : C} (predicate : parameter ⟶ power original value) :
    original.Fiber (value ⊗ parameter) := uncurry predicate

def quote {value parameter : C} (predicate : original.Fiber (value ⊗ parameter)) :
    parameter ⟶ power original value := curry predicate

theorem read_quote {value parameter : C} (predicate : original.Fiber (value ⊗ parameter)) :
    read original (quote original predicate) = predicate := uncurry_curry predicate

theorem quote_read {value parameter : C} (predicate : parameter ⟶ power original value) :
    quote original (read original predicate) = predicate := curry_uncurry predicate

theorem read_injective {value parameter : C} :
    Function.Injective (read original (value := value) (parameter := parameter)) :=
  uncurry_injective

theorem read_substitution {value first second : C} (incoming : first ⟶ second)
    (predicate : second ⟶ power original value) :
    read original (incoming ≫ predicate) =
      (value ◁ incoming) ≫ read original predicate :=
  uncurry_natural_left incoming predicate

def operations (value : C) : Operations C where
  proposition := power original value
  truth := quote original (original.top (value ⊗ 𝟙_ C))
  conjunction := quote original
    (original.meet (read original (fst _ _)) (read original (snd _ _)))

theorem read_meet {value parameter : C}
    (first second : (operations original value).Fiber parameter) :
    read original ((operations original value).meet first second) =
      original.meet (read original first) (read original second) := by
  change uncurry (lift first second ≫ curry _) = _
  rw [uncurry_natural_left, uncurry_curry]
  have transported : (value ◁ lift first second) ≫ original.meet
      (read original (fst (power original value) (power original value)))
      (read original (snd (power original value) (power original value))) =
      original.meet ((value ◁ lift first second) ≫ read original (fst _ _))
        ((value ◁ lift first second) ≫ read original (snd _ _)) :=
    original.reindex_meet (value ◁ lift first second) _ _
  have firstRead : (value ◁ lift first second) ≫ read original (fst _ _) = read original first :=
    (read_substitution original (lift first second) (fst _ _)).symm.trans
      (congrArg (read original) (lift_fst first second))
  have secondRead : (value ◁ lift first second) ≫ read original (snd _ _) = read original second :=
    (read_substitution original (lift first second) (snd _ _)).symm.trans
      (congrArg (read original) (lift_snd first second))
  exact transported.trans (congrArg₂ original.meet firstRead secondRead)

theorem read_top (value parameter : C) :
    read original ((operations original value).top parameter) = original.top (value ⊗ parameter) := by
  change uncurry (toUnit parameter ≫ curry _) = _
  rw [uncurry_natural_left, uncurry_curry]
  exact original.reindex_top (value ◁ toUnit parameter)

theorem conjunction_after {value parameter : C}
    (tuple : parameter ⟶ power original value ⊗ power original value) :
    tuple ≫ (operations original value).conjunction =
      (operations original value).meet (tuple ≫ fst _ _) (tuple ≫ snd _ _) := by
  change tuple ≫ (operations original value).conjunction =
    lift (tuple ≫ fst _ _) (tuple ≫ snd _ _) ≫ (operations original value).conjunction
  exact (congrArg (fun arrow => arrow ≫ (operations original value).conjunction)
    (lift_comp_fst_snd tuple)).symm

variable (originalLaws : original.Laws)

include originalLaws in
theorem function_laws (value : C) : (operations original value).Laws where
  commutativity := by
    apply read_injective original
    change read original ((operations original value).meet (snd _ _) (fst _ _)) =
      read original (operations original value).conjunction
    have direct : (operations original value).meet (fst _ _) (snd _ _) =
        (operations original value).conjunction := by
      simp only [Operations.meet, lift_fst_snd, Category.id_comp]
    rw [← direct, read_meet, read_meet]
    exact original.meet_comm originalLaws _ _
  associativity := by
    apply read_injective original
    change read original ((operations original value).meet
      (fst _ _ ≫ (operations original value).conjunction) (snd _ _)) =
      read original ((operations original value).meet (fst _ _ ≫ fst _ _)
        (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ (operations original value).conjunction))
    rw [conjunction_after, read_meet, read_meet, read_meet]
    have rightNested := read_meet original
      (fst (power original value ⊗ power original value) (power original value) ≫
        snd (power original value) (power original value))
      (snd (power original value ⊗ power original value) (power original value))
    refine (original.meet_assoc originalLaws _ _ _).trans ?_
    exact congrArg (original.meet _) rightNested.symm
  idempotence := by
    apply read_injective original
    change read original ((operations original value).meet (𝟙 _) (𝟙 _)) = read original (𝟙 _)
    rw [read_meet]
    exact original.meet_idem originalLaws _
  truthUnit := by
    apply read_injective original
    change read original ((operations original value).meet (𝟙 _)
      ((operations original value).top _)) = read original (𝟙 _)
    rw [read_meet, read_top]
    exact original.meet_top originalLaws _

include originalLaws in
theorem le_iff_read {value parameter : C}
    (first second : (operations original value).Fiber parameter) :
    letI := (operations original value).semilattice (function_laws original originalLaws value) parameter
    letI := original.semilattice originalLaws (value ⊗ parameter)
    first ≤ second ↔ read original first ≤ read original second := by
  change (operations original value).meet second first = first ↔
    original.meet (read original second) (read original first) = read original first
  rw [← read_meet]
  constructor
  · exact congrArg (read original)
  · intro same
    apply read_injective original
    exact same

end Mettapedia.CategoryTheory.InternalPredicateFunctionObject
