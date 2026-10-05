import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraQuotient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerControls

/-!
# Infinite growing indexed-coalgebra controls

The actual carrier has an arbitrary natural-number base parameter and,
at stage n, n+1 positions with Boolean provenance. All future children
retain the base parameter. Ordinary bisimulation identifies even different
parameters; the indexed quotient identifies exactly equal parameters.

New receipts appear at every stage and do not lie in the image of the
previous restriction. Receipts with different provenance remain distinct
in the source while their indexed readings agree. These facts instantiate
the general parameter-supported quotient construction, not indexed finality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraQuotientControls

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open PowerClassPresheafDescent.Controls
open Mettapedia.TypeTheory.ContextualWitnessCover

def parameters : Stagesᵒᵖ ⥤ Type where
  obj _ := Nat
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev source := CoveredFuturePowerClassifier.product parameters growingSource

def parameter : NaturalHom source parameters :=
  CoveredFuturePowerClassifier.firstProjection parameters growingSource

def children (point : Stagesᵒᵖ) (argument : source.obj point) : FuturePowerFamilies.Predicate source point where
  holds future := future.2.1 = argument.1
  closed {first second} move admitted := by
    have same : first.2.1 = second.2.1 := congrArg Prod.fst move.2
    exact same.symm.trans admitted

def transition : NaturalHom source (IndexedCoveredPower.family parameter) where
  app point argument := ⟨(argument.1, ofFull (children point argument)), fun _ available => available⟩
  naturality step argument := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Predicate.ext
      intro _
      exact Iff.rfl

theorem parameter_square : transition.comp (IndexedCoveredPower.projection parameter) = parameter := by
  apply NaturalHom.ext
  intro _ _
  rfl

abbrev underlying := IndexedCoalgebraBisimulation.original parameter transition
abbrev indexedFamily := IndexedCoalgebraQuotient.family parameter transition
abbrev indexedProjection := IndexedCoalgebraQuotient.projection parameter transition

theorem ordinary_all_equivalent (point : Stagesᵒᵖ) (first second : source.obj point) :
    ContextualCoalgebraBisimulation.Bisimilar underlying point first second := by
  apply ContextualCoalgebraBisimulation.greatest underlying (relation := fun _ _ _ => True)
  · exact {
      stable := fun {_ _} _ {_ _} _ => trivial
      forth := fun {_ _ right} _ future {child} _ =>
        ⟨(right.1, child.2), rfl, trivial⟩
      back := fun {_ left _} _ future {child} _ =>
        ⟨(left.1, child.2), rfl, trivial⟩ }
  · trivial

theorem indexed_reading_eq_iff (point : Stagesᵒᵖ) (first second : source.obj point) :
    indexedProjection.app point first = indexedProjection.app point second ↔ first.1 = second.1 := by
  constructor
  · intro same
    exact ((IndexedCoalgebraQuotient.projection_eq_iff parameter transition point first second).mp same).2
  · intro same
    exact (IndexedCoalgebraQuotient.projection_eq_iff parameter transition point first second).mpr
      ⟨ordinary_all_equivalent point first second, same⟩

def initialValue (base : Nat) (tag : Bool) : source.obj (world 0) :=
  (base, stageValue 0 0 (Nat.zero_lt_one) tag)

theorem infinitely_many_indexed_readings : Function.Injective
    (fun base => indexedProjection.app (world 0) (initialValue base false)) := by
  intro first second same
  exact (indexed_reading_eq_iff (world 0) (initialValue first false) (initialValue second false)).mp same

theorem ordinary_readout_forgets_base :
    (ContextualCoalgebraQuotient.projection underlying).app (world 0) (initialValue 0 false) =
      (ContextualCoalgebraQuotient.projection underlying).app (world 0) (initialValue 1 false) :=
  (ContextualCoalgebraQuotient.projection_eq_iff underlying (world 0) _ _).mpr
    (ordinary_all_equivalent (world 0) _ _)

theorem indexed_readout_retains_base :
    indexedProjection.app (world 0) (initialValue 0 false) ≠
      indexedProjection.app (world 0) (initialValue 1 false) :=
  fun same => Nat.zero_ne_one (infinitely_many_indexed_readings same)

theorem raw_provenance_distinct (base : Nat) : initialValue base true ≠ initialValue base false := by
  intro same
  exact Bool.noConfusion (congrArg (fun receipt : source.obj (world 0) => receipt.2.2) same)

theorem indexed_provenance_agrees (base : Nat) :
    indexedProjection.app (world 0) (initialValue base true) =
      indexedProjection.app (world 0) (initialValue base false) :=
  (indexed_reading_eq_iff (world 0) _ _).mpr rfl

def newReceipt (stage base : Nat) : source.obj (world (stage + 1)) :=
  (base, stageValue (stage + 1) (stage + 1) (Nat.lt_succ_self (stage + 1)) false)

def advance (stage : Nat) : world stage ⟶ world (stage + 1) := (homOfLE (Nat.le_succ stage)).op.op

theorem new_receipt_every_stage (stage base : Nat) :
    ¬ ∃ earlier : source.obj (world stage), source.map (advance stage) earlier = newReceipt stage base := by
  rintro ⟨earlier, same⟩
  have positions := congrArg (fun receipt : source.obj (world (stage + 1)) => receipt.2.1.val) same
  change earlier.2.1.val = stage + 1 at positions
  have bound := earlier.2.1.isLt
  change earlier.2.1.val < stage + 1 at bound
  rw [positions] at bound
  exact Nat.lt_irrefl _ bound

theorem new_receipt_admitted (stage base : Nat) :
    (underlying.app (world stage)
      (base, stageValue stage 0 (Nat.zero_lt_succ stage) false)).val.holds
        ⟨⟨world (stage + 1), advance stage⟩, newReceipt stage base⟩ := rfl

theorem whole_indexed_coalgebra_square :
    transition.comp (IndexedCoveredPower.image parameter
      (IndexedCoalgebraQuotient.quotientParameter parameter transition)
      indexedProjection (IndexedCoalgebraQuotient.parameter_square parameter transition)) =
    indexedProjection.comp (IndexedCoalgebraQuotient.indexedCoalgebra parameter transition parameter_square) :=
  IndexedCoalgebraQuotient.indexed_projection_square parameter transition parameter_square

end Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraQuotientControls
