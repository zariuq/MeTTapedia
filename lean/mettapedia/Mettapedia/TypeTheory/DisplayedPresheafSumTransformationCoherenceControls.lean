import Mettapedia.TypeTheory.DisplayedPresheafSumTransformationCoherence
import Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherenceControls

/-!
# Supplied-pair controls for dependent theory transformations

Successor transports both witnesses of the native pair. Reset identifies
distinct supplied pair receipts, so the sum restriction comparison being
invertible does not make an arbitrary theory transformation invertible.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSumTransformationCoherenceControls

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSigma
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafTheoryCwfControls DisplayedPresheafTheoryCwfTransformationControls
open DisplayedPresheafProductTransformationCoherenceControls
open DisplayedPresheafSumTransformationCoherence

abbrev selectedSum (selection : Callers ⥤ Worlds) :
    DisplayedFamily (selection.op ⋙ base) :=
  sigmaDisplayed (restrictFamily selection base witnesses)
    ((codomainFunctor selection base witnesses).obj witnessResults)

def suppliedPair (first second : Nat) :
    (totalSpace (selectedSum selectOne)).obj (point selectOne).1 :=
  ⟨(point selectOne).2, ⟨first, second⟩⟩

def transportedPair (change : selectZero ⟶ selectOne) (first second : Nat) :
    (totalSpace (selectedSum selectZero)).obj (point selectOne).1 :=
  (sumTotalMap change base witnesses witnessResults).app (point selectOne).1
    (suppliedPair first second)

theorem successor_transports_both (first second : Nat) :
    (transportedPair increment first second).2.1 = Nat.succ first ∧
      (transportedPair increment first second).2.2 = Nat.succ second := ⟨rfl, rfl⟩

theorem reset_transports_both (first second : Nat) :
    (transportedPair reset first second).2.1 = (1 : Nat) ∧
      (transportedPair reset first second).2.2 = (1 : Nat) := ⟨rfl, rfl⟩

theorem cannot_keep_old_body (first second : Nat) :
    (transportedPair increment first second).2.2 ≠ second :=
  Nat.succ_ne_self second

theorem reset_identifies_supplied_pairs :
    transportedPair reset 0 0 = transportedPair reset 3 8 := rfl

theorem supplied_pairs_distinct : suppliedPair 0 0 ≠ suppliedPair 3 8 := by
  intro same
  have different := congrArg (fun receipt => receipt.2.1) same
  exact (by decide : (0 : Nat) ≠ 3) different

theorem reset_pair_map_not_injective :
    ¬ Function.Injective
      ((sumTotalMap reset base witnesses witnessResults).app (point selectOne).1) := by
  intro injective
  exact supplied_pairs_distinct (injective reset_identifies_supplied_pairs)

namespace Horizontal

open DisplayedPresheafProductTransformationCoherenceControls.Covered

def suppliedScalarPair (first second : Nat) :
    (totalSpace (sigmaDisplayed
      (restrictFamily ((𝟭 ScalarWorlds) ⋙ (𝟭 ScalarWorlds)) scalarBase scalarWitnesses)
      ((codomainFunctor ((𝟭 ScalarWorlds) ⋙ (𝟭 ScalarWorlds))
        scalarBase scalarWitnesses).obj scalarResults))).obj scalarPoint.1 :=
  ⟨PUnit.unit, ⟨first, second⟩⟩

def horizontalPair (firstFactor secondFactor first second : Nat) :=
  ((sumTransformation (scale firstFactor ◫ scale secondFactor)
    scalarBase scalarWitnesses).app scalarResults).app scalarPoint.1
      (suppliedScalarPair first second)

theorem horizontal_transports_both (first second : Nat) :
    (horizontalPair 2 3 first second).2.1 = 6 * first ∧
      (horizontalPair 2 3 first second).2.2 = 6 * second := ⟨rfl, rfl⟩

theorem horizontal_staged_square :
    sumTransformation (scale 2 ◫ scale 3) scalarBase scalarWitnesses ≫
        (sumCompositionIso (𝟭 ScalarWorlds) (𝟭 ScalarWorlds)
          scalarBase scalarWitnesses).hom =
      (sumCompositionIso (𝟭 ScalarWorlds) (𝟭 ScalarWorlds)
        scalarBase scalarWitnesses).hom ≫
        Functor.whiskerRight (sumTransformation (scale 3) scalarBase scalarWitnesses)
          (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheaves (𝟭 ScalarWorlds)) ≫
          Functor.whiskerLeft (sumTotals (𝟭 ScalarWorlds) scalarBase scalarWitnesses)
            (Mettapedia.GSLT.Topos.LogicalTransport.restrictPresheavesMap (scale 2)) :=
  sumTransformation_horizontal_square (scale 2) (scale 3) scalarBase scalarWitnesses

theorem cannot_omit_first_action :
    horizontalPair 2 3 1 2 ≠ horizontalPair 1 3 1 2 := by
  intro same
  have first := congrArg (fun receipt => receipt.2.1) same
  exact (by decide : (6 : Nat) ≠ 3) first

end Horizontal

end Mettapedia.TypeTheory.DisplayedPresheafSumTransformationCoherenceControls
