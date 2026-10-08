import Mettapedia.GSLT.Core.LambdaTheoryBicategory
import Mettapedia.CategoryTheory.CartesianClosedPowerFunctor
import Mathlib.Logic.Equiv.Bool

/-!
# Closed theory map controls

Exchange of the two indices is a genuine nonidentity equivalence of a diagram
category. It preserves finite limits and canonical exponentials, and moves
independently supplied component values. In contrast, the Boolean power
functor preserves finite limits but its canonical exponential comparison
misses an independently supplied coordinate-exchanging function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.Core.LambdaTheoryClosedControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory

noncomputable section

abbrev Diagrams := Discrete Bool ⥤ Type

abbrev diagramsTheory : LambdaTheory.{1, 0} := LambdaTheory.ofCategory Diagrams

def swapEquivalence : Diagrams ≌ Diagrams :=
  (Discrete.equivalence Equiv.boolNot).congrLeft

abbrev swapMap : LambdaTheoryMap diagramsTheory diagramsTheory :=
  LambdaTheoryMap.ofEquivalence swapEquivalence

abbrev reverseSwapMap : LambdaTheoryMap diagramsTheory diagramsTheory :=
  LambdaTheoryMap.ofEquivalence swapEquivalence.symm

def asymmetric : Diagrams := Discrete.functor fun index =>
  match index with
  | false => Empty
  | true => Bool

def supplied_swapped_value : (swapMap.functor.obj asymmetric).obj ⟨false⟩ := true

theorem swap_is_nonidentity : swapMap.functor ≠ Functor.id Diagrams := by
  intro same
  have objects := congrArg (fun route : Diagrams ⥤ Diagrams =>
    (route.obj asymmetric).obj ⟨false⟩) same
  have impossible : Bool = Empty := objects
  exact Empty.elim (impossible ▸ true)

abbrev numbers : Diagrams := Discrete.functor fun _ => Nat

def shift : numbers ⟶ numbers :=
  Discrete.natTrans fun index => ↾fun (value : Nat) => value + if index.as then 2 else 1

theorem original_component_readout : shift.app ⟨false⟩ (10 : Nat) = (11 : Nat) := rfl

theorem swapped_component_readout : (swapMap.functor.map shift).app ⟨false⟩ (10 : Nat) = (12 : Nat) := rfl

theorem component_values_differ :
    ((swapMap.functor.map shift).app ⟨false⟩ (10 : Nat) : Nat) ≠
      (shift.app ⟨false⟩ (10 : Nat) : Nat) := by
  intro same
  have impossible : (12 : Nat) = 11 :=
    swapped_component_readout.symm.trans (same.trans original_component_readout)
  cases impossible

def swapUnit : LambdaTheoryMap.id diagramsTheory ≅
    LambdaTheoryMap.comp reverseSwapMap swapMap :=
  LambdaTheory.isoOfNatIso (source := diagramsTheory) (target := diagramsTheory)
    (first := LambdaTheoryMap.id diagramsTheory)
    (second := LambdaTheoryMap.comp reverseSwapMap swapMap) swapEquivalence.unitIso

def swapCounit : LambdaTheoryMap.comp swapMap reverseSwapMap ≅
    LambdaTheoryMap.id diagramsTheory :=
  LambdaTheory.isoOfNatIso (source := diagramsTheory) (target := diagramsTheory)
    (first := LambdaTheoryMap.comp swapMap reverseSwapMap)
    (second := LambdaTheoryMap.id diagramsTheory) swapEquivalence.counitIso

theorem swap_exponential_invertible (A B : Diagrams) :
    IsIso ((expComparison swapMap.functor A).natTrans.app B) := inferInstance

theorem swap_exponential_evaluation (A B : Diagrams) :
    swapMap.functor.obj A ◁ (expComparison swapMap.functor A).natTrans.app B ≫
      (ihom.ev (swapMap.functor.obj A)).app (swapMap.functor.obj B) =
    inv (CartesianMonoidalCategory.prodComparison swapMap.functor A ((ihom A).obj B)) ≫
      swapMap.functor.map ((ihom.ev A).app B) :=
  expComparison_ev swapMap.functor A B

abbrev typesTheory : LambdaTheory.{1, 0} := LambdaTheory.ofCategory Type

theorem power_is_lex : PreservesFiniteLimits
    (Mettapedia.CategoryTheory.CartesianClosedPowerFunctor.power Bool) := inferInstance

/-- The actual lex functor is excluded by the closed-map contract. -/
theorem power_is_not_theory_map :
    ¬ ∃ route : LambdaTheoryMap typesTheory typesTheory,
      route.functor = Mettapedia.CategoryTheory.CartesianClosedPowerFunctor.power Bool := by
  rintro ⟨route, same⟩
  let : PreservesFiniteLimits route.functor := route.preservesFiniteLimits
  let : PreservesLimitsOfShape (Discrete WalkingPair) route.functor := inferInstance
  let := route.preservesExponentials
  exact Mettapedia.CategoryTheory.CartesianClosedPowerFunctor.power_bool_not_closed
    (Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_of_naturalIso
      (eqToIso same.symm))

end

end Mettapedia.GSLT.Core.LambdaTheoryClosedControls
