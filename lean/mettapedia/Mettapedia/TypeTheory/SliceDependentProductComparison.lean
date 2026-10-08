import Mettapedia.CategoryTheory.SliceFunctorPullbackComparison
import Mettapedia.TypeTheory.CodomainClosedComprehension
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Dependent-product comparison of a finite-limit functor

The comparison is the actual mate of the complete pullback isomorphism.
It retains the whole dependent evaluation, abstraction and argument body.
Evaluation uniquely determines it. Invertibility is a separate property
and is not assumed for a finite-limit functor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.SliceDependentProductComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] [HasFiniteLimits C]
variable {D : Type u₂} [Category.{v₂} D] [HasFiniteLimits D]
variable (source : CodomainClosedComprehension C)
variable (target : CodomainClosedComprehension D)
variable (F : C ⥤ D) [PreservesFiniteLimits F]
variable {X Y : C} (route : X ⟶ Y)

def pullbackSquare : TwoSquare (Over.post (X := Y) F) (Over.pullback route)
    (Over.pullback (F.map route)) (Over.post (X := X) F) :=
  TwoSquare.mk _ _ _ _ (SliceFunctorPullbackComparison.comparison F route).inv

def comparison : source.dependentProduct route ⋙ Over.post F ⟶
    Over.post F ⋙ target.dependentProduct (F.map route) :=
  (mateEquiv (source.dependentAdjunction route)
    (target.dependentAdjunction (F.map route)) (pullbackSquare F route)).natTrans

theorem evaluation (result : Over X) :
    (Over.pullback (F.map route)).map
        ((comparison source target F route).app result) ≫
      target.evaluation (F.map route) ((Over.post F).obj result) =
    (SliceFunctorPullbackComparison.comparison F route).inv.app
        ((source.dependentProduct route).obj result) ≫
      (Over.post F).map (source.evaluation route result) :=
  mateEquiv_counit (source.dependentAdjunction route)
    (target.dependentAdjunction (F.map route)) (pullbackSquare F route) result

theorem abstraction {argument : Over Y} {result : Over X}
    (body : (Over.pullback route).obj argument ⟶ result) :
    (Over.post F).map (source.abstraction route body) ≫
        (comparison source target F route).app result =
      target.abstraction (F.map route)
        ((SliceFunctorPullbackComparison.comparison F route).inv.app argument ≫
          (Over.post F).map body) := by
  apply ((target.dependentAdjunction (F.map route)).homEquiv
    ((Over.post F).obj argument) ((Over.post F).obj result)).symm.injective
  change _ = ((target.dependentAdjunction (F.map route)).homEquiv
    ((Over.post F).obj argument) ((Over.post F).obj result)).symm
      (((target.dependentAdjunction (F.map route)).homEquiv
        ((Over.post F).obj argument) ((Over.post F).obj result))
          ((SliceFunctorPullbackComparison.comparison F route).inv.app argument ≫
            (Over.post F).map body))
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  change (Over.pullback (F.map route)).map
      ((Over.post F).map (source.abstraction route body) ≫
        (comparison source target F route).app result) ≫
      target.evaluation (F.map route) ((Over.post F).obj result) = _
  rw [Functor.map_comp, Category.assoc, evaluation]
  have natural := (SliceFunctorPullbackComparison.comparison F route).inv.naturality
    (source.abstraction route body)
  change (Over.pullback (F.map route)).map
      ((Over.post F).map (source.abstraction route body)) ≫
        (SliceFunctorPullbackComparison.comparison F route).inv.app
          ((source.dependentProduct route).obj result) =
      (SliceFunctorPullbackComparison.comparison F route).inv.app argument ≫
        (Over.post F).map ((Over.pullback route).map
          (source.abstraction route body)) at natural
  rw [← Category.assoc, natural]
  rw [Category.assoc, ← Functor.map_comp, source.beta]

theorem unit (argument : Over Y) :
    (Over.post F).map ((source.dependentAdjunction route).unit.app argument) ≫
        (comparison source target F route).app ((Over.pullback route).obj argument) =
      (target.dependentAdjunction (F.map route)).unit.app ((Over.post F).obj argument) ≫
        (target.dependentProduct (F.map route)).map
          ((SliceFunctorPullbackComparison.comparison F route).inv.app argument) :=
  unit_mateEquiv (source.dependentAdjunction route)
    (target.dependentAdjunction (F.map route)) (pullbackSquare F route) argument

/-- Any natural comparison with this complete evaluation is the constructed
mate. The test ranges over every actual slice object, including varying fibres. -/
theorem unique
    (candidate : source.dependentProduct route ⋙ Over.post F ⟶
      Over.post F ⋙ target.dependentProduct (F.map route))
    (readout : ∀ result,
      (Over.pullback (F.map route)).map (candidate.app result) ≫
          target.evaluation (F.map route) ((Over.post F).obj result) =
        (SliceFunctorPullbackComparison.comparison F route).inv.app
            ((source.dependentProduct route).obj result) ≫
          (Over.post F).map (source.evaluation route result)) :
    candidate = comparison source target F route := by
  apply NatTrans.ext
  funext result
  apply ((target.dependentAdjunction (F.map route)).homEquiv
    ((Over.post F).obj ((source.dependentProduct route).obj result))
    ((Over.post F).obj result)).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact (readout result).trans (evaluation source target F route result).symm

end Mettapedia.TypeTheory.SliceDependentProductComparison
