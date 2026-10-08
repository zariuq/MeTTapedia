import Mettapedia.TypeTheory.SliceDependentProductComparison

/-!
# Earned compatibility of the complete dependent-product comparison

The actual mate has complete evaluation, abstraction and unit equations.
This derived certificate can be instantiated at large constructed models
without reconstructing their chosen products during each pointwise proof.
Its fields are proved from the two adjunctions and the actual pullback
comparison; they are not additional conditions on either model.
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

/-- Complete compatibility, including every body in every actual slice.
The theorem `compatible` earns all fields for the constructed mate. -/
structure Compatible
    (candidate : source.dependentProduct route ⋙ Over.post F ⟶
      Over.post F ⋙ target.dependentProduct (F.map route)) : Prop where
  evaluation : ∀ result : Over X,
    (Over.pullback (F.map route)).map (candidate.app result) ≫
        target.evaluation (F.map route) ((Over.post F).obj result) =
      (SliceFunctorPullbackComparison.comparison F route).inv.app
          ((source.dependentProduct route).obj result) ≫
        (Over.post F).map (source.evaluation route result)
  abstraction : ∀ {argument : Over Y} {result : Over X}
    (body : (Over.pullback route).obj argument ⟶ result),
    (Over.post F).map (source.abstraction route
        (argument := argument) (result := result) body) ≫ candidate.app result =
      target.abstraction (F.map route)
        (argument := (Over.post F).obj argument) (result := (Over.post F).obj result)
        ((SliceFunctorPullbackComparison.comparison F route).inv.app argument ≫
          (Over.post F).map body)
  unit : ∀ argument : Over Y,
    (Over.post F).map ((source.dependentAdjunction route).unit.app argument) ≫
        candidate.app ((Over.pullback route).obj argument) =
      (target.dependentAdjunction (F.map route)).unit.app ((Over.post F).obj argument) ≫
        (target.dependentProduct (F.map route)).map
          ((SliceFunctorPullbackComparison.comparison F route).inv.app argument)

theorem compatible :
    Compatible source target F route (comparison source target F route) where
  evaluation := evaluation source target F route
  abstraction := abstraction source target F route
  unit := unit source target F route

/-- Even the evaluation part determines the whole comparison. -/
theorem compatible_unique
    (candidate : source.dependentProduct route ⋙ Over.post F ⟶
      Over.post F ⋙ target.dependentProduct (F.map route))
    (certificate : Compatible source target F route candidate) :
    candidate = comparison source target F route :=
  unique source target F route candidate certificate.evaluation

end Mettapedia.TypeTheory.SliceDependentProductComparison
