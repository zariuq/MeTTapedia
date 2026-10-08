import Mettapedia.TypeTheory.FibrationComprehensionProfile
import Mettapedia.TypeTheory.CodomainClosedComprehension
import Mettapedia.CategoryTheory.FibrationCodomainAction

/-!
# The actual closed-comprehension profile of codomain

Slice categories give the complete fibres. Substitution is the chosen
pullback and its total lift retains both projections. The sum is actual
composition; its strong comparison is computed from its adjunction unit
and the same total Cartesian lift. Dependent products use the independently
constructed right adjunction supplied by a closed codomain model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.CodomainFibrationComprehensionProfile

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open Mettapedia.CategoryTheory.FibrationTwoCategory
open FibrationComprehensionProfile

universe u v
variable {C : Type (max u v)} [Category.{v} C] [HasFiniteLimits C]

local instance codomainFibres : HasFibers.{v,max u v} (codomain C).functor :=
  CodomainComprehension.sliceFibres

local instance basePullbacks : HasPullbacks (codomain C).Base :=
  inferInstanceAs (HasPullbacks C)

def comprehension : Comprehension (codomain C) where
  display := CodomainComprehension.comprehension C
  over := rfl
  full := CodomainComprehension.comprehension_full C
  faithful := CodomainComprehension.comprehension_faithful C
  cartesian square supplied := by
    change Arrow.rightFunc.IsCartesian square.right square at supplied
    exact (CodomainComprehension.cartesian_iff_pullback square).mp supplied
  unit := CodomainComprehension.unit C
  unitFull := CodomainComprehension.unit_full C
  unitFaithful := CodomainComprehension.unit_faithful C
  unitOver := rfl
  unitAdjunction := CodomainComprehension.codomainAdjunction C
  domainAdjunction := CodomainComprehension.domainAdjunction C

def substitution : @Substitution (codomain C) CodomainComprehension.sliceFibres where
  reindex {source target} route := by
    change Over target ⥤ Over source
    exact Over.pullback route
  lift {source target} route := by
    change Over.pullback route ⋙ CodomainComprehension.fibreInclusion source ⟶
      CodomainComprehension.fibreInclusion target
    exact {
    app object := CodomainComprehension.pullbackLift
      ((CodomainComprehension.fibreInclusion _).obj object) route
    naturality first second arrow := by
      apply Arrow.hom_ext
      · change pullback.lift (pullback.fst first.hom route ≫ arrow.left)
          (pullback.snd first.hom route) _ ≫ pullback.fst second.hom route =
          pullback.fst first.hom route ≫ arrow.left
        exact pullback.lift_fst _ _ _
      · change 𝟙 source ≫ route = route ≫ 𝟙 target
        exact (Category.id_comp route).trans (Category.comp_id route).symm }
  cartesian route object := by
    change Arrow.rightFunc.IsStronglyCartesian route
      (CodomainComprehension.pullbackLift
        ((CodomainComprehension.fibreInclusion _).obj object) route)
    infer_instance

def closed (model : CodomainClosedComprehension C) :
    @Closed.{max u v,v,max u v,v} (codomain C) CodomainComprehension.sliceFibres where
  comprehension := comprehension
  substitution := substitution
  sum {source target} route := by
    change Over source ⥤ Over target
    exact Over.map route
  product {source target} route := by
    change Over source ⥤ Over target
    exact model.dependentProduct route
  sumAdjunction route := by
    change Over.map route ⊣ Over.pullback route
    exact Over.mapPullbackAdj route
  productAdjunction route := by
    change Over.pullback route ⊣ model.dependentProduct route
    exact model.dependentAdjunction route
  strongSum route object := by
    change IsIso (CodomainComprehension.canonicalSumSquare route object).left
    rw [CodomainComprehension.canonicalSumSquare_domain]
    exact (Iso.refl (show C from object.left)).isIso_hom

theorem sumArrow_eq_canonical (model : CodomainClosedComprehension C)
    {source target : C} (route : source ⟶ target) (object : Over source) :
    (closed model).sumArrow route object =
      CodomainComprehension.canonicalSumSquare route object := rfl

theorem strongSum_domain (model : CodomainClosedComprehension C)
    {source target : C} (route : source ⟶ target) (object : Over source) :
    ((closed model).strongSumComparison route object).hom = 𝟙 object.left :=
  CodomainComprehension.canonicalSumSquare_domain route object

theorem product_beta (model : CodomainClosedComprehension C)
    {source target : C} (route : source ⟶ target)
    {argument : Over target} {result : Over source}
    (body : (Over.pullback route).obj argument ⟶ result) :
    (Over.pullback route).map ((closed model).abstraction route body) ≫
      (closed model).evaluation route result = body :=
  (closed model).beta route body

end Mettapedia.TypeTheory.CodomainFibrationComprehensionProfile
