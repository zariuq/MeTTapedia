import Mettapedia.CategoryTheory.CodomainComprehensionFibration
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!
# Strong dependent sums in codomain comprehension

The canonical sum square is the vertical adjunction unit followed by the
chosen Cartesian lift. Applying domain to this square gives the strong
sum comparison. Its full computation is proved from the pullback
projections; the square is also genuinely opcartesian.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.CodomainComprehension

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {source target : C} (route : source ⟶ target) (object : Over source)

def canonicalSumSquare :
    (fibreInclusion source).obj object ⟶
      (fibreInclusion target).obj ((Over.map route).obj object) :=
  (fibreInclusion source).map ((Over.mapPullbackAdj route).unit.app object) ≫
    pullbackLift ((fibreInclusion target).obj ((Over.map route).obj object)) route

@[simp] theorem canonicalSumSquare_domain :
    (canonicalSumSquare route object).left = 𝟙 object.left := by
  change pullback.lift (𝟙 object.left) object.hom _ ≫
    pullback.fst (object.hom ≫ route) route = 𝟙 object.left
  exact pullback.lift_fst _ _ _

@[simp] theorem canonicalSumSquare_base :
    (canonicalSumSquare route object).right = route := by
  change 𝟙 source ≫ route = route
  exact Category.id_comp _

theorem canonicalSumSquare_eq :
    canonicalSumSquare route object = Arrow.homMk (𝟙 object.left) route
      (by change 𝟙 object.left ≫ (object.hom ≫ route) = object.hom ≫ route
          exact Category.id_comp _) := by
  apply Arrow.hom_ext
  · exact canonicalSumSquare_domain route object
  · exact canonicalSumSquare_base route object

def strongSumComparison : object.left ≅ ((Over.map route).obj object).left where
  hom := (canonicalSumSquare route object).left
  inv := 𝟙 object.left
  hom_inv_id := by
    rw [canonicalSumSquare_domain]
    exact Category.id_comp _
  inv_hom_id := by
    rw [canonicalSumSquare_domain]
    exact Category.id_comp _

@[reassoc] theorem strongSumComparison_display :
    (strongSumComparison route object).hom ≫ ((Over.map route).obj object).hom =
      object.hom ≫ route := by
  change (canonicalSumSquare route object).left ≫ _ = _
  rw [canonicalSumSquare_domain]
  exact Category.id_comp _

def strongSum : Over.forget source ≅ Over.map route ⋙ Over.forget target :=
  NatIso.ofComponents (strongSumComparison route) (by
    intro first second arrow
    change arrow.left ≫ (canonicalSumSquare route second).left =
      (canonicalSumSquare route first).left ≫ arrow.left
    rw [canonicalSumSquare_domain, canonicalSumSquare_domain]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

instance canonicalSumSquare_lift :
    Arrow.rightFunc.IsHomLift route (canonicalSumSquare route object) := by
  apply IsHomLift.of_fac _ route _ rfl rfl
  change route = 𝟙 source ≫ (canonicalSumSquare route object).right ≫ 𝟙 target
  rw [canonicalSumSquare_base]
  exact ((Category.id_comp (route ≫ 𝟙 target)).trans (Category.comp_id route)).symm

instance canonicalSumSquare_stronglyCocartesian :
    Arrow.rightFunc.IsStronglyCocartesian route (canonicalSumSquare route object) where
  toIsHomLift := inferInstance
  universal_property' := by
    intro result next supplied suppliedLift
    have := suppliedLift
    have base : route ≫ next = supplied.right :=
      IsHomLift.eq_of_isHomLift Arrow.rightFunc (route ≫ next) supplied
    let factor : (fibreInclusion target).obj ((Over.map route).obj object) ⟶ result :=
      Arrow.homMk supplied.left next (by
        change supplied.left ≫ result.hom = (object.hom ≫ route) ≫ next
        rw [Category.assoc, base]
        exact Arrow.w supplied)
    refine ⟨factor, ⟨?_, ?_⟩, ?_⟩
    · change Arrow.rightFunc.IsHomLift (Arrow.rightFunc.map factor) factor
      infer_instance
    · apply Arrow.hom_ext
      · change (canonicalSumSquare route object).left ≫ supplied.left = supplied.left
        rw [canonicalSumSquare_domain]
        exact Category.id_comp _
      · change (canonicalSumSquare route object).right ≫ next = supplied.right
        rw [canonicalSumSquare_base]
        exact base
    · intro candidate properties
      have := properties.1
      apply Arrow.hom_ext
      · have readout := congrArg Arrow.Hom.left properties.2
        change (canonicalSumSquare route object).left ≫ candidate.left = supplied.left at readout
        rw [canonicalSumSquare_domain] at readout
        exact (Category.id_comp _).symm.trans readout
      · exact (IsHomLift.eq_of_isHomLift Arrow.rightFunc next candidate).symm

end Mettapedia.CategoryTheory.CodomainComprehension
