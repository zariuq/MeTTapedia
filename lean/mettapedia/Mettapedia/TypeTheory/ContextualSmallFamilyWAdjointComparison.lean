import Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitutionCoherence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWComparison

/-!
# Complete W polynomials and existing dependent-function adjoints

The constructed original-bound polynomial is compared with the existing
dependent-section carrier on its small future cone. The inverse retains
all arrows and positions, and branch evaluation and restriction commute.
No smallness of the wider parameter category is used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWAdjointComparison

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers PowerClassPresheafBaseChange
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) (target : base.Elements ⥤ Type u)

abbrev AdjointAt (point : base.Elements) (future : Future.Objects point.1) : Type u :=
  Σ label : (futureDomain domain point).obj future,
    DependentSection (futureBody domain body point)
      (ContextualWComparison.branchTarget (futureDomain domain point) (futureBody domain body point)
        (futureDomain target point)) ⟨future, label⟩

def polynomialAdjointEquiv (point : base.Elements) (future : Future.Objects point.1) :
    ContextualWPolynomialReindexing.At (ContextualSmallFamilyWPolynomial.signature domain body target point) future ≃
      AdjointAt domain body target point future where
  toFun node := ⟨node.1, ContextualWComparison.branchEquiv (futureDomain domain point) (futureBody domain body point)
    (futureDomain target point) future node.1 node.2⟩
  invFun node := ⟨node.1, (ContextualWComparison.branchEquiv (futureDomain domain point) (futureBody domain body point)
    (futureDomain target point) future node.1).symm node.2⟩
  left_inv node := by
    rcases node with ⟨label, branches⟩
    exact congrArg (Sigma.mk label) ((ContextualWComparison.branchEquiv (futureDomain domain point)
      (futureBody domain body point) (futureDomain target point) future label).symm_apply_apply branches)
  right_inv node := by
    rcases node with ⟨label, sectionValue⟩
    exact congrArg (Sigma.mk label) ((ContextualWComparison.branchEquiv (futureDomain domain point)
      (futureBody domain body point) (futureDomain target point) future label).apply_symm_apply sectionValue)

theorem polynomialAdjointEquiv_value (point : base.Elements) (future : Future.Objects point.1)
    (node : ContextualWPolynomialReindexing.At (ContextualSmallFamilyWPolynomial.signature domain body target point) future)
    (later : Future.Objects point.1) (arrow : future ⟶ later)
    (position : ContextualWTypes.Position (futureDomain domain point) (futureBody domain body point) node.1 arrow) :
    (polynomialAdjointEquiv domain body target point future node).2.app
      ⟨later, (futureDomain domain point).map arrow node.1⟩
      (argumentMap (futureDomain domain point) arrow node.1) position = node.2.app later arrow position :=
  ContextualWComparison.branchEquiv_value (futureDomain domain point) (futureBody domain body point)
    (futureDomain target point) future node.1 node.2 later arrow position

theorem polynomialAdjointEquiv_restrict (point : base.Elements) {first second : Future.Objects point.1}
    (step : first ⟶ second)
    (node : ContextualWPolynomialReindexing.At (ContextualSmallFamilyWPolynomial.signature domain body target point) first) :
    (polynomialAdjointEquiv domain body target point second
      ((ContextualWPolynomialReindexing.family (ContextualSmallFamilyWPolynomial.signature domain body target point)).map step node)).2 =
      DependentSection.restrict (futureBody domain body point)
        (ContextualWComparison.branchTarget (futureDomain domain point) (futureBody domain body point)
          (futureDomain target point)) (argumentMap (futureDomain domain point) step node.1)
        (polynomialAdjointEquiv domain body target point first node).2 :=
  ContextualWComparison.branchEquiv_restrict (futureDomain domain point) (futureBody domain body point)
    (futureDomain target point) step node.1 node.2

end Mettapedia.TypeTheory.ContextualSmallFamilyWAdjointComparison
