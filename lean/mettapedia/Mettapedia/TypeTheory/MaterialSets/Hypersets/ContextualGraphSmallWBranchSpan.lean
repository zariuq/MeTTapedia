import Mettapedia.TypeTheory.ContextualSmallFamilyWObservation
import Mettapedia.TypeTheory.ContextualSmallFamilyComprehension
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphDiagrams

/-!
# Actual branch span of generated original-small W families

The current observations come from the complete native polynomial and
its proved destructor. State nodes retain their actual parameter, and
branch transport uses the declared dependent position family. Naturality
is derived from full-future polynomial evaluation; no independently
recentered graph is asserted to be literally the original graph.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWBranchSpan

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes ContextualSmallFamilyWAlgebra
open ContextualGraphDiagrams

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

/-- Totalization retains the actual parameter while applying a native
natural operation to its fibre. -/
def totalOperation {first second : base.Elements ⥤ Type u} (operation : NatTrans first second) :
    NaturalHom (total first) (total second) where
  app point receipt := ⟨receipt.1, operation.app ⟨point, receipt.1⟩ receipt.2⟩
  naturality {firstPoint secondPoint} arrival receipt := by
    apply congrArg (Sigma.mk (base.map arrival receipt.1))
    exact (congrArg (fun map => map receipt.2)
      (operation.naturality (CategoryOfElements.homMk (F := base)
        ⟨firstPoint, receipt.1⟩ ⟨secondPoint, base.map arrival receipt.1⟩ arrival rfl))).symm

noncomputable def labelNative : NatTrans (w domain body) domain :=
  ((NaturalHom.ofNatTrans (ContextualSmallFamilyWConstructor.destructor domain body)).comp
    (NaturalHom.ofNatTrans (ContextualSmallFamilyWObservation.rootLabelMap domain body (w domain body)))).toNatTrans

noncomputable def labelTarget : NaturalHom (total (w domain body)) (total domain) :=
  totalOperation (labelNative domain body)

def displayedBody : (total domain).Elements ⥤ Type u := restrict (unflatten domain) body

noncomputable def branches : (total (w domain body)).Elements ⥤ Type u :=
  restrict (elementMap (labelTarget domain body)) (displayedBody domain body)

noncomputable def argumentTarget : NaturalHom (total (branches domain body)) (total (displayedBody domain body)) :=
  ContextualSmallFamilyComprehension.totalChange (displayedBody domain body) (labelTarget domain body)

noncomputable def child (point : base.Elements) (tree : (w domain body).obj point)
    (branch : body.obj ⟨point, (labelNative domain body).app point tree⟩) : (w domain body).obj point :=
  ContextualSmallFamilyWObservation.evaluate domain body (w domain body) point
    (destructorValue domain body point tree) branch

/-- The fibre expression uses the actual induced dependent arrow, not
merely an equality of current supports. -/
theorem child_natural {first second : base.Elements} (step : first ⟶ second)
    (tree : (w domain body).obj first)
    (branch : body.obj ⟨first, (labelNative domain body).app first tree⟩)
    (dependentStep : domain.elementsMk first ((labelNative domain body).app first tree) ⟶
      domain.elementsMk second ((labelNative domain body).app second ((w domain body).map step tree)))
    (underlying : dependentStep.1 = step) :
    (w domain body).map step (child domain body first tree branch) =
      child domain body second ((w domain body).map step tree) (body.map dependentStep branch) := by
  have nodes : ContextualSmallFamilyWPolynomial.pMap domain body (w domain body) step
      (destructorValue domain body first tree) =
        destructorValue domain body second ((w domain body).map step tree) :=
    (congrArg (fun operation => operation tree)
      ((ContextualSmallFamilyWConstructor.destructor domain body).naturality step)).symm
  have labels := congrArg (fun operation => operation tree) ((labelNative domain body).naturality step)
  have targetEq : (⟨second, domain.map step ((labelNative domain body).app first tree)⟩ : domain.Elements) =
      ⟨second, (labelNative domain body).app second ((w domain body).map step tree)⟩ :=
    Sigma.ext rfl (heq_of_eq labels.symm)
  have values := familyMap_heq body rfl targetEq
    (argumentStep domain step ((labelNative domain body).app first tree)) dependentStep
    (elementArrow_heq rfl targetEq _ _ (heq_of_eq underlying.symm)) branch branch HEq.rfl
  have evaluated := ContextualSmallFamilyWObservation.evaluate_natural domain body (w domain body) step
    (destructorValue domain body first tree) branch
  have casted := ContextualSmallFamilyUniverse.cast_heq
    (congrArg (fun label => body.obj ⟨second, label⟩)
      (ContextualSmallFamilyWObservation.rootLabel_natural domain body (w domain body) step
        (destructorValue domain body first tree)))
    (body.map (argumentStep domain step ((labelNative domain body).app first tree)) branch)
  exact evaluated.trans (ContextualSmallFamilyWObservation.evaluate_node_congr domain body (w domain body)
    second _ _ nodes _ _ (casted.trans values))

noncomputable def childTarget : NaturalHom (total (branches domain body)) (total (w domain body)) where
  app point receipt := ⟨receipt.1.1, child domain body ⟨point, receipt.1.1⟩ receipt.1.2 receipt.2⟩
  naturality {first second} arrival receipt := by
    let step := CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1⟩
      ⟨second, base.map arrival receipt.1.1⟩ arrival rfl
    let branchStep := (unflatten domain).map ((elementMap (labelTarget domain body)).map
      (CategoryOfElements.homMk (F := total (w domain body)) ⟨first, receipt.1⟩
        ⟨second, (total (w domain body)).map arrival receipt.1⟩ arrival rfl))
    exact congrArg (Sigma.mk (base.map arrival receipt.1.1))
      (child_natural domain body step receipt.1.2 receipt.2 branchStep rfl)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWBranchSpan
