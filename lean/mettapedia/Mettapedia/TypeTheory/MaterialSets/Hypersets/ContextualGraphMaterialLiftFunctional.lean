import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalProducts

/-!
# Compatible material products at independently formed universe levels

Uniform full-future compatibility certificates are transported in both
directions. Consequently the actual upper compatible subfamily and the
lifted lower subfamily have inverse natural receipt maps, matching material
function bodies and matching enclosing carriers. No certificate is selected
from the classification proposition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftFunctional

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphMaterialFamilies ContextualGraphMaterialProducts
open ContextualGraphMaterialFunctionalProducts ContextualGraphMaterialLift

universe u
variable {D : Type u} [Category.{u} D] {original : D ⥤ Type u}
variable (domain : Family original) (body : Family (total domain.native))

abbrev upper := functionalPi (raise domain) (raisedBody domain body)
abbrev retained := raise (functionalPi domain body)

def upperLocal (point : Upper (D := D))
    (receipt : (total (nativeProduct (raise domain) (raisedBody domain body))).obj point)
    (certificate : LocalData domain body point.down
      ((ContextualGraphMaterialLiftProducts.functionParameterChange domain body).app point receipt).down) :
    LocalData (raise domain) (raisedBody domain body) point receipt := by
  intro first second same
  exact (Equal.ofEq (ContextualGraphMaterialLiftProducts.result_value domain body
    ⟨point, receipt.1⟩ receipt.2 first)).trans
      ((ContextualGraphUniverseLift.preserve
        (certificate first.down second.down (ContextualGraphUniverseLift.reflect same))).trans
          (Equal.ofEq (ContextualGraphMaterialLiftProducts.result_value domain body
            ⟨point, receipt.1⟩ receipt.2 second)).symm)

def lowerLocal (point : Upper (D := D))
    (receipt : (total (nativeProduct (raise domain) (raisedBody domain body))).obj point)
    (certificate : LocalData (raise domain) (raisedBody domain body) point receipt) :
    LocalData domain body point.down
      ((ContextualGraphMaterialLiftProducts.functionParameterChange domain body).app point receipt).down := by
  intro first second same
  exact ContextualGraphUniverseLift.reflect
    ((Equal.ofEq (ContextualGraphMaterialLiftProducts.result_value domain body
      ⟨point, receipt.1⟩ receipt.2 (ULift.up first))).symm.trans
        ((certificate (ULift.up first) (ULift.up second) (ContextualGraphUniverseLift.preserve same)).trans
          (Equal.ofEq (ContextualGraphMaterialLiftProducts.result_value domain body
            ⟨point, receipt.1⟩ receipt.2 (ULift.up second)))))

def upperData (point : Upper (D := D))
    (receipt : (total (nativeProduct (raise domain) (raisedBody domain body))).obj point)
    (certificate : FullData domain body point.down
      ((ContextualGraphMaterialLiftProducts.functionParameterChange domain body).app point receipt).down) :
    FullData (raise domain) (raisedBody domain body) point receipt :=
  fun future => upperLocal domain body future.1 _
    (cast (congrArg (LocalData domain body future.1.down)
      (congrArg ULift.down ((ContextualGraphMaterialLiftProducts.functionParameterChange domain body).naturality
        future.2 receipt))) (certificate ⟨future.1.down, future.2.down⟩))

def lowerData (point : Upper (D := D))
    (receipt : (total (nativeProduct (raise domain) (raisedBody domain body))).obj point)
    (certificate : FullData (raise domain) (raisedBody domain body) point receipt) :
    FullData domain body point.down
      ((ContextualGraphMaterialLiftProducts.functionParameterChange domain body).app point receipt).down :=
  fun future => cast (congrArg (LocalData domain body future.1)
    (congrArg ULift.down ((ContextualGraphMaterialLiftProducts.functionParameterChange domain body).naturality
      (PresheafSiteLift.Site.upFunctor.map future.2) receipt)).symm)
      (lowerLocal domain body (PresheafSiteLift.Site.upFunctor.obj future.1) _
        (certificate ⟨PresheafSiteLift.Site.upFunctor.obj future.1,
          PresheafSiteLift.Site.upFunctor.map future.2⟩))

def forward : NaturalHom (upper domain body).native (retained domain body).native where
  app point function := ULift.up
    ⟨((ContextualGraphMaterialLiftProducts.forward domain body).app point function.val).down,
      function.property.elim (fun certificate =>
        ⟨lowerData domain body point.1 ⟨point.2, function.val⟩ certificate⟩)⟩
  naturality step function := ULift.ext _ _ (Subtype.ext (congrArg ULift.down
    ((ContextualGraphMaterialLiftProducts.forward domain body).naturality step function.val)))

def backwardData (point : (base original).Elements)
    (function : (nativeProduct domain body).obj ((elementsDown original).obj point))
    (certificate : FullData domain body point.1.down ⟨point.2.down, function⟩) :
    FullData (raise domain) (raisedBody domain body) point.1
      ⟨point.2, (ContextualGraphMaterialLiftProducts.backward domain body).app point (ULift.up function)⟩ :=
  upperData domain body point.1 _
    (cast (congrArg (FullData domain body point.1.down)
      (congrArg (Sigma.mk point.2.down) (congrArg ULift.down
        ((ContextualGraphMaterialLiftProducts.nativeEquiv domain body point).apply_symm_apply
          (ULift.up function))).symm)) certificate)

def backward : NaturalHom (retained domain body).native (upper domain body).native where
  app point function :=
    ⟨(ContextualGraphMaterialLiftProducts.backward domain body).app point (ULift.up function.down.val),
      function.down.property.elim (fun certificate =>
        ⟨backwardData domain body point function.down.val certificate⟩)⟩
  naturality step function := Subtype.ext
    ((ContextualGraphMaterialLiftProducts.backward domain body).naturality step (ULift.up function.down.val))

theorem forward_backward : (forward domain body).comp (backward domain body) =
    ContextualSmallMapConstructions.identity (upper domain body).native := by
  apply NaturalHom.ext
  intro point function
  exact Subtype.ext ((ContextualGraphMaterialLiftProducts.nativeEquiv domain body point).symm_apply_apply function.val)

theorem backward_forward : (backward domain body).comp (forward domain body) =
    ContextualSmallMapConstructions.identity (retained domain body).native := by
  apply NaturalHom.ext
  intro point function
  exact ULift.ext _ _ (Subtype.ext (congrArg ULift.down
    ((ContextualGraphMaterialLiftProducts.nativeEquiv domain body point).apply_symm_apply
      (ULift.up function.down.val))))

def nativeEquiv (point : (base original).Elements) :
    (upper domain body).native.obj point ≃ (retained domain body).native.obj point where
  toFun := (forward domain body).app point
  invFun := (backward domain body).app point
  left_inv function := congrArg (fun operation => operation.app point function) (forward_backward domain body)
  right_inv function := congrArg (fun operation => operation.app point function) (backward_forward domain body)

def readingComparison (point : (base original).Elements)
    (function : (upper domain body).native.obj point) :
    Equal (termValue (upper domain body) point function)
      (termValue (retained domain body) point ((forward domain body).app point function)) :=
  ContextualGraphMaterialLiftProducts.readingComparison domain body point function.val

def inverseReading (point : (base original).Elements)
    (function : (retained domain body).native.obj point) :
    Equal (termValue (retained domain body) point function)
      (termValue (upper domain body) point ((backward domain body).app point function)) :=
  (Equal.ofEq (congrArg (termValue (retained domain body) point)
    ((nativeEquiv domain body point).apply_symm_apply function))).symm.trans
      (readingComparison domain body point ((backward domain body).app point function)).symm

def carrierComparison (point : (base original).Elements) :
    Equal (ContextualGraphUniverseLift.value
      ((carrier (functionalPi domain body)).app point.1.down point.2.down))
      ((carrier (upper domain body)).app point.1 point.2) :=
  (ContextualGraphMaterialLift.carrierComparison (functionalPi domain body) point.1 point.2.down).trans
    (ContextualGraphMaterialSubstitution.carrierCongr (upper domain body) (retained domain body)
      (forward domain body) (backward domain body) (readingComparison domain body)
      (fun point function =>
        (Equal.ofEq (congrArg (termValue (retained domain body) point)
          ((nativeEquiv domain body point).apply_symm_apply function))).symm.trans
            (readingComparison domain body point ((backward domain body).app point function)).symm) point).symm

def sectionComparison : (upper domain body).native.sections ≃ (retained domain body).native.sections where
  toFun := (forward domain body).mapSection
  invFun := (backward domain body).mapSection
  left_inv whole := by
    apply Subtype.ext
    funext point
    exact (nativeEquiv domain body point).symm_apply_apply (whole.val point)
  right_inv whole := by
    apply Subtype.ext
    funext point
    exact (nativeEquiv domain body point).apply_symm_apply (whole.val point)

def literalSectionComparison : (literal (upper domain body)).sections ≃
    (literal (retained domain body)).sections :=
  (sectionDecoder (upper domain body)).trans
    ((sectionComparison domain body).trans (sectionDecoder (retained domain body)).symm)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftFunctional
