import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialSubstitution

/-!
# Substitution of constructed compatible material products

The actual native future-product comparison transports uniform matching
certificates in both directions. Hence the independently formed compatible
subfamily has inverse natural receipt maps to the retained substituted
subfamily. The full attached material carriers, and their whole literal
sections, are compared through those maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalSubstitution

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphMaterialFamilies
open ContextualGraphMaterialProducts ContextualGraphMaterialFunctionalProducts
open ContextualGraphMaterialSubstitution

universe u
variable {D : Type u} [Category.{u} D] {base other : D ⥤ Type u}
variable (domain : Family base) (body : Family (total domain.native)) (change : NaturalHom other base)

theorem result_comparison (point : other.Elements)
    (function : (productUnder domain body change).native.obj point)
    (argument : (domainUnder domain change).native.obj point) :
    resultValue (domainUnder domain change) (bodyUnder domain body change) point function argument =
      resultValue domain body ((elementMap change).obj point)
        ((productBackward domain body change).app point function) argument := by
  let original := (productNativeComparison domain body change point).symm function
  have normalized := congrArg
    (fun native => evaluated (domainUnder domain change) (bodyUnder domain body change) point native argument)
    ((productNativeComparison domain body change point).apply_symm_apply function)
  exact congrArg
    (termValue body ((flatten domain.native).obj ⟨(elementMap change).obj point, argument⟩))
    (normalized.symm.trans (product_evaluation domain body change point original argument))

def newLocal (point : D)
    (receipt : (total (nativeProduct (domainUnder domain change) (bodyUnder domain body change))).obj point)
    (certificate : LocalData domain body point ((functionParameterChange domain body change).app point receipt)) :
    LocalData (domainUnder domain change) (bodyUnder domain body change) point receipt := by
  intro first second same
  exact (Equal.ofEq (result_comparison domain body change ⟨point, receipt.1⟩ receipt.2 first)).trans
    ((certificate first second same).trans
      (Equal.ofEq (result_comparison domain body change ⟨point, receipt.1⟩ receipt.2 second)).symm)

def oldLocal (point : D)
    (receipt : (total (nativeProduct (domainUnder domain change) (bodyUnder domain body change))).obj point)
    (certificate : LocalData (domainUnder domain change) (bodyUnder domain body change) point receipt) :
    LocalData domain body point ((functionParameterChange domain body change).app point receipt) := by
  intro first second same
  exact (Equal.ofEq (result_comparison domain body change ⟨point, receipt.1⟩ receipt.2 first)).symm.trans
    ((certificate first second same).trans
      (Equal.ofEq (result_comparison domain body change ⟨point, receipt.1⟩ receipt.2 second)))

/-- All future certificates are transported through the actual natural
map on parameter/function receipts, without choosing matching strategies. -/
def newData (point : D)
    (receipt : (total (nativeProduct (domainUnder domain change) (bodyUnder domain body change))).obj point)
    (certificate : FullData domain body point ((functionParameterChange domain body change).app point receipt)) :
    FullData (domainUnder domain change) (bodyUnder domain body change) point receipt :=
  fun future => newLocal domain body change future.1 _
    (cast (congrArg (LocalData domain body future.1)
      ((functionParameterChange domain body change).naturality future.2 receipt)) (certificate future))

def oldData (point : D)
    (receipt : (total (nativeProduct (domainUnder domain change) (bodyUnder domain body change))).obj point)
    (certificate : FullData (domainUnder domain change) (bodyUnder domain body change) point receipt) :
    FullData domain body point ((functionParameterChange domain body change).app point receipt) :=
  fun future => cast (congrArg (LocalData domain body future.1)
    ((functionParameterChange domain body change).naturality future.2 receipt).symm)
    (oldLocal domain body change future.1 _ (certificate future))

def forwardData (point : other.Elements)
    (function : (substitute (pi domain body) change).native.obj point)
    (certificate : FullData domain body point.1 ⟨change.app point.1 point.2, function⟩) :
    FullData (domainUnder domain change) (bodyUnder domain body change) point.1
      ⟨point.2, (productForward domain body change).app point function⟩ :=
  newData domain body change point.1 _
    (cast (congrArg (FullData domain body point.1)
      (congrArg (Sigma.mk (change.app point.1 point.2))
        ((productNativeComparison domain body change point).symm_apply_apply function).symm)) certificate)

abbrev functionalUnder := functionalPi (domainUnder domain change) (bodyUnder domain body change)
abbrev functionalRetained := substitute (functionalPi domain body) change

def forward : NaturalHom (functionalRetained domain body change).native (functionalUnder domain body change).native where
  app point function :=
    ⟨(productForward domain body change).app point function.val,
      function.property.elim (fun certificate => ⟨forwardData domain body change point function.val certificate⟩)⟩
  naturality step function := Subtype.ext ((productForward domain body change).naturality step function.val)

def backward : NaturalHom (functionalUnder domain body change).native (functionalRetained domain body change).native where
  app point function :=
    ⟨(productBackward domain body change).app point function.val,
      function.property.elim (fun certificate => ⟨oldData domain body change point.1 ⟨point.2, function.val⟩ certificate⟩)⟩
  naturality step function := Subtype.ext ((productBackward domain body change).naturality step function.val)

theorem forward_backward : (forward domain body change).comp (backward domain body change) =
    ContextualSmallMapConstructions.identity (functionalRetained domain body change).native := by
  apply NaturalHom.ext
  intro point function
  exact Subtype.ext ((productNativeComparison domain body change point).symm_apply_apply function.val)

theorem backward_forward : (backward domain body change).comp (forward domain body change) =
    ContextualSmallMapConstructions.identity (functionalUnder domain body change).native := by
  apply NaturalHom.ext
  intro point function
  exact Subtype.ext ((productNativeComparison domain body change point).apply_symm_apply function.val)

def nativeComparison (point : other.Elements) :
    (functionalRetained domain body change).native.obj point ≃
      (functionalUnder domain body change).native.obj point where
  toFun := (forward domain body change).app point
  invFun := (backward domain body change).app point
  left_inv function := Subtype.ext ((productNativeComparison domain body change point).symm_apply_apply function.val)
  right_inv function := Subtype.ext ((productNativeComparison domain body change point).apply_symm_apply function.val)

def readingComparison (point : other.Elements)
    (function : (functionalUnder domain body change).native.obj point) :
    Equal (termValue (functionalUnder domain body change) point function)
      (termValue (functionalRetained domain body change) point ((backward domain body change).app point function)) :=
  productReadingComparison domain body change point function.val

def carrierComparison (point : other.Elements) :
    Equal ((carrier (functionalUnder domain body change)).app point.1 point.2)
      ((carrier (functionalPi domain body)).app point.1 (change.app point.1 point.2)) :=
  (carrierCongr (functionalUnder domain body change) (functionalRetained domain body change)
    (backward domain body change) (forward domain body change)
    (readingComparison domain body change)
    (fun point function =>
      (Equal.ofEq (congrArg (termValue (functionalRetained domain body change) point)
        ((nativeComparison domain body change point).symm_apply_apply function))).symm.trans
      (readingComparison domain body change point ((forward domain body change).app point function)).symm)
    point).trans (carrierUnder (functionalPi domain body) change point)

def sectionComparison : (functionalRetained domain body change).native.sections ≃
    (functionalUnder domain body change).native.sections where
  toFun := (forward domain body change).mapSection
  invFun := (backward domain body change).mapSection
  left_inv whole := by
    apply Subtype.ext
    funext point
    exact (nativeComparison domain body change point).symm_apply_apply (whole.val point)
  right_inv whole := by
    apply Subtype.ext
    funext point
    exact (nativeComparison domain body change point).apply_symm_apply (whole.val point)

def literalSectionComparison : (literal (functionalRetained domain body change)).sections ≃
    (literal (functionalUnder domain body change)).sections :=
  (sectionDecoder (functionalRetained domain body change)).trans
    ((sectionComparison domain body change).trans (sectionDecoder (functionalUnder domain body change)).symm)

theorem application_comparison (point : other.Elements)
    (function : (functionalRetained domain body change).native.obj point)
    (argument : (domainUnder domain change).native.obj point) :
    resultValue (domainUnder domain change) (bodyUnder domain body change) point
        ((nativeComparison domain body change point) function).val argument =
      resultValue domain body ((elementMap change).obj point) function.val argument := by
  exact congrArg (termValue body ((flatten domain.native).obj ⟨(elementMap change).obj point, argument⟩))
    (product_evaluation domain body change point function.val argument)

theorem classified_substitution (whole : (nativeProduct domain body).sections)
    (certificate : ∀ point : base.Elements, ApplicationCompatible domain body point (whole.val point)) :
    (ContextualGraphMaterialFunctionalProducts.forget (domainUnder domain change) (bodyUnder domain body change)).mapSection
      (sectionComparison domain body change
        (ContextualSmallFamilyIdentity.reindexSection change (compatibleNative domain body)
          (classifySection domain body whole certificate))) =
      productSectionComparison domain body change
        (ContextualSmallFamilyIdentity.reindexSection change (nativeProduct domain body) whole) := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalSubstitution
