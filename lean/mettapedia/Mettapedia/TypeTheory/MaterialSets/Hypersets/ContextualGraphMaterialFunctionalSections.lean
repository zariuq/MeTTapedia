import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalSubstitution

/-!
# Abstraction and application of compatible complete sections

The actual native lambda equivalence restricts to bodies whose entire
future functions satisfy the constructed compatibility predicate. Its
inverse retains each native body receipt. Beta and eta therefore hold on
literal dependent sections while the material kernel is separately proved.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalSections

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphMaterialFamilies
open ContextualGraphMaterialProducts ContextualGraphMaterialFunctionalProducts

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : Family base) (body : Family (total domain.native))

abbrev QualifiedBody : Type u :=
  {term : body.native.sections // ∀ point : base.Elements,
    Nonempty (FullData domain body point.1
      ⟨point.2, (ContextualGraphFamilyProducts.nativeLambda domain.native body.native term).val point⟩)}

def abstract (term : QualifiedBody domain body) : (compatibleNative domain body).sections :=
  ⟨fun point => ⟨(ContextualGraphFamilyProducts.nativeLambda domain.native body.native term.val).val point,
      term.property point⟩,
    fun {_ _} step => Subtype.ext
      ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native term.val).property step)⟩

def applySection (term : (compatibleNative domain body).sections) : QualifiedBody domain body := by
  let native := (ContextualGraphMaterialFunctionalProducts.forget domain body).mapSection term
  refine ⟨(ContextualGraphFamilyProducts.nativeLambda domain.native body.native).symm native, ?_⟩
  intro point
  have same := congrArg (fun whole : (nativeProduct domain body).sections => whole.val point)
    ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native).apply_symm_apply native)
  exact cast (congrArg
    (fun function => Nonempty (FullData domain body point.1 ⟨point.2, function⟩)) same.symm)
    (term.val point).property

theorem abstract_apply (term : (compatibleNative domain body).sections) :
    abstract domain body (applySection domain body term) = term := by
  apply Subtype.ext
  funext point
  apply Subtype.ext
  exact congrArg (fun whole : (nativeProduct domain body).sections => whole.val point)
    ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native).apply_symm_apply
      ((ContextualGraphMaterialFunctionalProducts.forget domain body).mapSection term))

theorem apply_abstract (term : QualifiedBody domain body) :
    applySection domain body (abstract domain body term) = term :=
  Subtype.ext ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native).symm_apply_apply term.val)

def lambdaEquiv : QualifiedBody domain body ≃ (compatibleNative domain body).sections where
  toFun := abstract domain body
  invFun := applySection domain body
  left_inv := apply_abstract domain body
  right_inv := abstract_apply domain body

theorem beta (term : QualifiedBody domain body) (point : base.Elements) (argument : domain.native.obj point) :
    evaluated domain body point ((abstract domain body term).val point).val argument =
      term.val.val ((flatten domain.native).obj ⟨point, argument⟩) :=
  ContextualGraphMaterialSections.native_lambda_evaluation domain body term.val point argument

abbrev QualifiedLiteralBody : Type u :=
  {term : (literal body).sections // ∀ point : base.Elements,
    Nonempty (FullData domain body point.1
      ⟨point.2, (ContextualGraphFamilyProducts.nativeLambda domain.native body.native
        (sectionDecoder body term)).val point⟩)}

def bodyDecoder : QualifiedLiteralBody domain body ≃ QualifiedBody domain body where
  toFun term := ⟨sectionDecoder body term.val, term.property⟩
  invFun term := ⟨(sectionDecoder body).symm term.val, by
    intro point
    have same := (sectionDecoder body).apply_symm_apply term.val
    exact cast (congrArg (fun decoded => Nonempty (FullData domain body point.1
      ⟨point.2, (ContextualGraphFamilyProducts.nativeLambda domain.native body.native decoded).val point⟩)) same.symm)
      (term.property point)⟩
  left_inv term := Subtype.ext ((sectionDecoder body).symm_apply_apply term.val)
  right_inv term := Subtype.ext ((sectionDecoder body).apply_symm_apply term.val)

def literalLambdaEquiv : QualifiedLiteralBody domain body ≃ (literal (functionalPi domain body)).sections :=
  (bodyDecoder domain body).trans ((lambdaEquiv domain body).trans (sectionDecoder (functionalPi domain body)).symm)

theorem literal_beta (term : QualifiedLiteralBody domain body) (point : base.Elements)
    (argument : domain.native.obj point) :
    evaluated domain body point
        (((sectionDecoder (functionalPi domain body) (literalLambdaEquiv domain body term)).val point).val) argument =
      (sectionDecoder body term.val).val ((flatten domain.native).obj ⟨point, argument⟩) :=
  beta domain body ((bodyDecoder domain body) term) point argument

theorem literal_eta (term : (literal (functionalPi domain body)).sections) :
    literalLambdaEquiv domain body ((literalLambdaEquiv domain body).symm term) = term :=
  (literalLambdaEquiv domain body).apply_symm_apply term

variable {other : D ⥤ Type u} (change : NaturalHom other base)

def reindexBody (term : QualifiedBody domain body) :
    QualifiedBody (ContextualGraphMaterialSubstitution.domainUnder domain change)
      (ContextualGraphMaterialSubstitution.bodyUnder domain body change) := by
  refine ⟨ContextualSmallFamilyIdentity.reindexSection (totalChange domain.native change) body.native term.val, ?_⟩
  intro point
  have same := congrArg (fun whole => whole.val point)
    (ContextualGraphMaterialSubstitution.lambda_substitution domain body change term.val)
  exact (term.property ((elementMap change).obj point)).elim (fun certificate =>
    ⟨cast (congrArg
      (fun function => FullData (ContextualGraphMaterialSubstitution.domainUnder domain change)
        (ContextualGraphMaterialSubstitution.bodyUnder domain body change) point.1 ⟨point.2, function⟩) same)
      (ContextualGraphMaterialFunctionalSubstitution.forwardData domain body change point _ certificate)⟩)

theorem abstraction_substitution (term : QualifiedBody domain body) :
    ContextualGraphMaterialFunctionalSubstitution.sectionComparison domain body change
      (ContextualSmallFamilyIdentity.reindexSection change (compatibleNative domain body) (abstract domain body term)) =
      abstract (ContextualGraphMaterialSubstitution.domainUnder domain change)
        (ContextualGraphMaterialSubstitution.bodyUnder domain body change) (reindexBody domain body change term) := by
  apply Subtype.ext
  funext point
  apply Subtype.ext
  exact congrArg (fun whole => whole.val point)
    (ContextualGraphMaterialSubstitution.lambda_substitution domain body change term.val)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalSections
