import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialSections
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodySubstitution

/-!
# Reindexing actual material dependent families

Literal receipt comparisons retain the native substituted family. The
independently constructed attached carrier has full-future matching with
the retained carrier. Dependent sums are compared by their genuine native
pairs and actual component readings, rather than equality of authored
diagrams.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialSubstitution

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphMaterialFamilies
open ContextualGraphMaterialProducts

universe u
variable {D : Type u} [Category.{u} D] {base other : D ⥤ Type u}

def carrierUnder (family : Family base) (change : NaturalHom other base) (point : other.Elements) :
    Equal ((carrier (substitute family change)).app point.1 point.2)
      ((carrier family).app point.1 (change.app point.1 point.2)) :=
  ContextualGraphFamilyBodySubstitution.carrierComparison family.native family.reading change point

def sectionComparison (family : Family base) (change : NaturalHom other base) :
    (ContextualGraphReceiptFamilies.along (change.comp (carrier family))).sections ≃
      (literal (substitute family change)).sections :=
  ContextualGraphFamilyBodySubstitution.sectionComparison family.native family.reading change

theorem decoded_substitution (family : Family base) (change : NaturalHom other base)
    (term : (literal family).sections) :
    sectionDecoder (substitute family change)
        (ContextualGraphMaterialSections.pullSection family change term) =
      ContextualSmallFamilyIdentity.reindexSection change family.native (sectionDecoder family term) :=
  ContextualGraphMaterialSections.pullSection_decode family change term

/-- Natural maps with the declared value comparison induce an actual
membership action at every future. -/
def membershipAction (first second : Family base) (operation : NaturalHom first.native second.native)
    (reading : ∀ (point : base.Elements) (term : first.native.obj point),
      Equal (termValue first point term) (termValue second point (operation.app point term)))
    (point : base.Elements) (element : Value D point.1)
    (membership : Member element ((carrier first).app point.1 point.2)) :
    Member element ((carrier second).app point.1 point.2) :=
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode first.native first.reading point element membership
  ContextualGraphFamilyBodyComparison.memberIntro second.native second.reading point element
    (operation.app point decoded.1) (decoded.2.trans (reading point decoded.1))

def carrierCongr (first second : Family base)
    (forward : NaturalHom first.native second.native) (backward : NaturalHom second.native first.native)
    (forth : ∀ (point : base.Elements) (term : first.native.obj point),
      Equal (termValue first point term) (termValue second point (forward.app point term)))
    (back : ∀ (point : base.Elements) (term : second.native.obj point),
      Equal (termValue second point term) (termValue first point (backward.app point term)))
    (point : base.Elements) :
    Equal ((carrier first).app point.1 point.2) ((carrier second).app point.1 point.2) :=
  extensionality
    (fun target arrival element membership =>
      Member.transportParent (Equal.ofEq ((carrier second).naturality arrival point.2)).symm
        (membershipAction first second forward forth ⟨target, base.map arrival point.2⟩ element
          (Member.transportParent (Equal.ofEq ((carrier first).naturality arrival point.2)) membership)))
    (fun target arrival element membership =>
      Member.transportParent (Equal.ofEq ((carrier first).naturality arrival point.2)).symm
        (membershipAction second first backward back ⟨target, base.map arrival point.2⟩ element
          (Member.transportParent (Equal.ofEq ((carrier second).naturality arrival point.2)) membership)))

variable (domain : Family base) (body : Family (total domain.native)) (change : NaturalHom other base)

abbrev domainUnder := substitute domain change
abbrev bodyUnder := substitute body (totalChange domain.native change)
abbrev sumUnder := sigma (domainUnder domain change) (bodyUnder domain body change)

def sumForward : NaturalHom (sumUnder domain body change).native (substitute (sigma domain body) change).native where
  app _ term := term
  naturality _ _ := rfl

def sumBackward : NaturalHom (substitute (sigma domain body) change).native (sumUnder domain body change).native where
  app _ term := term
  naturality _ _ := rfl

theorem sum_forward_backward : (sumForward domain body change).comp (sumBackward domain body change) =
    ContextualSmallMapConstructions.identity (sumUnder domain body change).native := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem sum_backward_forward : (sumBackward domain body change).comp (sumForward domain body change) =
    ContextualSmallMapConstructions.identity (substitute (sigma domain body) change).native := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem sum_reading (point : other.Elements) (term : (sumUnder domain body change).native.obj point) :
    termValue (sumUnder domain body change) point term =
      termValue (substitute (sigma domain body) change) point ((sumForward domain body change).app point term) := rfl

def sumCarrierComparison (point : other.Elements) :
    Equal ((carrier (sumUnder domain body change)).app point.1 point.2)
      ((carrier (sigma domain body)).app point.1 (change.app point.1 point.2)) :=
  (carrierCongr (sumUnder domain body change) (substitute (sigma domain body) change)
    (sumForward domain body change) (sumBackward domain body change)
    (fun point term => Equal.ofEq (sum_reading domain body change point term))
    (fun _ _ => Equal.refl _) point).trans (carrierUnder (sigma domain body) change point)

abbrev productUnder := pi (domainUnder domain change) (bodyUnder domain body change)

/-- The comparison is constructed by restriction to the actual future
argument categories. No pointwise product carrier is supplied. -/
def productNativeComparison (point : other.Elements) :
    (substitute (pi domain body) change).native.obj point ≃
      (productUnder domain body change).native.obj point := by
  change (substitutedFamily (piDisplayed domain.native body.native) change).obj point ≃
    (piDisplayed (ContextualSmallFamilyTypeFormerCoherence.domainUnder change domain.native)
      (substitutedFamily body.native (totalChange domain.native change))).obj point
  unfold piDisplayed
  rw [indexedBody_substitution]
  exact ContextualSmallFamilyTypeFormerCoherence.productComparison change domain.native
    (indexedBody domain.native body.native) point

theorem product_evaluation (point : other.Elements)
    (function : (substitute (pi domain body) change).native.obj point)
    (argument : (domainUnder domain change).native.obj point) :
    evaluated (domainUnder domain change) (bodyUnder domain body change) point
        (productNativeComparison domain body change point function) argument =
      evaluated domain body ((elementMap change).obj point) function argument := by
  unfold evaluated productNativeComparison
  exact ContextualSmallFamilyTypeFormerCoherence.evaluate_substitution change domain.native
    (indexedBody domain.native body.native) point function argument

theorem product_future_value (point : other.Elements)
    (function : (substitute (pi domain body) change).native.obj point)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain (domainUnder domain change).native point).Elements) :
    HEq ((productNativeComparison domain body change point function).val argument)
      (function.val ((ContextualSmallFamilyTypeFormerCoherence.futureArgumentChange change domain.native point).obj argument)) := by
  unfold productNativeComparison
  exact ContextualSmallFamilyTypeFormerCoherence.productComparison_value change domain.native
    (indexedBody domain.native body.native) point function argument

def productForward : NaturalHom (substitute (pi domain body) change).native (productUnder domain body change).native :=
  NaturalHom.ofNatTrans (piDisplayedSubstitution domain.native change body.native)

theorem product_forward_value (point : other.Elements)
    (function : (substitute (pi domain body) change).native.obj point) :
    (productForward domain body change).app point function =
      productNativeComparison domain body change point function := rfl

def productBackward : NaturalHom (productUnder domain body change).native (substitute (pi domain body) change).native where
  app point := (productNativeComparison domain body change point).symm
  naturality {first second} step function := by
    apply (productNativeComparison domain body change second).injective
    have natural := (productForward domain body change).naturality step
      ((productNativeComparison domain body change first).symm function)
    exact natural.symm.trans (congrArg ((productUnder domain body change).native.map step)
      ((productNativeComparison domain body change first).apply_symm_apply function)) |>.trans
        ((productNativeComparison domain body change second).apply_symm_apply _).symm

theorem product_forward_backward : (productForward domain body change).comp (productBackward domain body change) =
    ContextualSmallMapConstructions.identity (substitute (pi domain body) change).native := by
  apply NaturalHom.ext
  intro point function
  exact (productNativeComparison domain body change point).symm_apply_apply function

theorem product_backward_forward : (productBackward domain body change).comp (productForward domain body change) =
    ContextualSmallMapConstructions.identity (productUnder domain body change).native := by
  apply NaturalHom.ext
  intro point function
  exact (productNativeComparison domain body change point).apply_symm_apply function

def functionReceiptChange : NaturalHom
    (total (productUnder domain body change).native) (total (substitute (pi domain body) change).native) where
  app point receipt := ⟨receipt.1, (productBackward domain body change).app ⟨point, receipt.1⟩ receipt.2⟩
  naturality {first second} arrival receipt := congrArg (Sigma.mk (other.map arrival receipt.1))
    ((productBackward domain body change).naturality
      (CategoryOfElements.homMk (F := other) ⟨first, receipt.1⟩
        ⟨second, other.map arrival receipt.1⟩ arrival rfl) receipt.2)

def functionParameterChange : NaturalHom (total (productUnder domain body change).native) (total (pi domain body).native) :=
  (functionReceiptChange domain body change).comp (substitutedTotalMap (pi domain body).native change)

abbrev retainedArguments : (total (productUnder domain body change).native).Elements ⥤ Type u :=
  substitutedFamily (arguments domain body) (functionParameterChange domain body change)

def argumentsForward : NaturalHom
    (arguments (domainUnder domain change) (bodyUnder domain body change)) (retainedArguments domain body change) where
  app _ argument := argument
  naturality _ _ := rfl

def argumentsBackward : NaturalHom (retainedArguments domain body change)
    (arguments (domainUnder domain change) (bodyUnder domain body change)) where
  app _ argument := argument
  naturality _ _ := rfl

def applicationFamily (first : Family base) (second : Family (total first.native)) :
    Family (total (pi first second).native) :=
  ⟨arguments first second, applicationReading first second⟩

theorem applications_reading (point : (total (productUnder domain body change).native).Elements)
    (argument : (arguments (domainUnder domain change) (bodyUnder domain body change)).obj point) :
    termValue (applicationFamily (domainUnder domain change) (bodyUnder domain body change)) point argument =
      termValue (substitute (applicationFamily domain body) (functionParameterChange domain body change)) point
        ((argumentsForward domain body change).app point argument) := by
  let parameter : other.Elements := ⟨point.1, point.2.1⟩
  let original := (productNativeComparison domain body change parameter).symm point.2.2
  have evaluatedSame := product_evaluation domain body change parameter original argument
  have normalized := congrArg
    (fun function => evaluated (domainUnder domain change) (bodyUnder domain body change) parameter function argument)
    ((productNativeComparison domain body change parameter).apply_symm_apply point.2.2)
  exact congrArg (fun result => ContextualGraphOrderedPairs.orderedPair
      (termValue domain ((elementMap change).obj parameter) argument)
      (termValue body ((flatten domain.native).obj ⟨(elementMap change).obj parameter, argument⟩) result))
    (normalized.symm.trans evaluatedSame)

def productReadingComparison (point : other.Elements)
    (function : (productUnder domain body change).native.obj point) :
    Equal (termValue (productUnder domain body change) point function)
      (termValue (substitute (pi domain body) change) point
        ((productBackward domain body change).app point function)) :=
  (carrierCongr
    (applicationFamily (domainUnder domain change) (bodyUnder domain body change))
    (substitute (applicationFamily domain body) (functionParameterChange domain body change))
    (argumentsForward domain body change) (argumentsBackward domain body change)
    (fun point argument => Equal.ofEq (applications_reading domain body change point argument))
    (fun point argument => (Equal.ofEq (applications_reading domain body change point argument)).symm)
    ⟨point.1, ⟨point.2, function⟩⟩).trans
      (carrierUnder (applicationFamily domain body) (functionParameterChange domain body change)
        ⟨point.1, ⟨point.2, function⟩⟩)

def productCarrierComparison (point : other.Elements) :
    Equal ((carrier (productUnder domain body change)).app point.1 point.2)
      ((carrier (pi domain body)).app point.1 (change.app point.1 point.2)) :=
  (carrierCongr (productUnder domain body change) (substitute (pi domain body) change)
    (productBackward domain body change) (productForward domain body change)
    (productReadingComparison domain body change)
    (fun point function =>
      (Equal.ofEq (congrArg (termValue (substitute (pi domain body) change) point)
        ((productNativeComparison domain body change point).symm_apply_apply function))).symm.trans
          (productReadingComparison domain body change point
            ((productForward domain body change).app point function)).symm)
    point).trans (carrierUnder (pi domain body) change point)

def productSectionComparison : (substitute (pi domain body) change).native.sections ≃
    (productUnder domain body change).native.sections where
  toFun := (productForward domain body change).mapSection
  invFun := (productBackward domain body change).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (productNativeComparison domain body change point).symm_apply_apply (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (productNativeComparison domain body change point).apply_symm_apply (term.val point)

def productLiteralSectionComparison : (literal (substitute (pi domain body) change)).sections ≃
    (literal (productUnder domain body change)).sections :=
  (sectionDecoder (substitute (pi domain body) change)).trans
    ((productSectionComparison domain body change).trans (sectionDecoder (productUnder domain body change)).symm)

theorem product_literal_future_value (term : (literal (substitute (pi domain body) change)).sections)
    (point : other.Elements)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain (domainUnder domain change).native point).Elements) :
    HEq (((sectionDecoder (productUnder domain body change)
      (productLiteralSectionComparison domain body change term)).val point).val argument)
      (((sectionDecoder (substitute (pi domain body) change) term).val point).val
        ((ContextualSmallFamilyTypeFormerCoherence.futureArgumentChange change domain.native point).obj argument)) :=
  product_future_value domain body change point
    ((sectionDecoder (substitute (pi domain body) change) term).val point) argument

/-- Abstraction commutes with the independently formed product under
parameter substitution, on entire compatible future sections. -/
theorem lambda_substitution (term : body.native.sections) :
    productSectionComparison domain body change
      (ContextualSmallFamilyIdentity.reindexSection change (pi domain body).native
        (ContextualGraphFamilyProducts.nativeLambda domain.native body.native term)) =
      ContextualGraphFamilyProducts.nativeLambda (domainUnder domain change).native (bodyUnder domain body change).native
        (ContextualSmallFamilyIdentity.reindexSection (totalChange domain.native change) body.native term) := by
  apply Subtype.ext
  funext point
  apply Subtype.ext
  funext argument
  apply eq_of_heq
  have mapped := product_future_value domain body change point
    ((ContextualGraphFamilyProducts.nativeLambda domain.native body.native term).val ((elementMap change).obj point)) argument
  have parameters := ContextualSmallFamilyTypeFormerCoherence.futureArgumentChange_embedding change domain.native point argument
  have bodies := congrArg (flatten domain.native).obj parameters
  exact mapped.trans (PowerClassPresheafBaseChange.Cat.dependentValue_heq term.val bodies)

theorem lambda_literal_substitution (term : (literal body).sections) :
    productLiteralSectionComparison domain body change
      (ContextualGraphMaterialSections.pullSection (pi domain body) change
        (ContextualGraphMaterialSections.lambdaEquiv domain body term)) =
      ContextualGraphMaterialSections.lambdaEquiv (domainUnder domain change) (bodyUnder domain body change)
        (ContextualGraphMaterialSections.pullSection body (totalChange domain.native change) term) :=
  congrArg (sectionDecoder (productUnder domain body change)).symm
    (lambda_substitution domain body change (sectionDecoder body term))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialSubstitution
