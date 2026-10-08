import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalSections

/-!
# Universe raising commutes with actual family substitution and abstraction

The context map and both family interpretations are formed independently.
Raising a substituted family agrees with substitution along the raised
context map. Whole-section inverse maps retain every future argument,
and the actual upper abstraction agrees with the raised lower abstraction
through the constructed product comparison. Literal receipt decoders and
material carriers satisfy the corresponding comparison squares.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftCoherence
open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualGraphMaterialFamilies ContextualGraphMaterialLift ContextualGraphMaterialProducts
universe u
variable {D : Type u} [Category.{u} D] {original : D ⥤ Type u}

theorem substitute_raise (family : Family original) {other : D ⥤ Type u}
    (change : NaturalHom other original) :
    substitute (raise family) (ContextualGraphMaterialLiftIdentity.liftedHom change) = raise (substitute family change) := rfl

def raiseSection (family : Family original) (term : family.native.sections) :
    (native family).sections :=
  ⟨fun point => ULift.up (term.val ((elementsDown original).obj point)),
    fun step => congrArg ULift.up (term.property ((elementsDown original).map step))⟩

variable (domain : Family original) (body : Family (total domain.native))

def bodySection (term : body.native.sections) : (raisedBody domain body).native.sections :=
  ContextualSmallFamilyIdentity.reindexSection (bodyBaseMap domain) (native body) (raiseSection body term)

theorem lambda_raise (term : body.native.sections) :
    ContextualGraphMaterialLiftProducts.sectionComparison domain body
      (ContextualGraphFamilyProducts.nativeLambda (native domain) (raisedBody domain body).native
        (bodySection domain body term)) =
    raiseSection (pi domain body) (ContextualGraphFamilyProducts.nativeLambda domain.native body.native term) := by
  apply Subtype.ext
  funext point
  apply ULift.ext
  apply Subtype.ext
  funext argument
  let upperTerm := ContextualGraphFamilyProducts.nativeLambda (native domain) (raisedBody domain body).native
    (bodySection domain body term)
  change ((ContextualSmallFamilyNativeAdjunction.nativeToSmall domain.native
    (indexedBody domain.native body.native)).app ((elementsDown original).obj point)
      (ContextualGraphMaterialLiftProducts.lowerNative domain body point
        ((ContextualGraphMaterialLiftProducts.decompressed domain body).app point (upperTerm.val point)))).val argument = _
  rw [ContextualSmallFamilyNativeAdjunction.nativeToSmall_value]
  let targetPoint := (elementsUp original).obj
    ((ContextualSmallFamilyTypeFormers.futureArguments domain.native ((elementsDown original).obj point)).obj argument).1
  let arrival := (elementsUp original).map
    (ContextualSmallFamilyTypeFormers.futureRootArrow domain.native ((elementsDown original).obj point) argument)
  change (evaluated (raise domain) (raisedBody domain body) targetPoint
    ((ContextualGraphMaterialLiftProducts.upper domain body).native.map arrival (upperTerm.val point))
    (ULift.up argument.2)).down = _
  have natural := upperTerm.property arrival
  refine (congrArg (fun function => (evaluated (raise domain) (raisedBody domain body)
    targetPoint function (ULift.up argument.2)).down) natural).trans ?_
  exact congrArg ULift.down (ContextualGraphMaterialSections.native_lambda_evaluation
    (raise domain) (raisedBody domain body) (bodySection domain body term)
    targetPoint (ULift.up argument.2))


def lowerSection (family : Family original) (term : (native family).sections) :
    family.native.sections :=
  ⟨fun point => (term.val ((elementsUp original).obj point)).down,
    fun step => congrArg ULift.down (term.property ((elementsUp original).map step))⟩

def sections (family : Family original) : family.native.sections ≃ (native family).sections where
  toFun := raiseSection family
  invFun := lowerSection family
  left_inv term := by apply Subtype.ext; funext point; rfl
  right_inv term := by apply Subtype.ext; funext point; rfl

def lowerBodySection (term : (raisedBody domain body).native.sections) : body.native.sections :=
  ⟨fun point => (term.val ((ContextualGraphMaterialLiftIdentity.upperComprehensionFunctor domain).obj point)).down,
    fun step => congrArg ULift.down
      (term.property ((ContextualGraphMaterialLiftIdentity.upperComprehensionFunctor domain).map step))⟩

def bodySections : body.native.sections ≃ (raisedBody domain body).native.sections where
  toFun := bodySection domain body
  invFun := lowerBodySection domain body
  left_inv term := by apply Subtype.ext; funext point; rfl
  right_inv term := by apply Subtype.ext; funext point; rfl

def literalRaise (family : Family original) : (literal family).sections ≃ (literal (raise family)).sections :=
  (sectionDecoder family).trans ((sections family).trans (sectionDecoder (raise family)).symm)

def literalBodyRaise : (literal body).sections ≃ (literal (raisedBody domain body)).sections :=
  (sectionDecoder body).trans ((bodySections domain body).trans (sectionDecoder (raisedBody domain body)).symm)

theorem lambda_literal_raise (term : (literal body).sections) :
    ContextualGraphMaterialLiftProducts.literalSectionComparison domain body
      (ContextualGraphMaterialSections.lambdaEquiv (raise domain) (raisedBody domain body)
        (literalBodyRaise domain body term)) =
      literalRaise (pi domain body) (ContextualGraphMaterialSections.lambdaEquiv domain body term) := by
  apply (sectionDecoder (raise (pi domain body))).injective
  exact lambda_raise domain body (sectionDecoder body term)

theorem raise_section_substitution (family : Family original) {other : D ⥤ Type u}
    (change : NaturalHom other original) (term : family.native.sections) :
    raiseSection (substitute family change)
        (ContextualSmallFamilyIdentity.reindexSection change family.native term) =
      ContextualSmallFamilyIdentity.reindexSection (ContextualGraphMaterialLiftIdentity.liftedHom change) (native family)
        (raiseSection family term) := rfl

theorem literal_raise_substitution (family : Family original) {other : D ⥤ Type u}
    (change : NaturalHom other original) (term : (literal family).sections) :
    ContextualGraphMaterialSections.pullSection (raise family) (ContextualGraphMaterialLiftIdentity.liftedHom change) (literalRaise family term) =
      literalRaise (substitute family change) (ContextualGraphMaterialSections.pullSection family change term) := by
  apply (sectionDecoder (raise (substitute family change))).injective
  exact (ContextualGraphMaterialSections.pullSection_decode (raise family) (ContextualGraphMaterialLiftIdentity.liftedHom change)
    (literalRaise family term)).trans
      ((raise_section_substitution family change (sectionDecoder family term)).symm.trans
        (congrArg (raiseSection (substitute family change))
          (ContextualGraphMaterialSections.pullSection_decode family change term).symm))

open ContextualGraphDiagrams ContextualRealizedGraphs

/-- Substitution and raising also compare the freshly attached material
carriers, without restricting their members to represented lower values. -/
def substitutedCarrierComparison (family : Family original) {other : D ⥤ Type u}
    (change : NaturalHom other original) (point : (base other).Elements) :
    Equal ((carrier (substitute (raise family) (ContextualGraphMaterialLiftIdentity.liftedHom change))).app point.1 point.2)
      (ContextualGraphUniverseLift.value
        ((carrier family).app point.1.down (change.app point.1.down point.2.down))) :=
  (ContextualGraphMaterialLift.carrierComparison (substitute family change) point.1 point.2.down).symm.trans
    (ContextualGraphUniverseLift.preserve
      (ContextualGraphMaterialSubstitution.carrierUnder family change ((elementsDown other).obj point)))

namespace Controls

open ContextualGraphMaterialObservedControls

def upperAbstract (term : bodyFamily.native.sections) :
    (ContextualGraphMaterialLiftProducts.upper domainFamily bodyFamily).native.sections :=
  ContextualGraphFamilyProducts.nativeLambda (native domainFamily) (raisedBody domainFamily bodyFamily).native
    (bodySection domainFamily bodyFamily term)

theorem identity_actual_upper_abstraction (stage : Nat) :
    (upperAbstract identityBody).val (ContextualGraphMaterialLiftControls.point stage) =
      (ContextualGraphMaterialLiftControls.upperIdentity stage).val := by
  apply (ContextualGraphMaterialLiftProducts.nativeEquiv domainFamily bodyFamily
    (ContextualGraphMaterialLiftControls.point stage)).injective
  have mapped := congrArg (fun whole => whole.val (ContextualGraphMaterialLiftControls.point stage))
    (lambda_raise domainFamily bodyFamily identityBody)
  exact mapped.trans
    ((ContextualGraphMaterialLiftProducts.nativeEquiv domainFamily bodyFamily
      (ContextualGraphMaterialLiftControls.point stage)).apply_symm_apply
        (ULift.up (identityFunction.val (parameter stage)))).symm

theorem identity_abstraction_qualifies_every_stage (stage : Nat) :
    ∃ function : (ContextualGraphMaterialLiftFunctional.upper domainFamily bodyFamily).native.obj
        (ContextualGraphMaterialLiftControls.point stage),
      function.val = (upperAbstract identityBody).val (ContextualGraphMaterialLiftControls.point stage) :=
  ⟨ContextualGraphMaterialLiftControls.upperIdentity stage, (identity_actual_upper_abstraction stage).symm⟩

theorem sensitive_actual_upper_abstraction :
    (upperAbstract sensitiveBody).val (ContextualGraphMaterialLiftControls.point 3) =
      ContextualGraphMaterialLiftControls.upperSensitive := by
  apply (ContextualGraphMaterialLiftProducts.nativeEquiv domainFamily bodyFamily
    (ContextualGraphMaterialLiftControls.point 3)).injective
  have mapped := congrArg (fun whole => whole.val (ContextualGraphMaterialLiftControls.point 3))
    (lambda_raise domainFamily bodyFamily sensitiveBody)
  exact mapped.trans
    ((ContextualGraphMaterialLiftProducts.nativeEquiv domainFamily bodyFamily
      (ContextualGraphMaterialLiftControls.point 3)).apply_symm_apply
        (ULift.up (sensitiveFunction.val (parameter 3)))).symm

theorem incompatible_upper_abstraction_still_excluded :
    ¬ ∃ function : (ContextualGraphMaterialLiftFunctional.upper domainFamily bodyFamily).native.obj
        (ContextualGraphMaterialLiftControls.point 3),
      function.val = (upperAbstract sensitiveBody).val (ContextualGraphMaterialLiftControls.point 3) := by
  rintro ⟨function, same⟩
  exact ContextualGraphMaterialLiftControls.incompatible_still_excluded
    ⟨function, same.trans sensitive_actual_upper_abstraction⟩

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftCoherence
