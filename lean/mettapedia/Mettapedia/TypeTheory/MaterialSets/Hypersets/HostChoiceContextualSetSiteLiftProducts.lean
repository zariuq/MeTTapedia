import Mettapedia.TypeTheory.ContextualFutureSiteProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftFamilies

/-!
# Actual dependent sums and complete future products across a model lift

The upper parent and argument-dependent body are formed in the larger
set model. Their native member signatures are compared to the independently
formed lower signatures through the actual site equivalence. Both sum
coordinates and every future product application retain their decoded
material values. The product and sum families have natural inverse maps,
including inverse maps on whole compatible sections.

The upper member decoder inherits the explicitly external recovery choice
of the model lift. The full-future comparisons do not select functions
from pointwise existence and do not classify arbitrary upper bodies as
lower bodies.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftProducts

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftFamilies
open WiderPresheafDependentFunctions

universe u v h
variable {D : Type u} [Category.{u} D] {P : D ⥤ Type v}
variable (parent : NaturalHom P (lowerSets (D := D)))
variable (bodyMap : NaturalHom (HostChoiceContextualHypersetFamilyClosure.comprehension parent)
  (lowerSets (D := D)))

namespace Pi

noncomputable abbrev lower := HostChoiceContextualHypersetFamilyClosure.piFamily parent bodyMap
noncomputable abbrev upper := HostChoiceContextualHypersetFamilyClosure.piFamily
  (upperParent parent) (upperBodyMap parent bodyMap)

noncomputable def equiv (point : (ContextualFutureSiteLift.base P).Elements) :
    (lower parent bodyMap).obj ((ContextualFutureSiteLift.elementsDown P).obj point) ≃
      (upper parent bodyMap).obj point :=
  (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv (lowerDomain parent)
    (lowerBody parent bodyMap) ((ContextualFutureSiteLift.elementsDown P).obj point)).symm.trans
    ((ContextualFutureSiteProducts.Pi.nativeEquiv (lowerDomain parent) (lowerBody parent bodyMap) point).symm.trans
      ((WiderPresheafSignatureEquivalence.piEquiv (signature parent bodyMap) point).trans
        (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv (upperDomain parent)
          (upperBody parent bodyMap) point)))

noncomputable def forward : Hom (ContextualFutureSiteLift.retained P (lower parent bodyMap))
    (upper parent bodyMap) :=
  ((ContextualFutureSiteLift.retainedHom P
      (ContextualSmallFamilyNativeAdjunction.smallToNative (lowerDomain parent) (lowerBody parent bodyMap))).comp
    (ContextualFutureSiteProducts.Pi.inverse (lowerDomain parent) (lowerBody parent bodyMap))).comp
      ((WiderPresheafSignatureEquivalence.piForward (signature parent bodyMap)).comp
        (ContextualSmallFamilyNativeAdjunction.nativeToSmall (upperDomain parent) (upperBody parent bodyMap)))

noncomputable def backward : Hom (upper parent bodyMap)
    (ContextualFutureSiteLift.retained P (lower parent bodyMap)) :=
  ((ContextualSmallFamilyNativeAdjunction.smallToNative (upperDomain parent) (upperBody parent bodyMap)).comp
    (WiderPresheafSignatureEquivalence.piBackward (signature parent bodyMap))).comp
      ((ContextualFutureSiteProducts.Pi.comparison (lowerDomain parent) (lowerBody parent bodyMap)).comp
        (ContextualFutureSiteLift.retainedHom P
          (ContextualSmallFamilyNativeAdjunction.nativeToSmall (lowerDomain parent) (lowerBody parent bodyMap))))

theorem forward_value (point : (ContextualFutureSiteLift.base P).Elements)
    (term : (lower parent bodyMap).obj ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    (forward parent bodyMap).app point term = equiv parent bodyMap point term := rfl

theorem backward_value (point : (ContextualFutureSiteLift.base P).Elements)
    (term : (upper parent bodyMap).obj point) :
    (backward parent bodyMap).app point term = (equiv parent bodyMap point).symm term := rfl

theorem forward_backward : (forward parent bodyMap).comp (backward parent bodyMap) = Hom.identity _ := by
  apply Hom.ext
  intro point term
  exact (equiv parent bodyMap point).symm_apply_apply term

theorem backward_forward : (backward parent bodyMap).comp (forward parent bodyMap) = Hom.identity _ := by
  apply Hom.ext
  intro point term
  exact (equiv parent bodyMap point).apply_symm_apply term

noncomputable def sections : (lower parent bodyMap).sections ≃ (upper parent bodyMap).sections :=
  (ContextualFutureSiteLift.retainedSections P (lower parent bodyMap)).trans {
    toFun := (forward parent bodyMap).mapSection
    invFun := (backward parent bodyMap).mapSection
    left_inv term := by
      apply Subtype.ext
      funext point
      exact (equiv parent bodyMap point).symm_apply_apply (term.val point)
    right_inv term := by
      apply Subtype.ext
      funext point
      exact (equiv parent bodyMap point).apply_symm_apply (term.val point) }

noncomputable def nativeForward : Hom
    (ContextualFutureSiteLift.retained P
      (dependentFunctions (lowerDomain parent) (lowerBody parent bodyMap)))
    (dependentFunctions (upperDomain parent) (upperBody parent bodyMap)) :=
  (ContextualFutureSiteProducts.Pi.inverse (lowerDomain parent) (lowerBody parent bodyMap)).comp
    (WiderPresheafSignatureEquivalence.piForward (signature parent bodyMap))

theorem native_evaluation (point next : (ContextualFutureSiteLift.base P).Elements)
    (term : DependentSection (lowerDomain parent) (lowerBody parent bodyMap)
      ((ContextualFutureSiteLift.elementsDown P).obj point))
    (arrow : point ⟶ next) (argument : (raisedDomain parent).obj next) :
    ((nativeForward parent bodyMap).app point term).app next arrow (domainEquiv parent next argument) =
      bodyEquiv parent bodyMap ⟨next, argument⟩
        (ULift.up (term.app ((ContextualFutureSiteLift.elementsDown P).obj next)
          ((ContextualFutureSiteLift.elementsDown P).map arrow) argument.down)) :=
  WiderPresheafSignatureEquivalence.piApply_on_shape (signature parent bodyMap)
    (ContextualFutureSiteProducts.Pi.raise (lowerDomain parent) (lowerBody parent bodyMap) point term)
    next arrow argument

theorem native_material_evaluation (point next : (ContextualFutureSiteLift.base P).Elements)
    (term : DependentSection (lowerDomain parent) (lowerBody parent bodyMap)
      ((ContextualFutureSiteLift.elementsDown P).obj point))
    (arrow : point ⟶ next) (argument : (raisedDomain parent).obj next) :
    embedding.app next.1
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder parent bodyMap
        ⟨(ContextualFutureSiteLift.elementsDown P).obj next, argument.down⟩
        (term.app ((ContextualFutureSiteLift.elementsDown P).obj next)
          ((ContextualFutureSiteLift.elementsDown P).map arrow) argument.down)).val =
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder (upperParent parent) (upperBodyMap parent bodyMap)
        ⟨next, domainEquiv parent next argument⟩
        (((nativeForward parent bodyMap).app point term).app next arrow
          (domainEquiv parent next argument))).val := by
  rw [native_evaluation]
  exact bodyEquiv_value parent bodyMap ⟨next, argument⟩ _

theorem small_native_square :
    (forward parent bodyMap).comp
        (ContextualSmallFamilyNativeAdjunction.smallToNative (upperDomain parent) (upperBody parent bodyMap)) =
      (ContextualFutureSiteLift.retainedHom P
        (ContextualSmallFamilyNativeAdjunction.smallToNative (lowerDomain parent) (lowerBody parent bodyMap))).comp
          (nativeForward parent bodyMap) := by
  apply Hom.ext
  intro point term
  exact (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv (upperDomain parent)
    (upperBody parent bodyMap) point).symm_apply_apply _

theorem material_future_application (point next : (ContextualFutureSiteLift.base P).Elements)
    (term : (lower parent bodyMap).obj ((ContextualFutureSiteLift.elementsDown P).obj point))
    (arrow : point ⟶ next) (argument : (raisedDomain parent).obj next) :
    embedding.app next.1
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder parent bodyMap
        ⟨(ContextualFutureSiteLift.elementsDown P).obj next, argument.down⟩
        (((ContextualSmallFamilyNativeAdjunction.smallToNative (lowerDomain parent) (lowerBody parent bodyMap)).app
          ((ContextualFutureSiteLift.elementsDown P).obj point) term).app
            ((ContextualFutureSiteLift.elementsDown P).obj next)
            ((ContextualFutureSiteLift.elementsDown P).map arrow) argument.down)).val =
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder (upperParent parent) (upperBodyMap parent bodyMap)
        ⟨next, domainEquiv parent next argument⟩
        (((ContextualSmallFamilyNativeAdjunction.smallToNative (upperDomain parent) (upperBody parent bodyMap)).app point
          ((forward parent bodyMap).app point term)).app next arrow (domainEquiv parent next argument))).val := by
  have expanded :
      (ContextualSmallFamilyNativeAdjunction.smallToNative (upperDomain parent) (upperBody parent bodyMap)).app point
          ((forward parent bodyMap).app point term) =
        (nativeForward parent bodyMap).app point
          ((ContextualSmallFamilyNativeAdjunction.smallToNative (lowerDomain parent) (lowerBody parent bodyMap)).app
            ((ContextualFutureSiteLift.elementsDown P).obj point) term) :=
    congrArg (fun operation => operation.app point term) (small_native_square parent bodyMap)
  exact (native_material_evaluation parent bodyMap point next _ arrow argument).trans
    (congrArg (fun function : DependentSection (upperDomain parent) (upperBody parent bodyMap) point =>
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder (upperParent parent) (upperBodyMap parent bodyMap)
        ⟨next, domainEquiv parent next argument⟩ (function.app next arrow (domainEquiv parent next argument))).val)
      expanded).symm

private theorem native_current {E : Type u} [Category.{u} E] {parameters : E ⥤ Type v}
    (domain : parameters.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
    (point : parameters.Elements) (term : (ContextualSmallFamilyTypeFormers.pi domain body).obj point)
    (argument : domain.obj point) :
    ((ContextualSmallFamilyNativeAdjunction.smallToNative domain body).app point term).app point (𝟙 point) argument =
      ContextualSmallFamilyTypeFormers.evaluateValue domain body point term argument := by
  change ContextualSmallFamilyTypeFormers.evaluateValue domain body point
    ((ContextualSmallFamilyTypeFormers.pi domain body).map (𝟙 point) term) argument = _
  rw [Functor.map_id_apply]

theorem material_current_application (point : (ContextualFutureSiteLift.base P).Elements)
    (term : (lower parent bodyMap).obj ((ContextualFutureSiteLift.elementsDown P).obj point))
    (argument : (lowerDomain parent).obj ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    embedding.app point.1
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder parent bodyMap
        ⟨(ContextualFutureSiteLift.elementsDown P).obj point, argument⟩
        (ContextualSmallFamilyTypeFormers.evaluateValue (lowerDomain parent) (lowerBody parent bodyMap)
          ((ContextualFutureSiteLift.elementsDown P).obj point) term argument)).val =
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder (upperParent parent) (upperBodyMap parent bodyMap)
        ⟨point, domainEquiv parent point (ULift.up argument)⟩
        (ContextualSmallFamilyTypeFormers.evaluateValue (upperDomain parent) (upperBody parent bodyMap) point
          ((forward parent bodyMap).app point term) (domainEquiv parent point (ULift.up argument)))).val := by
  have result := material_future_application parent bodyMap point point term (𝟙 point) (ULift.up argument)
  change embedding.app point.1 (HostChoiceContextualHypersetFamilyClosure.bodyDecoder parent bodyMap
      ⟨(ContextualFutureSiteLift.elementsDown P).obj point, argument⟩
      (((ContextualSmallFamilyNativeAdjunction.smallToNative (lowerDomain parent) (lowerBody parent bodyMap)).app
        ((ContextualFutureSiteLift.elementsDown P).obj point) term).app
          ((ContextualFutureSiteLift.elementsDown P).obj point) (𝟙 _) argument)).val = _ at result
  have oldValue := native_current (lowerDomain parent) (lowerBody parent bodyMap)
    ((ContextualFutureSiteLift.elementsDown P).obj point) term argument
  have newValue := native_current (upperDomain parent) (upperBody parent bodyMap) point
    ((forward parent bodyMap).app point term) (domainEquiv parent point (ULift.up argument))
  exact (congrArg (fun code => embedding.app point.1
    (HostChoiceContextualHypersetFamilyClosure.bodyDecoder parent bodyMap
      ⟨(ContextualFutureSiteLift.elementsDown P).obj point, argument⟩ code).val) oldValue).symm.trans
        (result.trans (congrArg (fun code =>
          (HostChoiceContextualHypersetFamilyClosure.bodyDecoder (upperParent parent) (upperBodyMap parent bodyMap)
            ⟨point, domainEquiv parent point (ULift.up argument)⟩ code).val) newValue))

theorem upper_beta (consumer : (ContextualFutureSiteLift.base P).Elements ⥤ Type h)
    (operation : Hom (over (upperDomain parent) consumer) (upperBody parent bodyMap)) :
    ContextualSmallFamilyNativeAdjunction.smallUncurry (upperDomain parent) (upperBody parent bodyMap)
      (ContextualSmallFamilyNativeAdjunction.smallCurry (upperDomain parent) (upperBody parent bodyMap) operation) = operation :=
  ContextualSmallFamilyNativeAdjunction.small_uncurry_curry (upperDomain parent) (upperBody parent bodyMap) operation

theorem upper_eta (consumer : (ContextualFutureSiteLift.base P).Elements ⥤ Type h)
    (operation : Hom consumer (upper parent bodyMap)) :
    ContextualSmallFamilyNativeAdjunction.smallCurry (upperDomain parent) (upperBody parent bodyMap)
      (ContextualSmallFamilyNativeAdjunction.smallUncurry (upperDomain parent) (upperBody parent bodyMap) operation) = operation :=
  ContextualSmallFamilyNativeAdjunction.small_curry_uncurry (upperDomain parent) (upperBody parent bodyMap) operation

end Pi

namespace Sigma

noncomputable abbrev lower := HostChoiceContextualHypersetFamilyClosure.sigmaFamily parent bodyMap
noncomputable abbrev upper := HostChoiceContextualHypersetFamilyClosure.sigmaFamily
  (upperParent parent) (upperBodyMap parent bodyMap)

noncomputable def equiv (point : (ContextualFutureSiteLift.base P).Elements) :
    (lower parent bodyMap).obj ((ContextualFutureSiteLift.elementsDown P).obj point) ≃
      (upper parent bodyMap).obj point :=
  (ContextualFutureSiteProducts.Sigma.equiv (lowerDomain parent) (lowerBody parent bodyMap) point).symm.trans
    (WiderPresheafSignatureEquivalence.sigmaEquiv (signature parent bodyMap) point)

noncomputable def forward : Hom (ContextualFutureSiteLift.retained P (lower parent bodyMap))
    (upper parent bodyMap) :=
  (ContextualFutureSiteProducts.Sigma.inverse (lowerDomain parent) (lowerBody parent bodyMap)).comp
    (WiderPresheafSignatureEquivalence.sigmaForward (signature parent bodyMap))

noncomputable def backward : Hom (upper parent bodyMap)
    (ContextualFutureSiteLift.retained P (lower parent bodyMap)) :=
  (WiderPresheafSignatureEquivalence.sigmaBackward (signature parent bodyMap)).comp
    (ContextualFutureSiteProducts.Sigma.comparison (lowerDomain parent) (lowerBody parent bodyMap))

theorem forward_backward : (forward parent bodyMap).comp (backward parent bodyMap) = Hom.identity _ := by
  apply Hom.ext
  intro point term
  exact (equiv parent bodyMap point).symm_apply_apply term

theorem backward_forward : (backward parent bodyMap).comp (forward parent bodyMap) = Hom.identity _ := by
  apply Hom.ext
  intro point term
  exact (equiv parent bodyMap point).apply_symm_apply term

noncomputable def sections : (lower parent bodyMap).sections ≃ (upper parent bodyMap).sections :=
  (ContextualFutureSiteLift.retainedSections P (lower parent bodyMap)).trans {
    toFun := (forward parent bodyMap).mapSection
    invFun := (backward parent bodyMap).mapSection
    left_inv term := by
      apply Subtype.ext
      funext point
      exact (equiv parent bodyMap point).symm_apply_apply (term.val point)
    right_inv term := by
      apply Subtype.ext
      funext point
      exact (equiv parent bodyMap point).apply_symm_apply (term.val point) }

theorem first_member_value (point : (ContextualFutureSiteLift.base P).Elements)
    (term : (lower parent bodyMap).obj ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    embedding.app point.1
      (HostChoiceContextualHypersetModel.memberDecoder
        ⟨point.1.down, parent.app point.1.down point.2⟩ term.1).val =
      (HostChoiceContextualHypersetModel.memberDecoder
        ⟨point.1, (upperParent parent).app point.1 point.2⟩
        ((forward parent bodyMap).app point term).1).val :=
  HostChoiceContextualSetSiteLiftCoherence.code_value
    ⟨point.1, (raisedParent parent).app point.1 point.2⟩ term.1

theorem second_member_value (point : (ContextualFutureSiteLift.base P).Elements)
    (term : (lower parent bodyMap).obj ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    embedding.app point.1
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder parent bodyMap
        ⟨(ContextualFutureSiteLift.elementsDown P).obj point, term.1⟩ term.2).val =
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder (upperParent parent) (upperBodyMap parent bodyMap)
        ⟨point, ((forward parent bodyMap).app point term).1⟩
        ((forward parent bodyMap).app point term).2).val :=
  bodyEquiv_value parent bodyMap ⟨point, ULift.up term.1⟩ (ULift.up term.2)

end Sigma

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftProducts
