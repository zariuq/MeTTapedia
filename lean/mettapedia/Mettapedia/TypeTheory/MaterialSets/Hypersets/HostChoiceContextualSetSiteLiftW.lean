import Mettapedia.TypeTheory.ContextualFutureSiteWCones
import Mettapedia.TypeTheory.ContextualSmallFamilyWSignatureNaturality
import Mettapedia.TypeTheory.ContextualSiteWAlgebra
import Mettapedia.TypeTheory.ContextualSmallFamilyWiderInitiality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftFamilies

/-!
# Independently formed material W families in the successor model

The original material member signature and its argument-dependent body
produce an original-small W family. The larger model independently
produces its own member signature and successor-small W family. Actual
site and member comparisons induce natural inverse tree maps and inverse
maps on whole compatible sections. No W carrier or constructor comparison
is supplied among the construction data.

Member recovery uses the explicitly external Choice of the host set
model. The structural tree maps themselves are indexed recursion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftW

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftFamilies
open WiderPresheafDependentFunctions

universe u v h
variable {D : Type u} [Category.{u} D] {P : D ⥤ Type v}
variable (parent : NaturalHom P (lowerSets (D := D)))
variable (bodyMap : NaturalHom (HostChoiceContextualHypersetFamilyClosure.comprehension parent)
  (lowerSets (D := D)))

noncomputable abbrev lower := HostChoiceContextualHypersetFamilyClosure.wFamily parent bodyMap
noncomputable abbrev upper := HostChoiceContextualHypersetFamilyClosure.wFamily
  (upperParent parent) (upperBodyMap parent bodyMap)

noncomputable def equiv (point : (ContextualFutureSiteLift.base P).Elements) :
    (lower parent bodyMap).obj ((ContextualFutureSiteLift.elementsDown P).obj point) ≃
      (upper parent bodyMap).obj point :=
  (ContextualFutureSiteWCones.equiv (lowerDomain parent) (lowerBody parent bodyMap) point).symm.trans
    (ContextualSmallFamilyWSignature.equiv (signature parent bodyMap) point)

noncomputable def forward : Hom (ContextualFutureSiteLift.retained P (lower parent bodyMap)) (upper parent bodyMap) :=
  (ContextualFutureSiteWCones.forward (lowerDomain parent) (lowerBody parent bodyMap)).comp
    (ContextualSmallFamilyWSignatureNaturality.forward (signature parent bodyMap))

noncomputable def backward : Hom (upper parent bodyMap) (ContextualFutureSiteLift.retained P (lower parent bodyMap)) :=
  (ContextualSmallFamilyWSignatureNaturality.backward (signature parent bodyMap)).comp
    (ContextualFutureSiteWCones.backward (lowerDomain parent) (lowerBody parent bodyMap))

theorem forward_backward : (forward parent bodyMap).comp (backward parent bodyMap) = Hom.identity _ := by
  apply Hom.ext
  intro point tree
  exact (equiv parent bodyMap point).symm_apply_apply tree

theorem backward_forward : (backward parent bodyMap).comp (forward parent bodyMap) = Hom.identity _ := by
  apply Hom.ext
  intro point tree
  exact (equiv parent bodyMap point).apply_symm_apply tree

noncomputable def sections : (lower parent bodyMap).sections ≃ (upper parent bodyMap).sections :=
  (ContextualFutureSiteWCones.sections (lowerDomain parent) (lowerBody parent bodyMap)).trans
    (ContextualSmallFamilyWSignatureNaturality.sections (signature parent bodyMap))

theorem sections_value (term : (lower parent bodyMap).sections)
    (point : (ContextualFutureSiteLift.base P).Elements) :
    (sections parent bodyMap term).val point =
      (forward parent bodyMap).app point (term.val ((ContextualFutureSiteLift.elementsDown P).obj point)) := rfl

theorem upper_initiality (target : (ContextualFutureSiteLift.base P).Elements ⥤ Type h)
    (algebra : ContextualSmallFamilyWiderAlgebra.Algebra (upperDomain parent) (upperBody parent bodyMap)
      (target := target)) :
    ∃! candidate : Hom (upper parent bodyMap) target,
      ∀ point node, candidate.app point
        (ContextualSmallFamilyWiderAlgebra.constructorValue (upperDomain parent) (upperBody parent bodyMap) point node) =
          algebra.app point
            (ContextualSmallFamilyWiderAction.mapValue (upperDomain parent) (upperBody parent bodyMap) candidate point node) :=
  ContextualSmallFamilyWiderInitiality.initiality (upperDomain parent) (upperBody parent bodyMap) algebra

theorem upper_fold_beta (target : (ContextualFutureSiteLift.base P).Elements ⥤ Type h)
    (algebra : ContextualSmallFamilyWiderAlgebra.Algebra (upperDomain parent) (upperBody parent bodyMap)
      (target := target)) (point : (ContextualFutureSiteLift.base P).Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At (upperDomain parent) (upperBody parent bodyMap)
      (upper parent bodyMap) point) :
    ContextualSmallFamilyWiderAlgebra.foldValue (upperDomain parent) (upperBody parent bodyMap) algebra point
        (ContextualSmallFamilyWiderAlgebra.constructorValue (upperDomain parent) (upperBody parent bodyMap) point node) =
      algebra.app point (ContextualSmallFamilyWiderAction.mapValue (upperDomain parent) (upperBody parent bodyMap)
        (ContextualSmallFamilyWiderRecursion.foldMap (upperDomain parent) (upperBody parent bodyMap) algebra) point node) :=
  ContextualSmallFamilyWiderInitiality.fold_beta (upperDomain parent) (upperBody parent bodyMap) algebra point node

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftW
