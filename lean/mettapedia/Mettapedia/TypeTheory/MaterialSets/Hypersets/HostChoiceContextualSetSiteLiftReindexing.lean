import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftW
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftProducts
import Mettapedia.TypeTheory.ContextualSmallFamilyWiderSubstitution

/-!
# Reindexing the actual upper dependent type formers

An arbitrary parameter map, including a noninjective one, independently
reforms the upper material body and its sums, complete products and W
trees. The resulting comparison with the retained original fibres has
constructed natural inverses and acts on whole compatible sections.
Neither an inverse parameter map nor a choice of sections is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftReindexing

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftFamilies
open HostChoiceContextualSetSiteLiftProducts
open WiderPresheafDependentFunctions

universe u v w h k l
variable {D : Type u} [Category.{u} D] {P : D ⥤ Type v}
variable (parent : NaturalHom P (lowerSets (D := D)))
variable (bodyMap : NaturalHom (HostChoiceContextualHypersetFamilyClosure.comprehension parent)
  (lowerSets (D := D)))
variable {other : UpperSite (D := D) ⥤ Type w}
variable (change : NaturalHom other (ContextualFutureSiteLift.base P))

def reindexed (family : (ContextualFutureSiteLift.base P).Elements ⥤ Type h) : other.Elements ⥤ Type h :=
  PresheafSiteLift.compose (ContextualSmallFamilyUniverse.elementMap change) family

def reindexHom {first : (ContextualFutureSiteLift.base P).Elements ⥤ Type h}
    {second : (ContextualFutureSiteLift.base P).Elements ⥤ Type k} (operation : Hom first second) :
    Hom (reindexed change first) (reindexed change second) where
  app point := operation.app ((ContextualSmallFamilyUniverse.elementMap change).obj point)
  naturality step := operation.naturality ((ContextualSmallFamilyUniverse.elementMap change).map step)

theorem reindex_inverse {first : (ContextualFutureSiteLift.base P).Elements ⥤ Type h}
    {second : (ContextualFutureSiteLift.base P).Elements ⥤ Type k}
    (forward : Hom first second) (backward : Hom second first)
    (inverse : forward.comp backward = Hom.identity first) :
    (reindexHom change forward).comp (reindexHom change backward) = Hom.identity _ := by
  apply Hom.ext
  intro point term
  exact congrArg (fun operation => operation.app ((ContextualSmallFamilyUniverse.elementMap change).obj point) term) inverse

theorem compose_inverse {first : other.Elements ⥤ Type h} {second : other.Elements ⥤ Type k}
    {third : other.Elements ⥤ Type l} (forward : Hom first second) (backward : Hom second first)
    (later : Hom second third) (earlier : Hom third second)
    (firstInverse : forward.comp backward = Hom.identity _) (secondInverse : later.comp earlier = Hom.identity _) :
    (forward.comp later).comp (earlier.comp backward) = Hom.identity _ := by
  apply Hom.ext
  intro point term
  exact (congrArg (backward.app point)
    (congrArg (fun operation => operation.app point (forward.app point term)) secondInverse)).trans
    (congrArg (fun operation => operation.app point term) firstInverse)

def equalityHom {first second : other.Elements ⥤ Type h} (same : first = second) : Hom first second := by
  cases same
  exact Hom.identity _

theorem equality_inverse {first second : other.Elements ⥤ Type h} (same : first = second) :
    (equalityHom same).comp (equalityHom same.symm) = Hom.identity _ := by
  cases same
  exact Hom.identity_comp _

def sectionEquiv {first : other.Elements ⥤ Type h} {second : other.Elements ⥤ Type k}
    (forward : Hom first second) (backward : Hom second first)
    (left : forward.comp backward = Hom.identity _) (right : backward.comp forward = Hom.identity _) :
    first.sections ≃ second.sections where
  toFun := forward.mapSection
  invFun := backward.mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact congrArg (fun operation => operation.app point (term.val point)) left
  right_inv term := by
    apply Subtype.ext
    funext point
    exact congrArg (fun operation => operation.app point (term.val point)) right

namespace Pi

noncomputable abbrev source := reindexed change
  (ContextualFutureSiteLift.retained P (HostChoiceContextualSetSiteLiftProducts.Pi.lower parent bodyMap))

noncomputable abbrev target := HostChoiceContextualHypersetFamilyClosure.freshPi
  (upperParent parent) (upperBodyMap parent bodyMap) change

noncomputable def beckChevalley : Hom
    (ContextualSmallFamilyUniverse.substitutedFamily (HostChoiceContextualSetSiteLiftProducts.Pi.upper parent bodyMap) change)
    (target parent bodyMap change) :=
  Hom.ofNatTrans (HostChoiceContextualHypersetFamilyClosure.piSubstitution (upperParent parent)
    (upperBodyMap parent bodyMap) change)

noncomputable def beckChevalleyInverse : Hom (target parent bodyMap change)
    (ContextualSmallFamilyUniverse.substitutedFamily (HostChoiceContextualSetSiteLiftProducts.Pi.upper parent bodyMap) change) :=
  Hom.ofNatTrans (HostChoiceContextualHypersetFamilyClosure.piSubstitutionInverse (upperParent parent)
    (upperBodyMap parent bodyMap) change)

theorem beckChevalley_left : (beckChevalley parent bodyMap change).comp (beckChevalleyInverse parent bodyMap change) =
    Hom.identity _ := by
  apply Hom.ext
  intro point term
  exact congrArg (fun operation => operation.app point term)
    (HostChoiceContextualHypersetFamilyClosure.piSubstitution_left (upperParent parent)
      (upperBodyMap parent bodyMap) change)

theorem beckChevalley_right : (beckChevalleyInverse parent bodyMap change).comp (beckChevalley parent bodyMap change) =
    Hom.identity _ := by
  apply Hom.ext
  intro point term
  exact congrArg (fun operation => operation.app point term)
    (HostChoiceContextualHypersetFamilyClosure.piSubstitution_right (upperParent parent)
      (upperBodyMap parent bodyMap) change)

noncomputable def forward : Hom (source parent bodyMap change) (target parent bodyMap change) :=
  (reindexHom change (HostChoiceContextualSetSiteLiftProducts.Pi.forward parent bodyMap)).comp
    (beckChevalley parent bodyMap change)

noncomputable def backward : Hom (target parent bodyMap change) (source parent bodyMap change) :=
  (beckChevalleyInverse parent bodyMap change).comp
    (reindexHom change (HostChoiceContextualSetSiteLiftProducts.Pi.backward parent bodyMap))

theorem forward_backward : (forward parent bodyMap change).comp (backward parent bodyMap change) = Hom.identity _ := by
  apply Hom.ext
  intro point term
  have restored := congrArg (fun operation => operation.app point
    ((reindexHom change (HostChoiceContextualSetSiteLiftProducts.Pi.forward parent bodyMap)).app point term))
    (beckChevalley_left parent bodyMap change)
  exact (congrArg ((reindexHom change (HostChoiceContextualSetSiteLiftProducts.Pi.backward parent bodyMap)).app point) restored).trans
    (congrArg (fun operation => operation.app point term)
      (reindex_inverse change _ _ (HostChoiceContextualSetSiteLiftProducts.Pi.forward_backward parent bodyMap)))

theorem backward_forward : (backward parent bodyMap change).comp (forward parent bodyMap change) = Hom.identity _ := by
  apply Hom.ext
  intro point term
  have restored := congrArg (fun operation => operation.app point ((beckChevalleyInverse parent bodyMap change).app point term))
    (reindex_inverse change _ _ (HostChoiceContextualSetSiteLiftProducts.Pi.backward_forward parent bodyMap))
  exact (congrArg ((beckChevalley parent bodyMap change).app point) restored).trans
    (congrArg (fun operation => operation.app point term) (beckChevalley_right parent bodyMap change))

noncomputable def sections : (source parent bodyMap change).sections ≃ (target parent bodyMap change).sections where
  toFun := (forward parent bodyMap change).mapSection
  invFun := (backward parent bodyMap change).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact congrArg (fun operation => operation.app point (term.val point)) (forward_backward parent bodyMap change)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact congrArg (fun operation => operation.app point (term.val point)) (backward_forward parent bodyMap change)

end Pi

theorem sigma_formation :
    HostChoiceContextualHypersetFamilyClosure.freshSigma (upperParent parent) (upperBodyMap parent bodyMap) change =
      ContextualSmallFamilyUniverse.substitutedFamily (Sigma.upper parent bodyMap) change :=
  HostChoiceContextualHypersetFamilyClosure.sigma_substitution (upperParent parent) (upperBodyMap parent bodyMap) change

theorem w_formation :
    ContextualSmallFamilyUniverse.substitutedFamily (HostChoiceContextualSetSiteLiftW.upper parent bodyMap) change =
      HostChoiceContextualHypersetFamilyClosure.freshW (upperParent parent) (upperBodyMap parent bodyMap) change :=
  HostChoiceContextualHypersetFamilyClosure.w_substitution (upperParent parent) (upperBodyMap parent bodyMap) change

namespace Sigma

noncomputable abbrev source := reindexed change
  (ContextualFutureSiteLift.retained P (HostChoiceContextualSetSiteLiftProducts.Sigma.lower parent bodyMap))
noncomputable abbrev target := HostChoiceContextualHypersetFamilyClosure.freshSigma
  (upperParent parent) (upperBodyMap parent bodyMap) change

noncomputable def forward : Hom (source parent bodyMap change) (target parent bodyMap change) :=
  (reindexHom change (HostChoiceContextualSetSiteLiftProducts.Sigma.forward parent bodyMap)).comp
    (equalityHom (sigma_formation parent bodyMap change).symm)

noncomputable def backward : Hom (target parent bodyMap change) (source parent bodyMap change) :=
  (equalityHom (sigma_formation parent bodyMap change)).comp
    (reindexHom change (HostChoiceContextualSetSiteLiftProducts.Sigma.backward parent bodyMap))

theorem forward_backward : (forward parent bodyMap change).comp (backward parent bodyMap change) = Hom.identity _ :=
  compose_inverse _ _ _ _ (reindex_inverse change _ _ (HostChoiceContextualSetSiteLiftProducts.Sigma.forward_backward parent bodyMap))
    (equality_inverse (sigma_formation parent bodyMap change).symm)

theorem backward_forward : (backward parent bodyMap change).comp (forward parent bodyMap change) = Hom.identity _ :=
  compose_inverse _ _ _ _ (equality_inverse (sigma_formation parent bodyMap change))
    (reindex_inverse change _ _ (HostChoiceContextualSetSiteLiftProducts.Sigma.backward_forward parent bodyMap))

noncomputable def sections : (source parent bodyMap change).sections ≃ (target parent bodyMap change).sections :=
  sectionEquiv (forward parent bodyMap change) (backward parent bodyMap change)
    (forward_backward parent bodyMap change) (backward_forward parent bodyMap change)

end Sigma

namespace W

noncomputable abbrev source := reindexed change
  (ContextualFutureSiteLift.retained P (HostChoiceContextualSetSiteLiftW.lower parent bodyMap))
noncomputable abbrev target := HostChoiceContextualHypersetFamilyClosure.freshW
  (upperParent parent) (upperBodyMap parent bodyMap) change

noncomputable def forward : Hom (source parent bodyMap change) (target parent bodyMap change) :=
  (reindexHom change (HostChoiceContextualSetSiteLiftW.forward parent bodyMap)).comp
    (equalityHom (w_formation parent bodyMap change))

noncomputable def backward : Hom (target parent bodyMap change) (source parent bodyMap change) :=
  (equalityHom (w_formation parent bodyMap change).symm).comp
    (reindexHom change (HostChoiceContextualSetSiteLiftW.backward parent bodyMap))

theorem forward_backward : (forward parent bodyMap change).comp (backward parent bodyMap change) = Hom.identity _ :=
  compose_inverse _ _ _ _ (reindex_inverse change _ _ (HostChoiceContextualSetSiteLiftW.forward_backward parent bodyMap))
    (equality_inverse (w_formation parent bodyMap change))

theorem backward_forward : (backward parent bodyMap change).comp (forward parent bodyMap change) = Hom.identity _ :=
  compose_inverse _ _ _ _ (equality_inverse (w_formation parent bodyMap change).symm)
    (reindex_inverse change _ _ (HostChoiceContextualSetSiteLiftW.backward_forward parent bodyMap))

noncomputable def sections : (source parent bodyMap change).sections ≃ (target parent bodyMap change).sections :=
  sectionEquiv (forward parent bodyMap change) (backward parent bodyMap change)
    (forward_backward parent bodyMap change) (backward_forward parent bodyMap change)

theorem fold_substitution {target : (ContextualFutureSiteLift.base P).Elements ⥤ Type h}
    (algebra : ContextualSmallFamilyWiderAlgebra.Algebra (upperDomain parent) (upperBody parent bodyMap) (target := target))
    (point : other.Elements)
    (tree : ContextualSmallFamilyWTypes.WAt (upperDomain parent) (upperBody parent bodyMap)
      ((ContextualSmallFamilyUniverse.elementMap change).obj point)) :
    ContextualSmallFamilyWiderAlgebra.foldValue (upperDomain parent) (upperBody parent bodyMap) algebra
        ((ContextualSmallFamilyUniverse.elementMap change).obj point) tree =
      ContextualSmallFamilyWiderAlgebra.foldValue
        (ContextualSmallFamilyTypeFormerCoherence.domainUnder change (upperDomain parent))
        (ContextualSmallFamilyTypeFormerCoherence.bodyUnder change (upperDomain parent) (upperBody parent bodyMap))
        (ContextualSmallFamilyWiderSubstitution.substitutedAlgebra change (upperDomain parent) (upperBody parent bodyMap) algebra)
        point (ContextualSmallFamilyWSubstitution.wComparison change (upperDomain parent) (upperBody parent bodyMap) point tree) :=
  ContextualSmallFamilyWiderSubstitution.fold_substitution change (upperDomain parent) (upperBody parent bodyMap) algebra point tree

end W

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftReindexing
