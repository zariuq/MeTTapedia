import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedContextualFamilies

/-!
# Beck--Chevalley for contextual realized graph receipts

Substitution independently reconstructs the dependent body over the
changed comprehension. Complete future product comparisons are inverse
natural maps, and contextual sums commute with substitution. Conjugating
these genuine comparisons by the receipt decoders preserves whole
compatible sections, including all future arguments and naturality data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedContextualSubstitution

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualAuthoredMaterialFamilies GraphRealizedContextualFamilies

universe u v w
variable {D : Type u} [Category.{u} D]
variable {base : D ⥤ Type (max u v)} {other : D ⥤ Type (max u w)}
variable (domain : Family base) (body : Family domain.extension)
variable (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (change : NaturalHom other base)

section ExplicitNaturalIsomorphisms

variable {E : Type (max u w)} [Category.{u} E]
variable {first middle last : E ⥤ Type u}

def inverseIso (comparison : NaturalEquiv first middle) : NaturalEquiv middle first where
  app point := (comparison.app point).symm
  naturality {firstPoint secondPoint} step value := by
    apply (comparison.app secondPoint).injective
    rw [Equiv.apply_symm_apply, comparison.naturality, Equiv.apply_symm_apply]

/-- Composition preserves the recorded component and naturality data. -/
def composeIso (earlier : NaturalEquiv first middle) (later : NaturalEquiv middle last) :
    NaturalEquiv first last where
  app point := (earlier.app point).trans (later.app point)
  naturality step value := by
    change later.app _ (earlier.app _ (first.map step value)) =
      last.map step (later.app _ (earlier.app _ value))
    rw [earlier.naturality, later.naturality]

def equalityIso (same : first = middle) : NaturalEquiv first middle := by
  cases same
  exact { app := fun point => Equiv.refl (first.obj point), naturality := fun _ _ => rfl }

end ExplicitNaturalIsomorphisms

def bodyUnder : Family (domain.reindex change).extension :=
  body.reindex (totalChange domain.native change)

def productUnder : Family other :=
  (domain.reindex change).pi (bodyUnder domain body change) worlds arrows

def sumUnder : Family other := (domain.reindex change).sigma (bodyUnder domain body change)

theorem bodyUnder_native :
    (domain.reindex change).bodyNative (bodyUnder domain body change) =
      ContextualSmallFamilyTypeFormerCoherence.bodyUnder change domain.native (domain.bodyNative body) :=
  indexedBody_substitution domain.native change body.native

def productNativeComparison (point : other.Elements) :
    ((domain.pi body worlds arrows).reindex change).native.obj point ≃
      (productUnder domain body worlds arrows change).native.obj point := by
  change ContextualSmallFamilyTypeFormers.ProductAt domain.native (domain.bodyNative body)
    ((elementMap change).obj point) ≃
      ContextualSmallFamilyTypeFormers.ProductAt (domain.reindex change).native
        ((domain.reindex change).bodyNative (bodyUnder domain body change)) point
  rw [bodyUnder_native]
  exact ContextualSmallFamilyTypeFormerCoherence.productComparison change domain.native (domain.bodyNative body) point

def productNativeForward : NatTrans ((domain.pi body worlds arrows).reindex change).native
    (productUnder domain body worlds arrows change).native :=
  piDisplayedSubstitution domain.native change body.native

def productNativeInverse : NatTrans (productUnder domain body worlds arrows change).native
    ((domain.pi body worlds arrows).reindex change).native := by
  change NatTrans (ContextualSmallFamilyTypeFormers.pi (domain.reindex change).native
    ((domain.reindex change).bodyNative (bodyUnder domain body change)))
      (substitutedFamily (ContextualSmallFamilyTypeFormers.pi domain.native (domain.bodyNative body)) change)
  rw [bodyUnder_native]
  exact ContextualSmallFamilyTypeFormerCoherence.piSubstitutionInverse change domain.native (domain.bodyNative body)

theorem productNativeForward_value (point : other.Elements)
    (value : ((domain.pi body worlds arrows).reindex change).native.obj point) :
    (productNativeForward domain body worlds arrows change).app point value =
      productNativeComparison domain body worlds arrows change point value := by
  unfold productNativeForward piDisplayedSubstitution productNativeComparison
  generalize indexedBody_substitution domain.native change body.native = same
  cases same
  rfl

theorem productNativeInverse_value (point : other.Elements)
    (value : (productUnder domain body worlds arrows change).native.obj point) :
    (productNativeInverse domain body worlds arrows change).app point value =
      (productNativeComparison domain body worlds arrows change point).symm value := by
  unfold productNativeInverse productNativeComparison
  generalize bodyUnder_native domain body change = same
  cases same
  rfl

def productNativeIso : NaturalEquiv ((domain.pi body worlds arrows).reindex change).native
    (productUnder domain body worlds arrows change).native where
  app := productNativeComparison domain body worlds arrows change
  naturality {first second} step value := by
    have law := congrArg (fun operation => operation value)
      ((productNativeForward domain body worlds arrows change).naturality step)
    change (productNativeForward domain body worlds arrows change).app second
      (((domain.pi body worlds arrows).reindex change).native.map step value) =
      (productUnder domain body worlds arrows change).native.map step
        ((productNativeForward domain body worlds arrows change).app first value) at law
    rw [productNativeForward_value, productNativeForward_value] at law
    exact law

def productBeckChevalley : NaturalEquiv (family ((domain.pi body worlds arrows).reindex change))
    (family (productUnder domain body worlds arrows change)) :=
  composeIso (composeIso (decoder _) (productNativeIso domain body worlds arrows change))
    (inverseIso (decoder _))

theorem sumNative_substitution : (sumUnder domain body change).native =
    ((domain.sigma body).reindex change).native :=
  sigmaDisplayed_substitution domain.native change body.native

def sumBeckChevalley : NaturalEquiv (family ((domain.sigma body).reindex change))
    (family (sumUnder domain body change)) :=
  composeIso (composeIso (decoder _) (equalityIso (sumNative_substitution domain body change).symm))
    (inverseIso (decoder _))

def sectionsOfIso {first second : other.Elements ⥤ Type u}
    (comparison : NaturalEquiv first second) : first.sections ≃ second.sections where
  toFun term := ⟨fun point => comparison.app point (term.val point), by
    intro first second step
    exact (comparison.naturality step (term.val first)).symm.trans
      (congrArg (comparison.app second) (term.property step))⟩
  invFun term := ⟨fun point => (comparison.app point).symm (term.val point), by
    intro first second step
    exact ((inverseIso comparison).naturality step (term.val first)).symm.trans
      (congrArg (comparison.app second).symm (term.property step))⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (comparison.app point).symm_apply_apply _
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (comparison.app point).apply_symm_apply _

def productSectionComparison : (family ((domain.pi body worlds arrows).reindex change)).sections ≃
    (family (productUnder domain body worlds arrows change)).sections :=
  sectionsOfIso (productBeckChevalley domain body worlds arrows change)

def sumSectionComparison : (family ((domain.sigma body).reindex change)).sections ≃
    (family (sumUnder domain body change)).sections :=
  sectionsOfIso (sumBeckChevalley domain body change)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedContextualSubstitution
