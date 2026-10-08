import Mettapedia.TypeTheory.ContextualSmallFamilyWSignature
import Mettapedia.TypeTheory.ContextualWSignatureReindexing

/-!
# Whole compatible W families under natural signature equivalences

The small complete future signature comparison commutes with parameter
substitution. Both directions act on actual trees, and therefore on whole
compatible sections, while retaining the original tree universe bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWSignatureNaturality

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes
open PowerClassPresheafBaseChange

universe u v w z
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable {domain nextDomain : base.Elements ⥤ Type u}
variable {body : domain.Elements ⥤ Type u} {nextBody : nextDomain.Elements ⥤ Type u}
variable (data : WiderPresheafSignatureEquivalence.Signature (shape := domain) (nextShape := nextDomain)
  (position := body) (nextPosition := nextBody))

private theorem dependentValue_heq {A : Sort w} {B : A → Sort z}
    (operation : (point : A) → B point) {first second : A} (same : first = second) :
    HEq (operation first) (operation second) := by
  cases same
  rfl

theorem signature_prefix {first second : base.Elements} (step : first ⟶ second) :
    HEq
      (ContextualWSignatureReindexing.underComparison (ContextualSmallFamilyUniverse.futurePrefix step.1)
        (first := signature domain body first) (second := signature nextDomain nextBody first)
        (ContextualSmallFamilyWSignature.signature data first))
      (ContextualSmallFamilyWSignature.signature data second) := by
  apply ContextualWSignatureReindexing.comparison_heq
    (ContextualSmallFamilyWTypes.signature_prefix domain body step)
    (ContextualSmallFamilyWTypes.signature_prefix nextDomain nextBody step)
  · intro future
    exact dependentValue_heq data.shapes (prefixPoint_eq step future)
  · intro future firstLabel secondLabel labels
    exact dependentValue_heq
      (fun entry : domain.Elements => data.positions entry.1 entry.2)
      (Sigma.ext (β := fun point : base.Elements => domain.obj point)
        (x := ⟨(ContextualSmallFamilyUniverse.futureElement first.1 first.2).obj
          ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future), firstLabel⟩)
        (y := ⟨(ContextualSmallFamilyUniverse.futureElement second.1 second.2).obj future, secondLabel⟩)
        (prefixPoint_eq step future) labels)

theorem equiv_natural {first second : base.Elements} (step : first ⟶ second)
    (tree : WAt domain body first) :
    ContextualSmallFamilyWSignature.equiv data second (wMap domain body step tree) =
      wMap nextDomain nextBody step (ContextualSmallFamilyWSignature.equiv data first tree) := by
  apply Subtype.ext
  apply eq_of_heq
  let contextMap := ContextualSmallFamilyUniverse.futurePrefix step.1
  let root := ContextualSmallFamilyUniverse.root second.1
  let compared := ContextualSmallFamilyWSignature.signature data first
  let moved := ContextualWTypes.restrict (futureDomain domain first) (futureBody domain body first)
    (ContextualSmallFamilyUniverse.rootArrow step.1) tree.val
  have afterCast := ContextualWSignatureReindexing.mapRaw_heq
    (ContextualSmallFamilyWTypes.signature_prefix domain body step).symm
    (ContextualSmallFamilyWTypes.signature_prefix nextDomain nextBody step).symm
    (ContextualSmallFamilyWSignature.signature data second)
    (ContextualWSignatureReindexing.underComparison contextMap
      (first := signature domain body first) (second := signature nextDomain nextBody first) compared)
    (signature_prefix data step).symm _ _ (wMap_raw domain body step tree)
  have afterPull := ContextualWSignatureReindexing.map_pull contextMap
    (first := signature domain body first) (second := signature nextDomain nextBody first) compared root moved
  have afterRestrict := ContextualWSignature.mapRaw_restrict compared
    (ContextualSmallFamilyUniverse.rootArrow step.1) tree.val
  have underPull := ContextualWReindexing.pull_congr (first := contextMap) rfl
    (leftSignature := signature nextDomain nextBody first) rfl rfl _ _ (heq_of_eq afterRestrict)
  exact afterCast.trans ((heq_of_eq afterPull).trans (underPull.trans
    (wMap_raw nextDomain nextBody step (ContextualSmallFamilyWSignature.equiv data first tree)).symm))

noncomputable def forward : WiderPresheafDependentFunctions.Hom (w domain body) (w nextDomain nextBody) where
  app point := ContextualSmallFamilyWSignature.equiv data point
  naturality step tree := (equiv_natural data step tree).symm

noncomputable def backward : WiderPresheafDependentFunctions.Hom (w nextDomain nextBody) (w domain body) where
  app point := (ContextualSmallFamilyWSignature.equiv data point).symm
  naturality {first second} step tree := by
    change WAt nextDomain nextBody first at tree
    apply (ContextualSmallFamilyWSignature.equiv data second).injective
    change ContextualSmallFamilyWSignature.equiv data second
        (wMap domain body step ((ContextualSmallFamilyWSignature.equiv data first).symm tree)) =
      ContextualSmallFamilyWSignature.equiv data second
        ((ContextualSmallFamilyWSignature.equiv data second).symm (wMap nextDomain nextBody step tree))
    rw [equiv_natural, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem forward_backward : (forward data).comp (backward data) =
    WiderPresheafDependentFunctions.Hom.identity _ := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point tree
  exact (ContextualSmallFamilyWSignature.equiv data point).symm_apply_apply tree

theorem backward_forward : (backward data).comp (forward data) =
    WiderPresheafDependentFunctions.Hom.identity _ := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point tree
  exact (ContextualSmallFamilyWSignature.equiv data point).apply_symm_apply tree

noncomputable def sections : (w domain body).sections ≃ (w nextDomain nextBody).sections where
  toFun := (forward data).mapSection
  invFun := (backward data).mapSection
  left_inv tree := by
    apply Subtype.ext
    funext point
    exact (ContextualSmallFamilyWSignature.equiv data point).symm_apply_apply (tree.val point)
  right_inv tree := by
    apply Subtype.ext
    funext point
    exact (ContextualSmallFamilyWSignature.equiv data point).apply_symm_apply (tree.val point)

end Mettapedia.TypeTheory.ContextualSmallFamilyWSignatureNaturality
