import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialTypeFormerEquivalence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualSiteLiftFormation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualIdentitySiteLift

/-!
# Complete material family comparisons across the successor site

The independently formed upper dependent types are naturally equivalent
to the lifted lower family, with equality of complete material values.
Their domains and bodies use the actual comprehension comparison. Full
future products and hereditary contextual trees retain every context
arrow; the ordinary discrete identity comparison retains both endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSiteEquivalence

open CategoryTheory ContextualGeneratedUniverse ContextualMaterialEquivalence
open Mettapedia.TypeTheory

universe u
variable {C : Type u} [Category.{u} C]
variable {original : LabelledContext C}

private def raiseEquiv {A : Type (u + 1)} {B : Type u} (comparison : A ≃ B) :
    A ≃ ULift.{u + 1, u} B where
  toFun term := ⟨comparison term⟩
  invFun term := comparison.symm term.down
  left_inv := comparison.symm_apply_apply
  right_inv term := congrArg ULift.up (comparison.apply_symm_apply term.down)

def liftEquivalence {first second : MaterialFamily original} (comparison : Equivalence first second) :
    Equivalence (ContextualSiteLiftMaterial.family first) (ContextualSiteLiftMaterial.family second) where
  fibre point := {
    toFun term := ⟨comparison.fibre ((PresheafSiteLift.elementsDown original.base).obj point) term.down⟩
    invFun term := ⟨(comparison.fibre ((PresheafSiteLift.elementsDown original.base).obj point)).symm term.down⟩
    left_inv term := congrArg ULift.up ((comparison.fibre _).symm_apply_apply term.down)
    right_inv term := congrArg ULift.up ((comparison.fibre _).apply_symm_apply term.down) }
  naturality step term := congrArg ULift.up
    (comparison.naturality ((PresheafSiteLift.elementsDown original.base).map step) term.down)
  value _point term := congrArg HSet.lift (comparison.value _ term.down)

def empty (original : LabelledContext C) :
    Equivalence (MaterialFamily.empty (ContextualSiteLiftMaterial.context original))
      (ContextualSiteLiftMaterial.family (MaterialFamily.empty original)) where
  fibre _ := {
    toFun term := term.down.elim
    invFun term := term.down.down.elim
    left_inv term := term.down.elim
    right_inv term := term.down.down.elim }
  naturality _ term := term.down.elim
  value _ term := term.down.elim

def unit (original : LabelledContext C) :
    Equivalence (MaterialFamily.unit (ContextualSiteLiftMaterial.context original))
      (ContextualSiteLiftMaterial.family (MaterialFamily.unit original)) where
  fibre _ := {
    toFun term := ⟨⟨term.down⟩⟩
    invFun term := ⟨term.down.down⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  naturality _ _ := rfl
  value _ _ := HSet.lift_empty

def reindex {other : LabelledContext C} (domain : MaterialFamily original)
    (change : NatTrans other.base original.base) :
    Equivalence
      ((ContextualSiteLiftMaterial.family domain).reindex
        (other := ContextualSiteLiftMaterial.context other) (PresheafSiteLift.raiseChange change))
      (ContextualSiteLiftMaterial.family (domain.reindex change)) where
  fibre _ := Equiv.refl _
  naturality _ _ := rfl
  value _ _ := rfl

variable (domain : MaterialFamily original) (body : MaterialFamily domain.extension)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

private def piFormed :
    Equivalence (MaterialContextualSiteLiftTypeFormers.Pi.formed domain body arrows)
      (ContextualSiteLiftMaterial.family (domain.pi body arrows)) where
  fibre point := raiseEquiv (MaterialContextualSiteLiftTypeFormers.Pi.semanticEquiv domain body arrows point)
  naturality step term := congrArg ULift.up
    (MaterialContextualSiteLiftTypeFormers.Pi.semantic_restriction domain body arrows step term)
  value point term := (MaterialContextualSiteLiftTypeFormers.Pi.formed_value domain body arrows point term).symm

def pi :
    Equivalence
      ((ContextualSiteLiftMaterial.family domain).pi (ContextualSiteLiftMaterial.body domain body)
        (ContextualSiteLiftMaterial.arrows arrows))
      (ContextualSiteLiftMaterial.family (domain.pi body arrows)) :=
  (ofEquality (MaterialContextualSiteLiftFormation.pi_formed_eq domain body arrows).symm).trans
    (piFormed domain body arrows)

private def sigmaFormed :
    Equivalence (MaterialContextualSiteLiftTypeFormers.Sigma.formed domain body)
      (ContextualSiteLiftMaterial.family (domain.sigma body)) where
  fibre point := raiseEquiv (MaterialContextualSiteLiftTypeFormers.Sigma.semanticEquiv domain body point)
  naturality step term := congrArg ULift.up
    (MaterialContextualSiteLiftTypeFormers.Sigma.semantic_restriction domain body step term)
  value point term := (MaterialContextualSiteLiftTypeFormers.Sigma.formed_value domain body point term).symm

def sigma :
    Equivalence
      ((ContextualSiteLiftMaterial.family domain).sigma (ContextualSiteLiftMaterial.body domain body))
      (ContextualSiteLiftMaterial.family (domain.sigma body)) :=
  (ofEquality (MaterialContextualSiteLiftFormation.sigma_formed_eq domain body).symm).trans (sigmaFormed domain body)

private noncomputable def wFormed :
    Equivalence (MaterialContextualWSiteLift.formed domain body arrows)
      (ContextualSiteLiftMaterial.family (domain.w body arrows)) where
  fibre point := raiseEquiv (MaterialContextualWSiteLift.semanticEquiv domain body arrows point)
  naturality step term := congrArg ULift.up (MaterialContextualWSiteLift.semantic_restriction domain body arrows step term)
  value point term := (MaterialContextualWSiteLift.formed_value domain body arrows point term).symm

noncomputable def w :
    Equivalence
      ((ContextualSiteLiftMaterial.family domain).w (ContextualSiteLiftMaterial.body domain body)
        (ContextualSiteLiftMaterial.arrows arrows))
      (ContextualSiteLiftMaterial.family (domain.w body arrows)) :=
  (ofEquality (MaterialContextualSiteLiftFormation.w_formed_eq domain body arrows).symm).trans (wFormed domain body arrows)

def identity (left right : domain.family.sections) :
    Equivalence
      ((ContextualSiteLiftMaterial.family domain).identity
        (PresheafSiteLift.raiseTerm original.base domain.family left)
        (PresheafSiteLift.raiseTerm original.base domain.family right))
      (ContextualSiteLiftMaterial.family (domain.identity left right)) where
  fibre point := raiseEquiv (MaterialContextualIdentitySiteLift.semanticEquiv domain left right point)
  naturality step term := congrArg ULift.up (MaterialContextualIdentitySiteLift.semantic_restriction domain left right step term)
  value point term := (MaterialContextualIdentitySiteLift.formed_value domain left right point term).symm

def piUnder {other : LabelledContext C} (change : NatTrans other.base original.base) :
    Equivalence ((domain.pi body arrows).reindex change) (domain.piUnder body arrows change) where
  fibre := domain.piComparison body arrows change
  naturality step term := congrArg (fun operation => operation term)
    ((PowerClassPresheafBaseChange.piBaseChange change domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family)).naturality step)
  value := domain.piUnder_value body arrows change

def sigmaUnder {other : LabelledContext C} (change : NatTrans other.base original.base) :
    Equivalence ((domain.sigma body).reindex change) (domain.sigmaUnder body change) where
  fibre _ := Equiv.refl _
  naturality _ _ := rfl
  value := domain.sigmaUnder_value body change

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSiteEquivalence
