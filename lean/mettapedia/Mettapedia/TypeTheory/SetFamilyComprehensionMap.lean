import Mettapedia.TypeTheory.DisplayedFamilyObservation
import Mettapedia.GSLT.Core.ContextualTypeCategory

/-!
# Fibre maps and comprehension in the set-families CwF

A map between two type families over the same context induces a map between
their comprehension contexts by acting in each fibre.  For the set-families
CwF this is the dependent-sum map

```text
(γ, a) ↦ (γ, fγ(a)).
```

The induced comprehension map is bijective exactly when every fibre map is
bijective.  A family of fibre equivalences therefore gives an isomorphism in
the category of types over the context.

The value projection from value-and-route terms fails this criterion, while
the joint value-and-route observation satisfies it.  Thus naturality of an
observation alone does not imply preservation of CwF comprehension.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SetFamilyComprehensionMap

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.CwfTermJointObservation

universe u

variable {Context : Type u}
variable {sourceFamily targetFamily : Context → Type u}

/-- The context-extension map induced by a fibrewise function. -/
def totalMap
    (fibreMap : ∀ context, sourceFamily context → targetFamily context) :
    (Sigma sourceFamily) → Sigma targetFamily
  | ⟨context, value⟩ => ⟨context, fibreMap context value⟩

/-- Injectivity of the total comprehension map is exactly fibrewise
injectivity. -/
theorem totalMap_injective_iff
    (fibreMap : ∀ context, sourceFamily context → targetFamily context) :
    Function.Injective (totalMap fibreMap) ↔
      ∀ context, Function.Injective (fibreMap context) := by
  constructor
  · intro totalInjective context left right sameImage
    have sameTotal :
        totalMap fibreMap ⟨context, left⟩ =
          totalMap fibreMap ⟨context, right⟩ := by
      exact Sigma.ext rfl (heq_of_eq sameImage)
    have sameSource := totalInjective sameTotal
    exact eq_of_heq (Sigma.mk.inj_iff.mp sameSource).2
  · intro fibreInjective left right sameImage
    rcases left with ⟨leftContext, leftValue⟩
    rcases right with ⟨rightContext, rightValue⟩
    have sameContext : leftContext = rightContext :=
      congrArg Sigma.fst sameImage
    cases sameContext
    have sameFibreImage :
        fibreMap leftContext leftValue =
          fibreMap leftContext rightValue :=
      eq_of_heq (Sigma.mk.inj_iff.mp sameImage).2
    have sameValue := fibreInjective leftContext sameFibreImage
    cases sameValue
    rfl

/-- Surjectivity of the total comprehension map is exactly fibrewise
surjectivity. -/
theorem totalMap_surjective_iff
    (fibreMap : ∀ context, sourceFamily context → targetFamily context) :
    Function.Surjective (totalMap fibreMap) ↔
      ∀ context, Function.Surjective (fibreMap context) := by
  constructor
  · intro totalSurjective context target
    rcases totalSurjective ⟨context, target⟩ with
      ⟨⟨sourceContext, source⟩, sameTotal⟩
    have sameContext : sourceContext = context :=
      congrArg Sigma.fst sameTotal
    cases sameContext
    refine ⟨source, ?_⟩
    exact eq_of_heq (Sigma.mk.inj_iff.mp sameTotal).2
  · intro fibreSurjective
    rintro ⟨context, target⟩
    rcases fibreSurjective context target with ⟨source, sameFibre⟩
    refine ⟨⟨context, source⟩, ?_⟩
    exact Sigma.ext rfl (heq_of_eq sameFibre)

/-- The exact comprehension-preservation criterion in the set-families
model. -/
theorem totalMap_bijective_iff
    (fibreMap : ∀ context, sourceFamily context → targetFamily context) :
    Function.Bijective (totalMap fibreMap) ↔
      ∀ context, Function.Bijective (fibreMap context) := by
  constructor
  · intro totalBijective
    exact fun context =>
      ⟨(totalMap_injective_iff fibreMap).1 totalBijective.1 context,
        (totalMap_surjective_iff fibreMap).1 totalBijective.2 context⟩
  · intro fibreBijective
    exact ⟨(totalMap_injective_iff fibreMap).2
        (fun context => (fibreBijective context).1),
      (totalMap_surjective_iff fibreMap).2
        (fun context => (fibreBijective context).2)⟩

/-- The induced comprehension map as a display map over the unchanged base
context. -/
def displayMap
    (fibreMap : ∀ context, sourceFamily context → targetFamily context) :
    (⟨sourceFamily⟩ : TypeOver (familiesCwf.{u}) Context) ⟶
      (⟨targetFamily⟩ : TypeOver (familiesCwf.{u}) Context) where
  substitution := totalMap fibreMap
  over := rfl

/-- Fibrewise equivalence supplies an actual isomorphism of types over the
context, including their selected comprehension contexts. -/
def displayIso
    (fibreEquivalence :
      ∀ context, sourceFamily context ≃ targetFamily context) :
    (⟨sourceFamily⟩ : TypeOver (familiesCwf.{u}) Context) ≅
      (⟨targetFamily⟩ : TypeOver (familiesCwf.{u}) Context) where
  hom := displayMap (fun context => fibreEquivalence context)
  inv := displayMap (fun context => (fibreEquivalence context).symm)
  hom_inv_id := by
    apply TypeOver.Hom.ext
    funext point
    rcases point with ⟨context, value⟩
    exact Sigma.ext rfl
      (heq_of_eq ((fibreEquivalence context).symm_apply_apply value))
  inv_hom_id := by
    apply TypeOver.Hom.ext
    funext point
    rcases point with ⟨context, value⟩
    exact Sigma.ext rfl
      (heq_of_eq ((fibreEquivalence context).apply_symm_apply value))

/-! ## Value-only and joint-view controls -/

namespace Canary

abbrev UnitPairFamily : PUnit → Type :=
  fun _ => Bool × Bool

abbrev UnitBoolFamily : PUnit → Type :=
  fun _ => Bool

abbrev UnitJointFamily : PUnit → Type :=
  fun _ => Bool × Bool

def valueFibreMap : ∀ context, UnitPairFamily context → UnitBoolFamily context :=
  fun _ => Prod.fst

def jointFibreMap :
    ∀ context, UnitPairFamily context → UnitJointFamily context :=
  fun _ pair => (pair.1, pair.2)

def duplicatedValueFibreMap :
    ∀ context, UnitPairFamily context → UnitJointFamily context :=
  fun _ pair => (pair.1, pair.1)

/-- The value projection loses the route and therefore does not preserve the
comprehension context up to bijection. -/
theorem value_totalMap_not_bijective :
    ¬ Function.Bijective (totalMap valueFibreMap) := by
  intro totalBijective
  have fibreInjective :=
    ((totalMap_bijective_iff valueFibreMap).1 totalBijective PUnit.unit).1
  have impossible := fibreInjective
    (show valueFibreMap PUnit.unit (false, false) =
      valueFibreMap PUnit.unit (false, true) from rfl)
  exact Bool.false_ne_true (congrArg Prod.snd impossible)

/-- Repeating one lossy observation does not repair comprehension. -/
theorem duplicatedValue_totalMap_not_bijective :
    ¬ Function.Bijective (totalMap duplicatedValueFibreMap) := by
  intro totalBijective
  have fibreInjective :=
    ((totalMap_bijective_iff duplicatedValueFibreMap).1
      totalBijective PUnit.unit).1
  have impossible := fibreInjective
    (show duplicatedValueFibreMap PUnit.unit (false, false) =
      duplicatedValueFibreMap PUnit.unit (false, true) from rfl)
  exact Bool.false_ne_true (congrArg Prod.snd impossible)

/-- The joint value-and-route map is fibrewise an equivalence. -/
def jointFibreEquivalence :
    ∀ context, UnitPairFamily context ≃ UnitJointFamily context :=
  fun _ =>
    { toFun := fun pair => (pair.1, pair.2)
      invFun := fun pair => (pair.1, pair.2)
      left_inv := by
        intro pair
        rcases pair with ⟨value, route⟩
        rfl
      right_inv := by
        intro pair
        rcases pair with ⟨value, route⟩
        rfl }

/-- Consequently the joint observation preserves the selected CwF
comprehension as an isomorphism of types over the unit context. -/
def jointDisplayIso :
    (⟨UnitPairFamily⟩ : TypeOver (familiesCwf.{0}) PUnit) ≅
      (⟨UnitJointFamily⟩ : TypeOver (familiesCwf.{0}) PUnit) :=
  displayIso jointFibreEquivalence

theorem joint_totalMap_bijective :
    Function.Bijective (totalMap jointFibreMap) :=
  (totalMap_bijective_iff jointFibreMap).2
    (fun context => (jointFibreEquivalence context).bijective)

/-- Joint separation and comprehension preservation agree in the positive
control, whereas either value coordinate alone remains lossy. -/
theorem observation_comprehension_boundary :
    (¬ Function.Bijective (totalMap valueFibreMap)) ∧
      (¬ Function.Bijective (totalMap duplicatedValueFibreMap)) ∧
      Function.Bijective (totalMap jointFibreMap) ∧
      Nonempty
        ((⟨UnitPairFamily⟩ : TypeOver (familiesCwf.{0}) PUnit) ≅
          (⟨UnitJointFamily⟩ : TypeOver (familiesCwf.{0}) PUnit)) :=
  ⟨value_totalMap_not_bijective,
    duplicatedValue_totalMap_not_bijective,
    joint_totalMap_bijective,
    ⟨jointDisplayIso⟩⟩

end Canary

#print axioms totalMap_injective_iff
#print axioms totalMap_surjective_iff
#print axioms totalMap_bijective_iff
#print axioms displayMap
#print axioms displayIso
#print axioms Canary.value_totalMap_not_bijective
#print axioms Canary.duplicatedValue_totalMap_not_bijective
#print axioms Canary.jointDisplayIso
#print axioms Canary.joint_totalMap_bijective
#print axioms Canary.observation_comprehension_boundary

end Mettapedia.TypeTheory.SetFamilyComprehensionMap
