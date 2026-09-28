import Mettapedia.OSLF.Syntax.IndexedRuleArityComparison

/-!
# Finitary indexed-rule algebras and their finite-product interpretations

An independently specified indexed rule algebra is compared with a
finite-product-preserving interpretation of the finite-context syntax. The
construction retains every rule occurrence and premise position. It is the
fixed-binding-model, Set-valued operational component of the larger authored
Chapter 7 classifier; binding-equation and general-target comparisons are
additional structure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts

open Mettapedia.TypeTheory
open CategoryTheory
open CategoryTheory.Limits

universe uIndex uShape uSem

variable {Judgment : Type uIndex}
variable (P : IndexedPolynomial.{0, uIndex, uShape, 0}
  Unit (fun _ => Judgment))

/-- An indexed rule algebra is specified independently of functors out of
the syntactic category. -/
structure RuleAlgebraModel where
  carrier : Judgment → Type (max uIndex uSem)
  action : P.Algebra (fun _ judgment => carrier judgment)

/-- A semantic interpretation includes actual finite-product preservation,
not merely an objectwise assignment. -/
structure ProductInterpretation where
  functor : Context P ⥤ Type (max uIndex uSem)
  preserves : PreservesFiniteProducts functor

attribute [instance] ProductInterpretation.preserves

/-- Equality of algebra maps is determined by their maps on carrier values. -/
theorem ruleHom_ext {X Y : RuleAlgebraModel.{uIndex,uShape,uSem} P}
    (f g : IndexedPolynomial.Algebra.Hom X.action Y.action)
    (same : ∀ judgment (value : X.carrier judgment),
      f.toFun PUnit.unit judgment value =
        g.toFun PUnit.unit judgment value) : f = g := by
  cases f with
  | mk ff hf =>
      cases g with
      | mk gg hg =>
          have hfun : ff = gg := by
            funext base judgment value
            exact same judgment value
          cases hfun
          rfl

/-- The same extensionality principle for homomorphisms with carriers not
yet packaged as category objects. -/
theorem algebraHom_ext
    {source target : Judgment → Type (max uIndex uSem)}
    {A : P.Algebra (fun _ judgment => source judgment)}
    {B : P.Algebra (fun _ judgment => target judgment)}
    (f g : IndexedPolynomial.Algebra.Hom A B)
    (same : ∀ judgment (value : source judgment),
      f.toFun PUnit.unit judgment value =
        g.toFun PUnit.unit judgment value) : f = g := by
  cases f with
  | mk ff hf =>
      cases g with
      | mk gg hg =>
          have hfun : ff = gg := by
            funext base judgment value
            exact same judgment value
          cases hfun
          rfl

/-- Compose algebra homomorphisms using their indexed constructor laws. -/
def composeRuleHom {X Y Z : RuleAlgebraModel.{uIndex,uShape,uSem} P}
    (f : IndexedPolynomial.Algebra.Hom X.action Y.action)
    (g : IndexedPolynomial.Algebra.Hom Y.action Z.action) :
    IndexedPolynomial.Algebra.Hom X.action Z.action where
  toFun := fun base judgment value =>
    g.toFun base judgment (f.toFun base judgment value)
  commutes := by
    intro base judgment layer
    calc
      g.toFun base judgment (f.toFun base judgment
          (X.action.act base judgment layer)) =
        g.toFun base judgment
          (Y.action.act base judgment
            (IndexedPolynomial.Extension.map P f.toFun layer)) := by
          rw [f.commutes]
      _ = Z.action.act base judgment
          (IndexedPolynomial.Extension.map P g.toFun
            (IndexedPolynomial.Extension.map P f.toFun layer)) := by
          rw [g.commutes]
      _ = Z.action.act base judgment
          (IndexedPolynomial.Extension.map P
            (fun base index value => g.toFun base index (f.toFun base index value))
            layer) := by
          rw [IndexedPolynomial.Extension.map_comp]

/-- Algebra models and constructor-preserving maps form a category. -/
instance : Category (RuleAlgebraModel.{uIndex,uShape,uSem} P) where
  Hom X Y := IndexedPolynomial.Algebra.Hom X.action Y.action
  id X := {
    toFun := fun _ _ value => value
    commutes := by intro base judgment layer; cases layer; rfl }
  comp f g := composeRuleHom P f g
  id_comp := by
    intro X Y f
    apply ruleHom_ext P
    intro judgment value
    rfl
  comp_id := by
    intro X Y f
    apply ruleHom_ext P
    intro judgment value
    rfl
  assoc := by
    intro W X Y Z f g h
    apply ruleHom_ext P
    intro judgment value
    rfl

/-- Product-preserving interpretations and ordinary natural maps form a
category; maps need not reflect or cover events. -/
noncomputable instance : Category (ProductInterpretation.{uIndex,uShape,uSem} P) where
  Hom X Y := X.functor ⟶ Y.functor
  id X := 𝟙 X.functor
  comp f g := f ≫ g
  id_comp := by intro X Y f; exact Category.id_comp f
  comp_id := by intro X Y f; exact Category.comp_id f
  assoc := by intro W X Y Z f g h; exact Category.assoc f g h

/-- The concrete semantic interpretation is functorial on independently
specified rule algebras and their homomorphisms. -/
noncomputable def classifyFunctor :
    RuleAlgebraModel.{uIndex,uShape,uSem} P ⥤
      ProductInterpretation.{uIndex,uShape,uSem} P where
  obj X := ⟨algebraSemantics P X.action,
    algebraSemanticsPreservesFiniteProducts P X.action⟩
  map f := algebraSemanticsHom P f
  map_id := by
    intro X
    apply NatTrans.ext
    funext Γ
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext assignment judgment slot
    rfl
  map_comp := by
    intro X Y Z f g
    apply NatTrans.ext
    funext Γ
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext assignment judgment slot
    rfl

/-- A finite-product interpretation reconstructs its actual indexed rule
algebra, functorially on ordinary natural transformations. -/
noncomputable def recoverFunctor
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape)) :
    ProductInterpretation.{uIndex,uShape,uSem} P ⥤
      RuleAlgebraModel.{uIndex,uShape,uSem} P where
  obj X := ⟨fun judgment => X.functor.obj (singleton P judgment),
    recoverAlgebra P finitePositions X.functor⟩
  map f := recoverAlgebraMap P finitePositions _ _ f
  map_id := by
    intro X
    apply algebraHom_ext P
    intro judgment value
    rfl
  map_comp := by
    intro X Y Z f g
    apply algebraHom_ext P
    intro judgment value
    rfl

/-- The algebra recovered from the interpretation of a given algebra is
isomorphic to that original algebra, with both maps preserving rules. -/
noncomputable def algebraRoundtripIso
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    (X : RuleAlgebraModel.{uIndex,uShape,uSem} P) :
    ((classifyFunctor P ⋙ recoverFunctor P finitePositions).obj X) ≅ X where
  hom := recoverSemanticsHom P finitePositions X.action
  inv := recoverSemanticsInvHom P finitePositions X.action
  hom_inv_id := by
    apply algebraHom_ext P
    intro judgment value
    exact recoverSemantics_recovered_roundTrip P finitePositions
      X.action judgment value
  inv_hom_id := by
    apply algebraHom_ext P
    intro judgment value
    exact recoverSemantics_original_roundTrip P finitePositions
      X.action judgment value

/-- The algebra round trip is natural in every constructor-preserving
model map. -/
noncomputable def algebraRoundtripNatIso
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape)) :
    classifyFunctor P ⋙ recoverFunctor P finitePositions ≅
      𝟭 (RuleAlgebraModel.{uIndex,uShape,uSem} P) :=
  NatIso.ofComponents
    (algebraRoundtripIso P finitePositions)
    (by
      intro X Y f
      apply algebraHom_ext P
      intro judgment value
      rfl)

/-- A product-preserving interpretation returns, after algebra recovery
and reinterpretation, to an isomorphic interpretation on every context. -/
noncomputable def interpretationRoundtripIso
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape))
    (X : ProductInterpretation.{uIndex,uShape,uSem} P) :
    ((recoverFunctor P finitePositions ⋙ classifyFunctor P).obj X) ≅ X where
  hom := (contextComparisonIso P finitePositions X.functor).inv
  inv := (contextComparisonIso P finitePositions X.functor).hom
  hom_inv_id := (contextComparisonIso P finitePositions X.functor).inv_hom_id
  inv_hom_id := (contextComparisonIso P finitePositions X.functor).hom_inv_id

/-- The interpretation round trip is natural in ordinary interpretation
maps, with no requirement that they cover target events. -/
noncomputable def interpretationRoundtripNatIso
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape)) :
    recoverFunctor P finitePositions ⋙ classifyFunctor P ≅
      𝟭 (ProductInterpretation.{uIndex,uShape,uSem} P) :=
  NatIso.ofComponents
    (interpretationRoundtripIso P finitePositions)
    (by
      intro X Y mapping
      apply NatTrans.ext
      funext Γ
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      funext assignment
      apply (contextComparison P Y.functor Γ).injective
      have h := contextComparison_map_natural P X.functor Y.functor
        mapping Γ ((contextComparison P X.functor Γ).symm assignment)
      change (contextComparison P Y.functor Γ)
          ((contextComparison P Y.functor Γ).symm
            (fun judgment slot => mapping.app (singleton P judgment)
              (assignment judgment slot))) =
        (contextComparison P Y.functor Γ)
          (mapping.app Γ ((contextComparison P X.functor Γ).symm assignment))
      rw [Equiv.apply_symm_apply]
      have hX := (contextComparison P X.functor Γ).apply_symm_apply assignment
      rw [hX] at h
      exact h.symm)

/-- Finitary indexed-rule algebras are equivalent, as a category with all
ordinary algebra maps, to finite-product-preserving Set-valued
interpretations of their free finite-context syntax. -/
noncomputable def finiteProductClassification
    (finitePositions : ∀ (judgment : Judgment)
      (shape : P.Shape PUnit.unit judgment), Finite (P.Position shape)) :
    RuleAlgebraModel.{uIndex,uShape,uSem} P ≌
      ProductInterpretation.{uIndex,uShape,uSem} P :=
  CategoryTheory.Equivalence.mk (classifyFunctor P) (recoverFunctor P finitePositions)
    (algebraRoundtripNatIso P finitePositions).symm
    (interpretationRoundtripNatIso P finitePositions)
end Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts
