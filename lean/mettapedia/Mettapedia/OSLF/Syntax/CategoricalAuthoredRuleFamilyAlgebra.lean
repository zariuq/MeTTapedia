import Mettapedia.OSLF.Syntax.CategoricalAuthoredRulePolynomial

/-!
# Indexed families of rule algebras without coproduct assumptions

An authored presentation has one action for each declared rule. A target
with finite limits and chosen function objects need not have coproducts, so
the semantic category should retain this family directly. When a target
does have coproducts, the family's actions may also be assembled into the
single coproduct-polynomial algebra.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredRuleFamilyAlgebra

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation
open Mettapedia.OSLF.Binding.CategoricalAuthoredRulePolynomial
open Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps

universe u v w

/-- Algebras for a family of endofunctors on one carrier, with no coproduct
requirement on the ambient category. -/
structure FamilyAlgebra {C : Type u} [Category.{v} C]
    {I : Type w} (F : I → C ⥤ C) where
  carrier : C
  action : (index : I) → (F index).obj carrier ⟶ carrier

namespace FamilyAlgebra

variable {C : Type u} [Category.{v} C] {I : Type w}
variable {F : I → C ⥤ C}

structure Hom (A B : FamilyAlgebra F) where
  carrier : A.carrier ⟶ B.carrier
  action : ∀ index : I,
    (F index).map carrier ≫ B.action index =
      A.action index ≫ carrier

@[ext] theorem Hom.ext {A B : FamilyAlgebra F} {f g : Hom A B}
    (same : f.carrier = g.carrier) : f = g := by
  cases f
  cases g
  cases same
  rfl

instance : Category (FamilyAlgebra F) where
  Hom := Hom
  id A := {
    carrier := 𝟙 A.carrier
    action := by intro index; simp }
  comp f g := {
    carrier := f.carrier ≫ g.carrier
    action := by
      intro index
      rw [Functor.map_comp, Category.assoc, g.action index,
        ← Category.assoc, f.action index, Category.assoc] }
  id_comp := by intros; apply Hom.ext; simp
  comp_id := by intros; apply Hom.ext; simp
  assoc := by intros; apply Hom.ext; exact Category.assoc _ _ _

end FamilyAlgebra

variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
  [MonoidalClosed D] [CategoryTheory.Limits.HasPullbacks D]
variable (M : Model S D) (P : ProgramCarrier M)
variable (rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema))

/-- The actual authored rule polynomials as an indexed family. The index is
the declaration's position, so duplicates remain distinct. -/
noncomputable def authoredFamily (index : Fin rules.length) :
    EventSlice M P ⥤ EventSlice M P :=
  rulePolynomial M P (rules.get index)

/-- Assemble each authored firing action into a family algebra, without
requiring any coproduct of rule positions in the target. -/
noncomputable def toFamily :
    OperationalModel M P rules ⥤ FamilyAlgebra (authoredFamily M P rules) where
  obj X := {
    carrier := Over.mk X.endpoints
    action := fun index =>
      actionToSlice M P (rules.get index) (Over.mk X.endpoints)
        (X.action index) }
  map {X Y} f := by
    let graphMap : Over.mk X.endpoints ⟶ Over.mk Y.endpoints :=
      Over.homMk f.event f.endpoints
    refine { carrier := graphMap, action := ?_ }
    intro index
    exact (action_square_iff M P (rules.get index) graphMap
      (X.action index) (Y.action index)).2 (f.action index)
  map_id := by
    intro X
    apply FamilyAlgebra.Hom.ext
    apply Over.OverMorphism.ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply FamilyAlgebra.Hom.ext
    apply Over.OverMorphism.ext
    rfl

/-- Read a family algebra as an authored operational model. -/
noncomputable def fromFamily :
    FamilyAlgebra (authoredFamily M P rules) ⥤
      OperationalModel M P rules where
  obj A := {
    event := A.carrier.left
    endpoints := A.carrier.hom
    action := fun index =>
      actionOfSlice M P (rules.get index) A.carrier (A.action index) }
  map {A B} f := {
    event := f.carrier.left
    endpoints := f.carrier.w
    action := by
      intro index
      exact (action_square_iff M P (rules.get index) f.carrier
        (actionOfSlice M P (rules.get index) A.carrier (A.action index))
        (actionOfSlice M P (rules.get index) B.carrier (B.action index))).1
          (f.action index) }
  map_id := by
    intro A
    apply OperationalModel.Hom.ext
    rfl
  map_comp := by
    intro A B C f g
    apply OperationalModel.Hom.ext
    rfl

instance toFamily_faithful : (toFamily M P rules).Faithful where
  map_injective := by
    intro X Y f g same
    apply OperationalModel.Hom.ext
    exact congrArg (fun h :
      (toFamily M P rules).obj X ⟶ (toFamily M P rules).obj Y =>
        h.carrier.left) same

instance toFamily_full : (toFamily M P rules).Full where
  map_surjective := by
    intro X Y f
    let graphMap := f.carrier
    let lifted : OperationalModel.Hom M P X Y := {
      event := graphMap.left
      endpoints := graphMap.w
      action := by
        intro index
        exact (action_square_iff M P (rules.get index) graphMap
          (X.action index) (Y.action index)).1 (f.action index) }
    refine ⟨lifted, ?_⟩
    apply FamilyAlgebra.Hom.ext
    apply Over.OverMorphism.ext
    rfl

noncomputable instance toFamily_essSurj :
    (toFamily M P rules).EssSurj where
  mem_essImage A := by
    let source := (fromFamily M P rules).obj A
    have same : (toFamily M P rules).obj source = A := by
      cases A with
      | mk graph actions =>
        cases graph
        dsimp [source, fromFamily, toFamily]
        congr 1
    exact ⟨source, ⟨eqToIso same⟩⟩

noncomputable instance toFamily_isEquivalence :
    (toFamily M P rules).IsEquivalence where

/-- The operational meaning of a finite authored rule list is a family of
algebras over its true scoped-premise polynomials. This equivalence includes
all model maps and needs no coproducts or initial-algebra assumptions. -/
noncomputable def familyEquivalence :
    OperationalModel M P rules ≌ FamilyAlgebra (authoredFamily M P rules) :=
  (toFamily M P rules).asEquivalence

end Mettapedia.OSLF.Binding.CategoricalAuthoredRuleFamilyAlgebra
