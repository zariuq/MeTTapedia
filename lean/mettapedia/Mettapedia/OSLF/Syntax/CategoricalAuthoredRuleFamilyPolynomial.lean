import Mettapedia.OSLF.Syntax.CategoricalAuthoredRuleFamilyAlgebra
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# A finite authored rule family as one event-graph polynomial

For a fixed binding interpretation and program carrier, each authored rule
demands a graph of premise witnesses. Their coproduct remembers which rule
fired. An algebra for the resulting endofunctor is exactly an interpretation
of every authored rule, including ordered premises under local binders.

This identifies the general free-event problem with an initial-algebra
problem. It does not assume that the target has such initial algebras.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredRuleFamilyPolynomial

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation
open Mettapedia.OSLF.Binding.CategoricalAuthoredRulePolynomial
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleFamilyAlgebra
open Mettapedia.OSLF.Binding.CategoricalScopedRuleAction
open Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable (M : Model S D) (P : ProgramCarrier M)
variable (rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema))
variable [HasCoproductsOfShape (Fin rules.length) (EventSlice M P)]

/-- The graph demanded by a selected rule, retaining its position in the
authored rule list. -/
noncomputable abbrev ruleSummand (G : EventSlice M P) (index : Fin rules.length) :
    EventSlice M P :=
  (rulePolynomial M P (rules.get index)).obj G

/-- The finite coproduct of the actual scoped premise polynomials. Distinct
rule-list positions remain distinct summands, even when their endpoints and
premises coincide. -/
noncomputable def ruleFamilyPolynomial : EventSlice M P ⥤ EventSlice M P where
  obj G := ∐ fun index : Fin rules.length => ruleSummand M P rules G index
  map {G H} f := Limits.Sigma.map (fun index =>
    (rulePolynomial M P (rules.get index)).map f)
  map_id G := by
    change Limits.Sigma.map (fun index : Fin rules.length =>
      (rulePolynomial M P (rules.get index)).map (𝟙 G)) = 𝟙 _
    simp
  map_comp f g := by
    change Limits.Sigma.map (fun index : Fin rules.length =>
      (rulePolynomial M P (rules.get index)).map (f ≫ g)) =
      Limits.Sigma.map (fun index : Fin rules.length =>
        (rulePolynomial M P (rules.get index)).map f) ≫
      Limits.Sigma.map (fun index : Fin rules.length =>
        (rulePolynomial M P (rules.get index)).map g)
    rw [Limits.Sigma.map_comp_map]
    congr 1
    funext index
    exact (rulePolynomial M P (rules.get index)).map_comp f g

/-- All individual authored rule actions assemble into one algebra arrow. -/
noncomputable def actionToFamily (G : EventSlice M P)
    (actions : (index : Fin rules.length) →
      InterpretsRule M P G.left G.hom (rules.get index)) :
    (ruleFamilyPolynomial M P rules).obj G ⟶ G :=
  Limits.Sigma.desc (fun index => actionToSlice M P (rules.get index) G (actions index))

/-- Restrict a family algebra arrow to the chosen authored rule. -/
noncomputable def actionOfFamily (G : EventSlice M P)
    (action : (ruleFamilyPolynomial M P rules).obj G ⟶ G)
    (index : Fin rules.length) :
    InterpretsRule M P G.left G.hom (rules.get index) :=
  actionOfSlice M P (rules.get index) G
    (Limits.Sigma.ι (ruleSummand M P rules G) index ≫ action)

theorem actionOfFamily_actionToFamily (G : EventSlice M P)
    (actions : (index : Fin rules.length) →
      InterpretsRule M P G.left G.hom (rules.get index)) :
    actionOfFamily M P rules G (actionToFamily M P rules G actions) =
      actions := by
  funext index
  simp [actionOfFamily, actionToFamily,
    actionOfSlice_actionToSlice]

theorem actionToFamily_actionOfFamily (G : EventSlice M P)
    (action : (ruleFamilyPolynomial M P rules).obj G ⟶ G) :
    actionToFamily M P rules G (actionOfFamily M P rules G action) =
      action := by
  apply Limits.Sigma.hom_ext
  intro index
  simp [actionToFamily, actionOfFamily,
    actionToSlice_actionOfSlice]

/-- The one algebra square is precisely the family of actual authored rule
action squares. No target-step coverage or event injectivity is imposed. -/
theorem action_family_square_iff {G H : EventSlice M P}
    (f : G ⟶ H)
    (source : (index : Fin rules.length) →
      InterpretsRule M P G.left G.hom (rules.get index))
    (target : (index : Fin rules.length) →
      InterpretsRule M P H.left H.hom (rules.get index)) :
    (ruleFamilyPolynomial M P rules).map f ≫
        actionToFamily M P rules H target =
      actionToFamily M P rules G source ≫ f ↔
    ∀ index : Fin rules.length,
      mapInput (ruleInputMap M P f.left f.w (rules.get index)) ≫
          (target index).fire =
        (source index).fire ≫ f.left := by
  constructor
  · intro equal index
    have component := congrArg
      (fun h => Limits.Sigma.ι (ruleSummand M P rules G) index ≫ h) equal
    have square :
        (rulePolynomial M P (rules.get index)).map f ≫
          actionToSlice M P (rules.get index) H (target index) =
        actionToSlice M P (rules.get index) G (source index) ≫ f := by
      dsimp [ruleFamilyPolynomial, actionToFamily] at component
      rw [← Category.assoc, Limits.Sigma.ι_map,
        Category.assoc, Limits.Sigma.ι_desc] at component
      simpa only [← Category.assoc, Limits.Sigma.ι_desc,
        ruleSummand, List.get_eq_getElem] using component
    exact (action_square_iff M P (rules.get index) f
      (source index) (target index)).1 square
  · intro each
    apply Limits.Sigma.hom_ext
    intro index
    have square := (action_square_iff M P (rules.get index) f
      (source index) (target index)).2 (each index)
    dsimp [ruleFamilyPolynomial, actionToFamily]
    rw [← Category.assoc, Limits.Sigma.ι_map,
      Category.assoc, Limits.Sigma.ι_desc]
    simpa only [← Category.assoc, Limits.Sigma.ι_desc,
      ruleSummand, List.get_eq_getElem] using square

/-- Interpret an authored finite family of rules as one algebra of the
coproduct premise polynomial. -/
noncomputable def familyToAlgebra :
    OperationalModel M P rules ⥤
      Endofunctor.Algebra (ruleFamilyPolynomial M P rules) where
  obj X := {
    a := Over.mk X.endpoints
    str := actionToFamily M P rules (Over.mk X.endpoints) X.action }
  map {X Y} f := by
    let graphMap : Over.mk X.endpoints ⟶ Over.mk Y.endpoints :=
      Over.homMk f.event f.endpoints
    refine { f := graphMap, h := ?_ }
    exact (action_family_square_iff M P rules graphMap
      X.action Y.action).2 f.action
  map_id := by
    intro X
    apply Endofunctor.Algebra.Hom.ext
    apply Over.OverMorphism.ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply Endofunctor.Algebra.Hom.ext
    apply Over.OverMorphism.ext
    rfl

/-- Read an algebra as a model of all the authored rules. -/
noncomputable def familyFromAlgebra :
    Endofunctor.Algebra (ruleFamilyPolynomial M P rules) ⥤
      OperationalModel M P rules where
  obj A := {
    event := A.a.left
    endpoints := A.a.hom
    action := actionOfFamily M P rules A.a A.str }
  map {A B} f := {
    event := f.f.left
    endpoints := f.f.w
    action := (action_family_square_iff M P rules f.f
      (actionOfFamily M P rules A.a A.str)
      (actionOfFamily M P rules B.a B.str)).1 (by
        simpa only [actionToFamily_actionOfFamily] using f.h) }
  map_id := by
    intro A
    apply OperationalModel.Hom.ext
    rfl
  map_comp := by
    intro A B C f g
    apply OperationalModel.Hom.ext
    rfl

instance familyToAlgebra_faithful :
    (familyToAlgebra M P rules).Faithful where
  map_injective := by
    intro X Y f g same
    apply OperationalModel.Hom.ext
    exact congrArg (fun h :
      (familyToAlgebra M P rules).obj X ⟶
        (familyToAlgebra M P rules).obj Y => h.f.left) same

instance familyToAlgebra_full :
    (familyToAlgebra M P rules).Full where
  map_surjective := by
    intro X Y f
    let graphMap := f.f
    let lifted : OperationalModel.Hom M P X Y := {
      event := graphMap.left
      endpoints := graphMap.w
      action := (action_family_square_iff M P rules graphMap
        X.action Y.action).1 f.h }
    refine ⟨lifted, ?_⟩
    apply Endofunctor.Algebra.Hom.ext
    apply Over.OverMorphism.ext
    rfl

noncomputable instance familyToAlgebra_essSurj :
    (familyToAlgebra M P rules).EssSurj where
  mem_essImage A := by
    let source := (familyFromAlgebra M P rules).obj A
    have same : (familyToAlgebra M P rules).obj source = A := by
      cases A with
      | mk graph action =>
        cases graph
        dsimp [source, familyFromAlgebra, familyToAlgebra]
        congr 1
        exact actionToFamily_actionOfFamily M P rules _ action
    exact ⟨source, ⟨eqToIso same⟩⟩

noncomputable instance familyToAlgebra_isEquivalence :
    (familyToAlgebra M P rules).IsEquivalence where

/-- For any finite list of authored rules, fixed-base proof-relevant
operational models are exactly algebras of the sum of their scoped-premise
polynomials. The conclusion holds for every arity of ordered, binder-local
premises; free-algebra existence is a separate construction. -/
noncomputable def familyAlgebraEquivalence :
    OperationalModel M P rules ≌
      Endofunctor.Algebra (ruleFamilyPolynomial M P rules) :=
  (familyToAlgebra M P rules).asEquivalence

/-- When the event slice has the required finite coproduct, the independent
family-of-actions semantics agrees with its coproduct-polynomial encoding.
The former remains available in finite-limit targets without coproducts. -/
noncomputable def familyCoproductEquivalence :
    FamilyAlgebra (authoredFamily M P rules) ≌
      Endofunctor.Algebra (ruleFamilyPolynomial M P rules) :=
  (familyEquivalence M P rules).symm.trans
    (familyAlgebraEquivalence M P rules)

end Mettapedia.OSLF.Binding.CategoricalAuthoredRuleFamilyPolynomial
