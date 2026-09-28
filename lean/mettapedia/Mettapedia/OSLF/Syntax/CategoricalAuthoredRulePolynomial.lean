import Mettapedia.OSLF.Syntax.CategoricalAuthoredRuleInterpretation
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# An authored scoped rule as an endofunctor on event graphs

Fix a binding interpretation and a common program object. The premise
bundle of an authored conditional rule is recursive in the event graph.
It is an endofunctor of the slice over program endpoint pairs. An action
interpreting the rule is exactly an algebra arrow for this endofunctor.
This retains ordered, binder-local firing witnesses. No image or quotient
of the event graph enters the construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredRulePolynomial

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation
open Mettapedia.OSLF.Binding.CategoricalScopedRuleAction
open Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable (M : Model S D) (P : ProgramCarrier M)
variable (rule : IntrinsicScopedConditionalPolynomial.Rule S schema)

/-- Individual firing evidence with its endpoints in the fixed program
object. -/
abbrev EventSlice := Over (EndpointPairs M P)

/-- The event graph demanded by one firing of an authored conditional rule.
Its points are the ordered premise witnesses over one parameter assignment;
its endpoint arrow is the rule's declared conclusion at that assignment. -/
noncomputable def rulePolynomial : EventSlice M P ⥤ EventSlice M P where
  obj G := Over.mk
    (assignment (rulePremises M P G.left G.hom rule) ≫
      ruleConclusion M P rule)
  map {G H} f := Over.homMk
    (mapInput (ruleInputMap M P f.left f.w rule)) (by
      change mapInput (ruleInputMap M P f.left f.w rule) ≫
          (assignment (rulePremises M P H.left H.hom rule) ≫
            ruleConclusion M P rule) =
        assignment (rulePremises M P G.left G.hom rule) ≫
          ruleConclusion M P rule
      rw [← Category.assoc, mapInput_assignment]
      simp [ruleInputMap])
  map_id G := by
    apply Over.OverMorphism.ext
    exact mapInput_ruleInputMap_id M P G.hom (by simp) rule
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact mapInput_ruleInputMap_comp M P f.left g.left
      f.w g.w (by simp [Category.assoc, f.w, g.w]) rule

/-- The semantic firing action is an algebra map in the event-graph slice.
The slice equation is precisely the endpoint law, rather than an extra
assumption about source or target events. -/
noncomputable def actionToSlice (G : EventSlice M P)
    (action : InterpretsRule M P G.left G.hom rule) :
    (rulePolynomial M P rule).obj G ⟶ G :=
  Over.homMk action.fire action.endpoint_law

/-- Read a slice algebra map as the authored rule's firing action. -/
noncomputable def actionOfSlice (G : EventSlice M P)
    (map : (rulePolynomial M P rule).obj G ⟶ G) :
    InterpretsRule M P G.left G.hom rule where
  fire := map.left
  endpoint_law := map.w

theorem actionOfSlice_actionToSlice (G : EventSlice M P)
    (action : InterpretsRule M P G.left G.hom rule) :
    actionOfSlice M P rule G (actionToSlice M P rule G action) = action := by
  cases action
  rfl

theorem actionToSlice_actionOfSlice (G : EventSlice M P)
    (map : (rulePolynomial M P rule).obj G ⟶ G) :
    actionToSlice M P rule G (actionOfSlice M P rule G map) = map := by
  apply Over.OverMorphism.ext
  rfl

/-- Algebra homomorphism equations are exactly the authored action square.
This uses the actual position-preserving pullback map on scoped premises. -/
theorem action_square_iff {G H : EventSlice M P}
    (f : G ⟶ H)
    (source : InterpretsRule M P G.left G.hom rule)
    (target : InterpretsRule M P H.left H.hom rule) :
    (rulePolynomial M P rule).map f ≫
        actionToSlice M P rule H target =
      actionToSlice M P rule G source ≫ f ↔
    mapInput (ruleInputMap M P f.left f.w rule) ≫ target.fire =
      source.fire ≫ f.left := by
  constructor
  · intro equal
    exact congrArg CommaMorphism.left equal
  · intro equal
    apply Over.OverMorphism.ext
    exact equal

/-- A single-rule authored model is an algebra for its actual scoped
premise polynomial. -/
noncomputable def singleRuleToAlgebra :
    OperationalModel M P [rule] ⥤
      Endofunctor.Algebra (rulePolynomial M P rule) where
  obj X := {
    a := Over.mk X.endpoints
    str := actionToSlice M P rule (Over.mk X.endpoints)
      (X.action ⟨0, by simp⟩) }
  map {X Y} f := by
    let graphMap : Over.mk X.endpoints ⟶ Over.mk Y.endpoints :=
      Over.homMk f.event f.endpoints
    refine { f := graphMap, h := ?_ }
    exact (action_square_iff M P rule graphMap
      (X.action ⟨0, by simp⟩)
      (Y.action ⟨0, by simp⟩)).2 (f.action ⟨0, by simp⟩)
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

/-- Read an algebra for the scoped-rule polynomial as an operational
interpretation of the corresponding one-rule presentation. -/
noncomputable def singleRuleFromAlgebra :
    Endofunctor.Algebra (rulePolynomial M P rule) ⥤
      OperationalModel M P [rule] where
  obj A := {
    event := A.a.left
    endpoints := A.a.hom
    action index := by
      have one : index = ⟨0, by simp⟩ := by
        apply Fin.ext
        have bound : index.val < 1 := index.isLt
        have zero : index.val = 0 := by omega
        simpa only [Fin.val_mk] using zero
      subst index
      exact actionOfSlice M P rule A.a A.str }
  map {A B} f := {
    event := f.f.left
    endpoints := f.f.w
    action := by
      intro index
      have one : index = ⟨0, by simp⟩ := by
        apply Fin.ext
        have bound : index.val < 1 := index.isLt
        have zero : index.val = 0 := by omega
        simpa only [Fin.val_mk] using zero
      subst index
      exact (action_square_iff M P rule f.f
        (actionOfSlice M P rule A.a A.str)
        (actionOfSlice M P rule B.a B.str)).1 f.h }
  map_id := by
    intro A
    apply OperationalModel.Hom.ext
    rfl
  map_comp := by
    intro A B C f g
    apply OperationalModel.Hom.ext
    rfl

instance singleRuleToAlgebra_faithful :
    (singleRuleToAlgebra M P rule).Faithful where
  map_injective := by
    intro X Y f g same
    apply OperationalModel.Hom.ext
    exact congrArg (fun h :
      (singleRuleToAlgebra M P rule).obj X ⟶
        (singleRuleToAlgebra M P rule).obj Y => h.f.left) same

instance singleRuleToAlgebra_full :
    (singleRuleToAlgebra M P rule).Full where
  map_surjective := by
    intro X Y f
    let graphMap := f.f
    let lifted : OperationalModel.Hom M P X Y := {
      event := graphMap.left
      endpoints := graphMap.w
      action := by
        intro index
        have one : index = ⟨0, by simp⟩ := by
          apply Fin.ext
          have bound : index.val < 1 := index.isLt
          have zero : index.val = 0 := by omega
          simpa only [Fin.val_mk] using zero
        subst index
        exact (action_square_iff M P rule graphMap
          (X.action ⟨0, by simp⟩)
          (Y.action ⟨0, by simp⟩)).1 f.h }
    refine ⟨lifted, ?_⟩
    apply Endofunctor.Algebra.Hom.ext
    apply Over.OverMorphism.ext
    rfl

noncomputable instance singleRuleToAlgebra_essSurj :
    (singleRuleToAlgebra M P rule).EssSurj where
  mem_essImage A := by
    let source := (singleRuleFromAlgebra M P rule).obj A
    have same : (singleRuleToAlgebra M P rule).obj source = A := by
      cases A with
      | mk graph action =>
        cases graph
        dsimp [source, singleRuleFromAlgebra, singleRuleToAlgebra]
        congr 1
    exact ⟨source, ⟨eqToIso same⟩⟩

noncomputable instance singleRuleToAlgebra_isEquivalence :
    (singleRuleToAlgebra M P rule).IsEquivalence where

/-- Over a fixed binding interpretation and program carrier, a one-rule
operational model is precisely an algebra for the rule's scoped event
polynomial. This identifies the free-rule problem as an actual initial-
algebra problem in the event-graph slice. -/
noncomputable def singleRuleAlgebraEquivalence :
    OperationalModel M P [rule] ≌
      Endofunctor.Algebra (rulePolynomial M P rule) :=
  (singleRuleToAlgebra M P rule).asEquivalence

end Mettapedia.OSLF.Binding.CategoricalAuthoredRulePolynomial
