import Mettapedia.OSLF.Syntax.ResultSortedScopedOperationalPresentation
import Mettapedia.OSLF.Syntax.SortIndexedScopedFreeModel

/-!
# Free model of canonically result-sorted scoped rules

The free algebra retains constructor labels and distinct recursive firing
witnesses at each authored result sort. The cartesian forgetful map removes
result-sort certificates but keeps the same ordered firing positions. This
is the operational rule-algebra component; combining it with authored
binding syntax, equations, and function structure remains a separate
classifying theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType)
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory
open Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation

/-- Closure under every canonically admitted, result-sorted authored rule
constructor and its ordered recursive premise list. -/
def AuthoredRuleClosed (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) (predicate : Judgment → Prop) : Prop :=
  (presentation relEnv lang free).RuleClosed (fun _ => predicate)

/-- Complete free firing trees are the least predicate closed under the
canonically admitted result-sorted rule constructors. -/
theorem derivation_least (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) (predicate : Judgment → Prop)
    (closed : AuthoredRuleClosed relEnv lang free predicate)
    (judgment : Judgment)
    (tree : (presentation relEnv lang free).Derivation () judgment) :
    predicate judgment :=
  FiniteRulePremiseLists.FinitePresentation.derivation_least
    (presentation relEnv lang free) (fun _ => predicate)
    closed () judgment tree

/-- The canonically sorted authored rule presentation. -/
def authoredRules (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) : Presentation Unit where
  Judgment := fun _ => Judgment
  rules := (presentation relEnv lang free).polynomial

/-- Its initial proof-relevant operational model. -/
def freeAuthoredRules (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) : Equipped Unit :=
  IndexedOperationalPresentationCategory.free
    (authoredRules relEnv lang free)

/-- Each sorted constructor maps to its original scoped operational
constructor without losing or merging recursive premise positions. -/
def toContextSorted (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) :
    authoredRules relEnv lang free ⟶
      SortIndexedScopedFreeModel.authoredRules relEnv lang where
  judgment := fun _ judgment => judgment.eraseResult
  rules := erasePolynomialMap relEnv lang free

/-- The cartesian map acts on complete free firing trees. -/
noncomputable def toContextSortedFree (relEnv : RelationEnv)
    (lang : LanguageDef) (free : FreeTypeContext) :
    freeAuthoredRules relEnv lang free ⟶
      SortIndexedScopedFreeModel.freeAuthoredRules relEnv lang :=
  freeMap (toContextSorted relEnv lang free)

/-- A complete one-fuel raw firing carries a single root constructor.
Its source declaration canonically admits that constructor exactly when
its ordered premises can be annotated at the selected ambient context. -/
def OneFuelCanonical (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : List TypeExpr) (source target : Pattern)
    (tree : (SortIndexedScopedOperationalPresentation.presentation
      relEnv lang).Derivation () ⟨1, ambient, source, target⟩) : Prop :=
  match tree with
  | .roll shape _ =>
      ∃ children,
        ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
          ambient shape = some children

/-- A one-fuel authored firing with checked result endpoints and a
canonically compiled declaration lifts to the result-sorted free model.
No recursive child can be present at fuel one, by the established raw
zero-fuel exclusion. -/
noncomputable def admitOneFuelTree (relEnv : RelationEnv)
    (lang : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (resultType : TypeExpr)
    (source target : Pattern)
    (sourceTyped : HasType lang free ambient source resultType)
    (targetTyped : HasType lang free ambient target resultType)
    (tree : (SortIndexedScopedOperationalPresentation.presentation
      relEnv lang).Derivation () ⟨1, ambient, source, target⟩)
    (canonical : OneFuelCanonical relEnv lang ambient source target tree) :
    (presentation relEnv lang free).Derivation ()
      ⟨1, ambient, resultType, source, target⟩ :=
  match tree with
  | .roll shape rawChildren =>
      let selected := Classical.choose canonical
      let newShape : RuleShape relEnv lang free ambient resultType
          source target :=
        ⟨shape, selected, Classical.choose_spec canonical,
          sourceTyped, targetTyped⟩
      .roll newShape (fun position =>
        (SortIndexedScopedFreeModel.one_fuel_shape_nullary
          relEnv lang ambient source target shape rawChildren).false
          (((erasePolynomialMap relEnv lang free).onPosition ()
            ⟨1, ambient, resultType, source, target⟩
            newShape).symm position) |>.elim)

/-- Forgetting the admission certificate returns the exact original
one-fuel firing tree, not just another tree at the same endpoints. -/
theorem admitOneFuelTree_erase (relEnv : RelationEnv)
    (lang : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (resultType : TypeExpr)
    (source target : Pattern)
    (sourceTyped : HasType lang free ambient source resultType)
    (targetTyped : HasType lang free ambient target resultType)
    (tree : (SortIndexedScopedOperationalPresentation.presentation
      relEnv lang).Derivation () ⟨1, ambient, source, target⟩)
    (canonical : OneFuelCanonical relEnv lang ambient source target tree) :
    (toContextSortedFree relEnv lang free).toFun ()
      ⟨1, ambient, resultType, source, target⟩
      (admitOneFuelTree relEnv lang free ambient resultType source target
        sourceTyped targetTyped tree canonical) = tree := by
  match tree with
  | .roll shape rawChildren =>
      change Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll shape _ =
        Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll shape rawChildren
      congr 1
      funext position
      exact (SortIndexedScopedFreeModel.one_fuel_shape_nullary
        relEnv lang ambient source target shape rawChildren).false
          position |>.elim

/-- Interpreting the free result-sorted operational model is equivalent to
interpreting its canonically admitted rule constructors in a target model. -/
noncomputable def freeHomEquiv (relEnv : RelationEnv)
    (lang : LanguageDef) (free : FreeTypeContext)
    (target : Equipped Unit) :
    (freeAuthoredRules relEnv lang free ⟶ target) ≃
      (authoredRules relEnv lang free ⟶ target.presentation) :=
  IndexedOperationalPresentationCategory.freeHomEquiv
    (authoredRules relEnv lang free) target

/-- Interpretation after forgetting result sorts is precomposition by the
cartesian constructor map. This includes maps of firing evidence. -/
theorem interpretation_restricts (relEnv : RelationEnv)
    (lang : LanguageDef) (free : FreeTypeContext)
    (target : Equipped Unit)
    (interpretation : SortIndexedScopedFreeModel.freeAuthoredRules
      relEnv lang ⟶ target) :
    freeHomEquiv relEnv lang free target
      (toContextSortedFree relEnv lang free ≫ interpretation) =
    toContextSorted relEnv lang free ≫
      (SortIndexedScopedFreeModel.freeHomEquiv relEnv lang target)
        interpretation := by
  rfl

#print axioms derivation_least
#print axioms toContextSorted
#print axioms admitOneFuelTree
#print axioms admitOneFuelTree_erase
#print axioms interpretation_restricts

end Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel
