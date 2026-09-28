import Mettapedia.OSLF.Syntax.SortIndexedScopedTreeLifting
import Mettapedia.OSLF.Syntax.ScopedOperationalFreeModel

/-!
# Free rule algebra for sort-indexed scoped premises

The authored scoped rule skeleton determines a rule presentation whose
judgments retain the full context of sort names. Its free algebra consists
of complete constructor trees. The cartesian forgetful map to the older
depth-indexed presentation is an actual map of rule presentations and
therefore transports both models and their interpretations.

This is the free *rule-algebra* component of the Chapter 7 construction.
The combined binding/equation/function/operation classifier still needs
its own comparison and universal property.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SortIndexedScopedFreeModel

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory
open Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation

/-- Closure under each sorted authored constructor, with all recursive
premise positions supplied in their full binder contexts. -/
def AuthoredRuleClosed (relEnv : RelationEnv) (lang : LanguageDef)
    (predicate : Judgment → Prop) : Prop :=
  (presentation relEnv lang).RuleClosed (fun _ => predicate)

/-- The free sorted derivations form the least predicate closed under the
authored scoped constructors. -/
theorem derivation_least (relEnv : RelationEnv) (lang : LanguageDef)
    (predicate : Judgment → Prop)
    (closed : AuthoredRuleClosed relEnv lang predicate)
    (judgment : Judgment)
    (tree : (presentation relEnv lang).Derivation () judgment) :
    predicate judgment :=
  FiniteRulePremiseLists.FinitePresentation.derivation_least
    (presentation relEnv lang) (fun _ => predicate)
    closed () judgment tree

/-- The authored rule presentation with full sort contexts at each premise. -/
def authoredRules (relEnv : RelationEnv) (lang : LanguageDef) :
    Presentation Unit where
  Judgment := fun _ => Judgment
  rules := (presentation relEnv lang).polynomial

/-- Its least proof-relevant model retains each constructor occurrence and
each ordered recursive premise. -/
def freeAuthoredRules (relEnv : RelationEnv) (lang : LanguageDef) :
    Equipped Unit :=
  free (authoredRules relEnv lang)

/-- Erasing sort names from judgments is cartesian: no rule constructor or
recursive firing position is removed or duplicated. -/
def toDepthPresentation (relEnv : RelationEnv) (lang : LanguageDef) :
    authoredRules relEnv lang ⟶
      ScopedOperationalFreeModel.authoredRules relEnv lang where
  judgment := fun _ judgment => judgment.depth
  rules := depthPolynomialMap relEnv lang

/-- The rule-presentation map acts on complete free firing trees. -/
noncomputable def toDepthFreeModel (relEnv : RelationEnv)
    (lang : LanguageDef) :
    freeAuthoredRules relEnv lang ⟶
      ScopedOperationalFreeModel.freeAuthoredRules relEnv lang :=
  freeMap (toDepthPresentation relEnv lang)

/-- On each sorted judgment, the categorical evidence map is the
previously constructed recursive sort-erasure map. -/
theorem toDepthFreeModel_tree (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment)
    (tree : (presentation relEnv lang).Derivation () judgment) :
    (toDepthFreeModel relEnv lang).toFun () judgment tree =
      eraseTree relEnv lang judgment tree := by
  rfl

/-- The categorical forgetful map is bijective on each fixed root-judgment
fibre. Different sorted root judgments may still have the same depth image,
so this does not assert a global equivalence of rule presentations. -/
theorem toDepthFreeModel_fibre_bijective (relEnv : RelationEnv)
    (lang : LanguageDef) (judgment : Judgment) :
    Function.Bijective
      ((toDepthFreeModel relEnv lang).toFun () judgment) := by
  change Function.Bijective (eraseTree relEnv lang judgment)
  exact (SortIndexedScopedTreeLifting.derivationEquiv relEnv lang judgment).bijective

/-- A map out of the free sorted rule algebra is exactly a cartesian
interpretation of its authored rule presentation in the target. -/
noncomputable def freeHomEquiv (relEnv : RelationEnv) (lang : LanguageDef)
    (target : Equipped Unit) :
    (freeAuthoredRules relEnv lang ⟶ target) ≃
      (authoredRules relEnv lang ⟶ target.presentation) :=
  IndexedOperationalPresentationCategory.freeHomEquiv
    (authoredRules relEnv lang) target

/-- An interpretation of the depth-indexed presentation restricts along
the sort-erasure map. The equality includes maps between rule models,
not only endpoint predicates. -/
theorem interpretation_restricts (relEnv : RelationEnv)
    (lang : LanguageDef) (target : Equipped Unit)
    (interpretation : ScopedOperationalFreeModel.freeAuthoredRules
      relEnv lang ⟶ target) :
    freeHomEquiv relEnv lang target
      (toDepthFreeModel relEnv lang ≫ interpretation) =
    toDepthPresentation relEnv lang ≫
      (ScopedOperationalFreeModel.freeHomEquiv relEnv lang target)
        interpretation := by
  rfl

/-- The restricted interpretation evaluates a sorted constructor tree by
erasing its sort annotations, then applying the original interpretation.
The action still retains the individual firing tree as evidence. -/
theorem restricted_interpretation_tree (relEnv : RelationEnv)
    (lang : LanguageDef) (target : Equipped Unit)
    (interpretation : ScopedOperationalFreeModel.freeAuthoredRules
      relEnv lang ⟶ target)
    (judgment : Judgment)
    (tree : (presentation relEnv lang).Derivation () judgment) :
    (toDepthFreeModel relEnv lang ≫ interpretation).toFun () judgment tree =
      interpretation.toFun () judgment.depth
        (eraseTree relEnv lang judgment tree) := by
  rfl

/-- Any interpretation of the depth-indexed free rule algebra evaluates a
sort-annotated lift exactly as it evaluates the original firing history. -/
theorem restricted_interpretation_lift (relEnv : RelationEnv)
    (lang : LanguageDef) (target : Equipped Unit)
    (interpretation : ScopedOperationalFreeModel.freeAuthoredRules
      relEnv lang ⟶ target)
    (judgment : Judgment)
    (tree : (ScopedOperationalPresentation.presentation relEnv lang).Derivation
      () judgment.depth) :
    (toDepthFreeModel relEnv lang ≫ interpretation).toFun () judgment
      (SortIndexedScopedTreeLifting.liftTreeAt relEnv lang judgment tree) =
      interpretation.toFun () judgment.depth tree := by
  have mapped := restricted_interpretation_tree relEnv lang target
    interpretation judgment
    (SortIndexedScopedTreeLifting.liftTreeAt relEnv lang judgment tree)
  have erased := SortIndexedScopedTreeLifting.erase_liftTreeAt
    relEnv lang judgment tree
  exact mapped.trans
    (congrArg (interpretation.toFun () judgment.depth) erased)

/-- No constructor of the authored scoped rule presentation concludes at
zero fuel, including when a full sort context is retained. -/
theorem no_zero_fuel_derivation (relEnv : RelationEnv)
    (lang : LanguageDef) (ambient : List TypeExpr)
    (source target : Pattern) :
    ¬ Nonempty ((presentation relEnv lang).Derivation ()
      ⟨0, ambient, source, target⟩) := by
  intro sorted
  exact ScopedOperationalFreeModel.no_zero_fuel_derivation
    relEnv lang ambient.length source target
    (sorted_derivation_has_depth_derivation relEnv lang
      ⟨0, ambient, source, target⟩ sorted)

/-- The zero-fuel exclusion also applies when the judgment is supplied as
data rather than written as a constructor expression. -/
theorem no_derivation_of_zero_fuel (relEnv : RelationEnv)
    (lang : LanguageDef) (judgment : Judgment)
    (zero : judgment.fuel = 0) :
    ¬ Nonempty ((presentation relEnv lang).Derivation () judgment) := by
  cases judgment with
  | mk fuel ambient source target =>
      cases fuel with
      | zero =>
          exact no_zero_fuel_derivation relEnv lang ambient source target
      | succ fuel => cases zero

/-- A complete one-fuel tree cannot require a recursive premise: every
such premise would have fuel zero, where no authored constructor exists.
The result identifies the actual premise-position type as empty. -/
theorem one_fuel_shape_nullary (relEnv : RelationEnv)
    (lang : LanguageDef) (ambient : List TypeExpr)
    (source target : Pattern)
    (shape : (presentation relEnv lang).polynomial.Shape ()
      ⟨1, ambient, source, target⟩)
    (children : (position : (presentation relEnv lang).polynomial.Position
      shape) → (presentation relEnv lang).Derivation ()
      ((presentation relEnv lang).polynomial.next shape position)) :
    IsEmpty ((presentation relEnv lang).polynomial.Position shape) := by
  refine ⟨?_⟩
  intro position
  let child := (presentation relEnv lang).polynomial.next shape position
  have childFuel : child.fuel = 0 := by
    simp [child, FiniteRulePremiseLists.FinitePresentation.polynomial,
      SortIndexedScopedOperationalPresentation.presentation]
  exact no_derivation_of_zero_fuel relEnv lang child childFuel
    ⟨children position⟩

#print axioms toDepthPresentation
#print axioms toDepthFreeModel_tree
#print axioms toDepthFreeModel_fibre_bijective
#print axioms freeHomEquiv
#print axioms interpretation_restricts
#print axioms restricted_interpretation_lift
#print axioms restricted_interpretation_tree
#print axioms no_zero_fuel_derivation
#print axioms one_fuel_shape_nullary

end Mettapedia.OSLF.Binding.SortIndexedScopedFreeModel
