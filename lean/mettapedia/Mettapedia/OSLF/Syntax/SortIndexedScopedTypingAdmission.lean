import Mettapedia.OSLF.Syntax.AdmittedJudgmentRulePresentation
import Mettapedia.OSLF.Syntax.SortIndexedScopedFreeModel
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Endpoint-typed refinement of the authored scoped rule algebra

The raw sort-context presentation retains binder labels but admits shapes
whose endpoints are not terms of the selected authored result type. This
module restricts the judgment carrier to endpoints checked by the exact
`LanguageDef` typing relation and restricts each constructor at all of its
recursive children. Its cartesian inclusion retains firing evidence.

Endpoint typing is a necessary admission condition. It is not yet the full
generated subject-reduction theorem: a source-to-model comparison must also
establish that the rule's declared result sort, instantiated metavariables,
and premise outputs justify these endpoint certificates.
The fixed `resultType` is the homogeneous fragment used by the authored
lambda control. A general multi-sort presentation must retain each
premise's own result sort in its child judgment before using this criterion.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SortIndexedScopedTypingAdmission

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.AdmittedJudgmentRulePresentation
open Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory

/-- Both endpoints have the author's selected result type in the full
binder-sort context. This does not assume proof irrelevance of firings. -/
def EndpointsHaveType (language : LanguageDef)
    (free : FreeTypeContext) (resultType : TypeExpr)
    (judgment : Judgment) : Prop :=
  HasType language free judgment.ambient judgment.source resultType ∧
    HasType language free judgment.ambient judgment.target resultType

/-- The rule presentation with endpoint-admitted judgments and child
positions. Each retained shape proves that all its recursive children
are also admitted; nonrecursive premise guards remain in the raw shape. -/
def presentation (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (resultType : TypeExpr) :=
  restrict (SortIndexedScopedFreeModel.authoredRules relEnv language)
    (fun _ judgment => EndpointsHaveType language free resultType judgment)

/-- The free rule algebra of endpoint-admitted constructor trees. -/
def freePresentation (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (resultType : TypeExpr) :=
  IndexedOperationalPresentationCategory.free
    (presentation relEnv language free resultType)

/-- Forgetting endpoint certificates is cartesian and preserves every
individual recursive premise position. -/
def toRaw (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (resultType : TypeExpr) :
    presentation relEnv language free resultType ⟶
      SortIndexedScopedFreeModel.authoredRules relEnv language :=
  inclusion (SortIndexedScopedFreeModel.authoredRules relEnv language)
    (fun _ judgment => EndpointsHaveType language free resultType judgment)

/-- The same inclusion acts on complete proof-relevant firing trees. -/
noncomputable def toRawFree (relEnv : RelationEnv)
    (language : LanguageDef) (free : FreeTypeContext)
    (resultType : TypeExpr) :
    freePresentation relEnv language free resultType ⟶
      SortIndexedScopedFreeModel.freeAuthoredRules relEnv language :=
  includeFree (SortIndexedScopedFreeModel.authoredRules relEnv language)
    (fun _ judgment => EndpointsHaveType language free resultType judgment)

/-- The typed-to-depth presentation map factors through the full sort
context presentation. Each component is cartesian. -/
def toDepth (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (resultType : TypeExpr) :
    presentation relEnv language free resultType ⟶
      ScopedOperationalFreeModel.authoredRules relEnv language :=
  toRaw relEnv language free resultType ≫
    SortIndexedScopedFreeModel.toDepthPresentation relEnv language

/-- The same factorization acts on complete firing trees. -/
noncomputable def toDepthFree (relEnv : RelationEnv)
    (language : LanguageDef) (free : FreeTypeContext)
    (resultType : TypeExpr) :
    freePresentation relEnv language free resultType ⟶
      ScopedOperationalFreeModel.freeAuthoredRules relEnv language :=
  freeMap (toDepth relEnv language free resultType)

/-- Forgetting typing certificates and then sort labels acts exactly like
the composite cartesian presentation map on every firing tree. -/
theorem toDepthFree_tree (relEnv : RelationEnv)
    (language : LanguageDef) (free : FreeTypeContext)
    (resultType : TypeExpr)
    (index : (presentation relEnv language free resultType).Judgment ())
    (tree : (presentation relEnv language free resultType).rules.Fix ()
      index) :
    (toDepthFree relEnv language free resultType).toFun () index tree =
      SortIndexedScopedOperationalPresentation.eraseTree relEnv language
        index.1
        ((toRawFree relEnv language free resultType).toFun () index
          tree) := by
  exact Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms.Hom.mapFix_comp
    (toRaw relEnv language free resultType).rules
    (SortIndexedScopedFreeModel.toDepthPresentation relEnv language).rules
    () index tree

/-- A certified judgment index exposes the exact authored endpoint
typing proofs, in the context carried by the operational index. -/
theorem admitted_endpoints (relEnv : RelationEnv)
    (language : LanguageDef) (free : FreeTypeContext)
    (resultType : TypeExpr)
    (judgment : (presentation relEnv language free resultType).Judgment ()) :
    HasType language free judgment.1.ambient judgment.1.source resultType ∧
      HasType language free judgment.1.ambient judgment.1.target resultType :=
  judgment.2

/-- At every fuel and with any number of ordered recursive premises, a
typed free tree is exactly a raw free tree for which every node has typed
source and target endpoints. This does not assume that raw authored rules
produce those proofs; the remaining soundness theorem must do that. -/
noncomputable def typedTreeEquiv (relEnv : RelationEnv)
    (language : LanguageDef) (free : FreeTypeContext)
    (resultType : TypeExpr) (judgment : Judgment)
    (typed : EndpointsHaveType language free resultType judgment) :
    (presentation relEnv language free resultType).rules.Fix ()
      ⟨judgment, typed⟩ ≃
      {tree : (SortIndexedScopedOperationalPresentation.presentation
        relEnv language).Derivation () judgment //
        AllNodesAdmitted
          (SortIndexedScopedFreeModel.authoredRules relEnv language)
          (fun _ child => EndpointsHaveType language free resultType child)
          () judgment tree} :=
  admittedTreeEquiv
    (SortIndexedScopedFreeModel.authoredRules relEnv language)
    (fun _ child => EndpointsHaveType language free resultType child)
    () judgment typed

/-- A complete one-fuel raw tree can be admitted when its endpoints have
the selected authored type. Such a tree has no recursive premise, as proved
from the absence of zero-fuel derivations; the generic restriction then
retains its actual constructor and empty premise-position type. -/
noncomputable def admit_one_fuel_tree (relEnv : RelationEnv)
    (language : LanguageDef) (free : FreeTypeContext)
    (resultType : TypeExpr) (ambient : List TypeExpr)
    (source target : Pattern)
    (typed : EndpointsHaveType language free resultType
      ⟨1, ambient, source, target⟩)
    (tree : (SortIndexedScopedOperationalPresentation.presentation
      relEnv language).Derivation ()
      ⟨1, ambient, source, target⟩) :
    (presentation relEnv language free resultType).rules.Fix ()
      ⟨⟨1, ambient, source, target⟩, typed⟩ :=
  match tree with
  | .roll shape children =>
      nullaryTree (SortIndexedScopedFreeModel.authoredRules relEnv language)
        (fun _ judgment => EndpointsHaveType language free resultType judgment)
        () ⟨1, ambient, source, target⟩ typed shape
        (SortIndexedScopedFreeModel.one_fuel_shape_nullary
          relEnv language ambient source target shape children)

/-- The same base-case admission applies to a witnessed raw derivation. -/
theorem admit_one_fuel_nonempty (relEnv : RelationEnv)
    (language : LanguageDef) (free : FreeTypeContext)
    (resultType : TypeExpr) (ambient : List TypeExpr)
    (source target : Pattern)
    (typed : EndpointsHaveType language free resultType
      ⟨1, ambient, source, target⟩)
    (raw : Nonempty
      ((SortIndexedScopedOperationalPresentation.presentation
        relEnv language).Derivation ()
          ⟨1, ambient, source, target⟩)) :
    Nonempty ((presentation relEnv language free resultType).rules.Fix ()
      ⟨⟨1, ambient, source, target⟩, typed⟩) :=
  raw.map (admit_one_fuel_tree relEnv language free resultType ambient
    source target typed)

/-- The one-fuel admission map is a section of certificate erasure on
individual complete firing trees. It retains the exact raw constructor;
the child comparison is empty because a genuine one-fuel tree cannot have
recursive premises. -/
theorem admit_one_fuel_toRaw (relEnv : RelationEnv)
    (language : LanguageDef) (free : FreeTypeContext)
    (resultType : TypeExpr) (ambient : List TypeExpr)
    (source target : Pattern)
    (typed : EndpointsHaveType language free resultType
      ⟨1, ambient, source, target⟩)
    (tree : (SortIndexedScopedOperationalPresentation.presentation
      relEnv language).Derivation ()
      ⟨1, ambient, source, target⟩) :
    (toRawFree relEnv language free resultType).toFun ()
      ⟨⟨1, ambient, source, target⟩, typed⟩
      (admit_one_fuel_tree relEnv language free resultType ambient
        source target typed tree) = tree := by
  match tree with
  | .roll shape children =>
      change Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll shape _ =
        Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll shape children
      congr 1
      funext position
      exact (SortIndexedScopedFreeModel.one_fuel_shape_nullary
        relEnv language ambient source target shape children).false
        position |>.elim

#print axioms toRaw
#print axioms toRawFree
#print axioms toDepthFree_tree
#print axioms admitted_endpoints
#print axioms typedTreeEquiv
#print axioms admit_one_fuel_tree
#print axioms admit_one_fuel_nonempty
#print axioms admit_one_fuel_toRaw

end Mettapedia.OSLF.Binding.SortIndexedScopedTypingAdmission
