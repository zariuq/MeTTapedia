import Mettapedia.OSLF.Syntax.CartesianAdmissionTransport
import Mettapedia.OSLF.Syntax.ResultSortedScopedFreeModel

/-!
# Every node of an erased result-sorted firing remains typed

The authored source tree records a potentially different result sort at each
recursive premise. Complete trees, rather than isolated parent shapes, carry
all endpoint typing evidence through the cartesian sort erasure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ResultSortedScopedAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext HasType)
open Mettapedia.OSLF.Binding.AdmittedJudgmentRulePresentation
open Mettapedia.OSLF.Binding.CartesianAdmissionTransport
open Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel

/-- A raw sort-context judgment admits some common authored endpoint sort.
The selected sort remains explicit in the result-sorted source tree. -/
def SomeEndpointsHaveType (language : LanguageDef)
    (free : FreeTypeContext)
    (judgment : SortIndexedScopedOperationalPresentation.Judgment) : Prop :=
  ∃ resultType,
    HasType language free judgment.ambient judgment.source resultType ∧
    HasType language free judgment.ambient judgment.target resultType

/-- Every node of the erased result-sorted tree has authored endpoint
typing, possibly at a different result sort from its parent. The proof
recurses over complete trees; the parent shape alone does not certify the
premise results. -/
theorem eraseTree_allNodesHaveType
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext)
    (judgment : ResultSortedScopedOperationalPresentation.Judgment)
    (tree : (presentation relEnv language free).Derivation () judgment) :
    AllNodesAdmitted
      (SortIndexedScopedFreeModel.authoredRules relEnv language)
      (fun _ child => SomeEndpointsHaveType language free child)
      () judgment.eraseResult
      ((toContextSortedFree relEnv language free).toFun () judgment tree) := by
  change AllNodesAdmitted
    (⟨fun _ => SortIndexedScopedOperationalPresentation.Judgment,
      (SortIndexedScopedOperationalPresentation.presentation relEnv language).polynomial⟩ :
        IndexedRulePresentationCategory.Presentation Unit)
    (fun _ child => SomeEndpointsHaveType language free child)
      () judgment.eraseResult
      ((erasePolynomialMap relEnv language free).mapFix () judgment tree)
  apply mapFix_allNodesAdmitted
    (erasePolynomialMap relEnv language free)
    (fun _ child => SomeEndpointsHaveType language free child)
  intro _ index shape
  cases index with
  | mk fuel ambient resultType source target =>
      cases fuel with
      | zero => cases shape
      | succ fuel =>
          exact ⟨resultType, shape.sourceTyped, shape.targetTyped⟩

#print axioms eraseTree_allNodesHaveType

end Mettapedia.OSLF.Binding.ResultSortedScopedAdmission
