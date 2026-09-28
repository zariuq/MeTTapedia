import Mettapedia.OSLF.Syntax.CartesianTreeLiftCriterion
import Mettapedia.OSLF.Syntax.ResultSortedScopedHistory

/-!
# Exact local admission of result-sorted firing trees

The result-sorted rule polynomial is a cartesian refinement of the authored
raw operational polynomial. Its local lifting criterion checks a result sort,
endpoint typing, canonical ordered child sorts, and the same criterion at
every recursive premise. This is the precise property an executor soundness
theorem must establish; declaration compilation alone supplies only the
canonical child-sort portion.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ResultSortedScopedTreeLiftCriterion

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext HasType)
open Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ResultSortedScopedHistory
open Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.CartesianTreeLiftCriterion

/-- Each raw constructor and its recursively selected child trees have
the author's required result-sort and endpoint typing certificates. The
predicate examines constructor positions, so equal child endpoints do not
merge distinct selected firings. -/
def LocallyResultSorted (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext)
    (judgment : ResultSortedScopedOperationalPresentation.Judgment)
    (tree : (SortIndexedScopedOperationalPresentation.presentation relEnv
      lang).Derivation () judgment.eraseResult) : Prop :=
  LocalTreeLift (erasePolynomialMap relEnv lang free) () judgment tree

/-- Local result-sort certification is equivalent to an actual typed tree
whose cartesian erasure is exactly the selected raw tree. -/
theorem locallyResultSorted_iff_exact_lift
    (relEnv : RelationEnv) (lang : LanguageDef) (free : FreeTypeContext)
    (judgment : ResultSortedScopedOperationalPresentation.Judgment)
    (tree : (SortIndexedScopedOperationalPresentation.presentation relEnv
      lang).Derivation () judgment.eraseResult) :
    LocallyResultSorted relEnv lang free judgment tree ↔
      ∃ sorted : (ResultSortedScopedOperationalPresentation.presentation
        relEnv lang free).Derivation () judgment,
        (erasePolynomialMap relEnv lang free).mapFix () judgment sorted =
          tree :=
  liftable_iff_exists (erasePolynomialMap relEnv lang free) () judgment tree

/-- An exact local certificate retains the original raw firing tree and
its depth-indexed decoder result. In particular, it cannot exchange two
premise histories with equal endpoint judgments. -/
theorem locallyResultSorted_preserves_history
    (relEnv : RelationEnv) (lang : LanguageDef) (free : FreeTypeContext)
    (judgment : ResultSortedScopedOperationalPresentation.Judgment)
    (tree : (SortIndexedScopedOperationalPresentation.presentation relEnv
      lang).Derivation () judgment.eraseResult)
    (certified : LocallyResultSorted relEnv lang free judgment tree) :
    ∃ sorted : (ResultSortedScopedOperationalPresentation.presentation
        relEnv lang free).Derivation () judgment,
      (erasePolynomialMap relEnv lang free).mapFix () judgment sorted = tree ∧
        decodeSorted? relEnv lang free judgment sorted =
          Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
            relEnv lang judgment.eraseResult.depth
            ((depthPolynomialMap relEnv lang).mapFix ()
              judgment.eraseResult tree) := by
  obtain ⟨sorted, erases⟩ :=
    (locallyResultSorted_iff_exact_lift relEnv lang free judgment tree).mp
      certified
  refine ⟨sorted, erases, ?_⟩
  rw [decodeSorted_eq_mapFix]
  rw [show eraseToDepthMap relEnv lang free =
      Hom.comp (erasePolynomialMap relEnv lang free)
        (depthPolynomialMap relEnv lang) from rfl]
  rw [Hom.mapFix_comp, erases]

#print axioms locallyResultSorted_iff_exact_lift
#print axioms locallyResultSorted_preserves_history

end Mettapedia.OSLF.Binding.ResultSortedScopedTreeLiftCriterion
