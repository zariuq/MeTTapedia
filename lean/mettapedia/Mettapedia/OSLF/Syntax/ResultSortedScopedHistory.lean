import Mettapedia.OSLF.Syntax.ResultSortedScopedFreeModel
import Mettapedia.OSLF.Syntax.SortIndexedScopedFreeModel
import Mettapedia.OSLF.Syntax.ScopedOperationalHistory

/-!
# Reading selected histories through result-sort erasure

The canonically result-sorted rule polynomial retains each raw rule label
and an equivalent position for every recursive premise. Decoding after the
two cartesian erasures therefore obeys the same constructor equation as the
raw history decoder. This is a positional law: equal child endpoints do not
permit exchanging their distinct firing witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ResultSortedScopedHistory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel
open Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.SortIndexedScopedFreeModel
open Mettapedia.OSLF.Binding.ScopedOperationalHistory
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms

/-- Decode a sorted firing tree by forgetting its result sorts and binder
sort names, then reading the retained authored rule and premise events. -/
noncomputable def decodeSorted? (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext)
    (judgment : ResultSortedScopedOperationalPresentation.Judgment)
    (tree : (presentation relEnv lang free).Derivation () judgment) :
    Option Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.RuleHistory :=
  decodeHistory? relEnv lang judgment.eraseResult.depth
    ((toDepthFreeModel relEnv lang).toFun () judgment.eraseResult
      ((toContextSortedFree relEnv lang free).toFun () judgment tree))

private theorem decodeHistory_cast (relEnv : RelationEnv) (lang : LanguageDef)
    {i j : Mettapedia.OSLF.Binding.ScopedOperationalPresentation.Judgment}
    (same : i = j)
    (tree : (Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
      relEnv lang).Derivation () i) :
    decodeHistory? relEnv lang j (same ▸ tree) =
      decodeHistory? relEnv lang i tree := by
  cases same
  rfl

/-- The composite cartesian map from fully result-sorted constructors to
the depth-indexed operational presentation. -/
def eraseToDepthMap (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) :
    Hom (presentation relEnv lang free).polynomial
      (Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
        relEnv lang).polynomial
      (fun _ judgment => judgment.eraseResult.depth) :=
  Hom.comp (erasePolynomialMap relEnv lang free)
    (depthPolynomialMap relEnv lang)

/-- The categorical free-model erasure agrees with recursive action of
the composite polynomial map on the same complete firing tree. -/
theorem decodeSorted_eq_mapFix (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext)
    (judgment : ResultSortedScopedOperationalPresentation.Judgment)
    (tree : (presentation relEnv lang free).Derivation () judgment) :
    decodeSorted? relEnv lang free judgment tree =
      decodeHistory? relEnv lang judgment.eraseResult.depth
        ((eraseToDepthMap relEnv lang free).mapFix () judgment tree) := by
  unfold decodeSorted? eraseToDepthMap
  rw [Hom.mapFix_comp]
  rfl

/-- A sorted constructor decodes by decoding each child in its exact
transported premise position and applying the original raw rule decoder. -/
theorem decodeSorted_roll (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext)
    (judgment : ResultSortedScopedOperationalPresentation.Judgment)
    (shape : (presentation relEnv lang free).polynomial.Shape () judgment)
    (children : (position :
      (presentation relEnv lang free).polynomial.Position shape) →
        (presentation relEnv lang free).Derivation ()
          ((presentation relEnv lang free).polynomial.next shape position)) :
    decodeSorted? relEnv lang free judgment
        (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll shape children) =
      decodeLayer relEnv lang judgment.eraseResult.depth
        ((eraseToDepthMap relEnv lang free).onShape () judgment shape)
        (fun position =>
          decodeSorted? relEnv lang free
            ((presentation relEnv lang free).polynomial.next shape
              ((eraseToDepthMap relEnv lang free).onPosition () judgment shape position))
            (children ((eraseToDepthMap relEnv lang free).onPosition () judgment shape position))) := by
  rw [decodeSorted_eq_mapFix]
  let h := eraseToDepthMap relEnv lang free
  change decodeHistory? relEnv lang judgment.eraseResult.depth
    (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
      (h.onShape () judgment shape)
      (fun position =>
        (h.onNext () judgment shape position).symm ▸
          h.mapFix () _ (children (h.onPosition () judgment shape position)))) = _
  rw [decodeHistory?_roll]
  congr 1
  funext position
  rw [decodeHistory_cast]
  exact (decodeSorted_eq_mapFix relEnv lang free
    ((presentation relEnv lang free).polynomial.next shape
      (h.onPosition () judgment shape position))
    (children (h.onPosition () judgment shape position))).symm

#print axioms decodeHistory_cast
#print axioms decodeSorted_eq_mapFix
#print axioms decodeSorted_roll

end Mettapedia.OSLF.Binding.ResultSortedScopedHistory
