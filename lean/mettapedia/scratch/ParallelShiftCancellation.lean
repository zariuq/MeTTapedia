import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

/-!
# Pairwise shift-cancellation over a nonempty availability

Two bvar-containing bare-parallel payload abstracts, differing only in element
order, over one shared nonempty binder context with a genuinely shifting
thinning (a foreign target binder).  The endpoint composite of the
`parallelSide` conclusion — keyed two-depth canonicalization followed by
ambient thickening — is checked to agree on the pair even though the shift is
nontrivial, at two scope depths.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelShiftCancellation

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The wrapped process sort is not readable at the base colour. -/
theorem wrappedSort_rejected_at_base :
    decodeCostStaticTypeExpr rhoCIGSLT .base (.base costWrappedSortName) =
      none := by decide

/-- A genuinely shifting thinning: one foreign (wrapped-typed) target binder
above one mapped Name binder. -/
def foreignShiftThinning :
    CostStaticBinderThinning rhoCIGSLT .base
      [.base "Name"]
      (.base costWrappedSortName ::
        [mapTypeExpr (CostStaticColor.symbols rhoCIGSLT .base) (.base "Name")]) :=
  .foreign (.base costWrappedSortName) wrappedSort_rejected_at_base
    (.mapped (.base "Name") .nil)

/-- **The shift is nontrivial**: the ambient source index 0 lands at target
index 1.  (This also completes the refutation core for the one-endpoint
restore-to-payload-normal statement at nonempty availability: the frame side
moves the bvar, the payload's own normal does not.) -/
theorem ambientShift_nontrivial :
    foreignShiftThinning.thickenAmbientBVars 0 (.bvar 0) = .bvar 1 := by
  simp [foreignShiftThinning, CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticBinderThinning.embedIndexAt,
    CostStaticBinderThinning.toTargetIndex]

theorem ambientShift_nontrivial_ne :
    foreignShiftThinning.thickenAmbientBVars 0 (.bvar 0) ≠ .bvar 0 := by
  simp [foreignShiftThinning, CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticBinderThinning.embedIndexAt,
    CostStaticBinderThinning.toTargetIndex]

/-- Left payload abstract: a bare parallel with an ambient bvar and a leaf
name, in one order. -/
def leftParallelAbstract : Pattern :=
  .collection .hashBag [.bvar 0, .fvar "a"] none

/-- Right payload abstract: the same bag in the opposite order. -/
def rightParallelAbstract : Pattern :=
  .collection .hashBag [.fvar "a", .bvar 0] none

/-- The endpoint composite of the parallelSide conclusion, at one shared key. -/
def endpointComposite (scopeDepth : Nat) (pattern : Pattern) : Pattern :=
  foreignShiftThinning.thickenAmbientBVars scopeDepth
    (canonicalizeByDepths
      (fun _ _ => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode)
      rhoReflectivePresentation.toReflectivePresentationDecl 3 scopeDepth
      pattern)

/-- The keyed canonical form of both bags, at scope depth 0: sorting is by
the shared key, so the two orders land on one list. -/
theorem canonicalLeft_depth0 :
    canonicalizeByDepths
        (fun _ _ => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode)
        rhoReflectivePresentation.toReflectivePresentationDecl 3 0
        leftParallelAbstract =
      .collection .hashBag [.bvar 0, .fvar "a"] none := by
  simp [leftParallelAbstract, rightParallelAbstract, canonicalizeByDepths,
    canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    List.mergeSort, List.merge,
    rhoReflectivePresentation]
  decide

theorem canonicalRight_depth0 :
    canonicalizeByDepths
        (fun _ _ => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode)
        rhoReflectivePresentation.toReflectivePresentationDecl 3 0
        rightParallelAbstract =
      .collection .hashBag [.bvar 0, .fvar "a"] none := by
  simp [leftParallelAbstract, rightParallelAbstract, canonicalizeByDepths,
    canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    List.mergeSort, List.merge,
    rhoReflectivePresentation]
  decide

/-- **Pairwise shift-cancellation, scope depth 0**: the differently-ordered
bvar-containing parallels have literally equal endpoint composites through
the nontrivial shift — the keyed sort lands both on one list, and one shared
thinning then acts once. -/
theorem endpointComposite_pair_eq_depth0 :
    endpointComposite 0 leftParallelAbstract =
      endpointComposite 0 rightParallelAbstract := by
  unfold endpointComposite
  rw [canonicalLeft_depth0, canonicalRight_depth0]

theorem canonicalLeft_depth1 :
    canonicalizeByDepths
        (fun _ _ => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode)
        rhoReflectivePresentation.toReflectivePresentationDecl 3 1
        leftParallelAbstract =
      .collection .hashBag [.bvar 0, .fvar "a"] none := by
  simp [leftParallelAbstract, rightParallelAbstract, canonicalizeByDepths,
    canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    List.mergeSort, List.merge,
    rhoReflectivePresentation]
  decide

theorem canonicalRight_depth1 :
    canonicalizeByDepths
        (fun _ _ => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode)
        rhoReflectivePresentation.toReflectivePresentationDecl 3 1
        rightParallelAbstract =
      .collection .hashBag [.bvar 0, .fvar "a"] none := by
  simp [leftParallelAbstract, rightParallelAbstract, canonicalizeByDepths,
    canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    List.mergeSort, List.merge,
    rhoReflectivePresentation]
  decide

/-- The same cancellation at scope depth 1, where the bvar is scoped rather
than ambient. -/
theorem endpointComposite_pair_eq_depth1 :
    endpointComposite 1 leftParallelAbstract =
      endpointComposite 1 rightParallelAbstract := by
  unfold endpointComposite
  rw [canonicalLeft_depth1, canonicalRight_depth1]

/-- The depth-0 value, explicitly: the bag survives with the ambient bvar
shifted past the foreign binder. -/
theorem endpointComposite_value_depth0 :
    endpointComposite 0 leftParallelAbstract =
      .collection .hashBag [.bvar 1, .fvar "a"] none := by
  unfold endpointComposite
  rw [canonicalLeft_depth0]
  simp [foreignShiftThinning, CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticBinderThinning.embedIndexAt,
    CostStaticBinderThinning.toTargetIndex]

end ParallelShiftCancellation
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
