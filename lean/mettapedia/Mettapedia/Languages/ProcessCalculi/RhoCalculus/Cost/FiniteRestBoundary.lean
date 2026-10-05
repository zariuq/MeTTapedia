import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteWhole

/-!
# A retained collection rest crosses the finite Cost sort boundary

The selected funded rule captures the unmatched parallel remainder inside
its base redex. Its contractum inserts that same remainder into a wrapped
parallel collection. Ordinary schema typing does not type collection-rest
metavariables, so the validated schema does not justify this change of sort.

The actual admitted reflective runtime below fires on a well-sorted source
with one unmatched base zero and produces a result that is not well sorted.
This is a boundary of the current generated rule, not an alternative
execution semantics or a weakened typing judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.FiniteRestBoundary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveEngine
open FiniteWhole

def source : Pattern := .apply costContactConstructorName
  [.apply costSignedConstructorName
    [.collection .hashBag
      [.apply (costBaseConstructorName "PInput") [expandedChannel, .lambda none localBody],
       .apply (costBaseConstructorName "POutputK") [canonicalChannel, zero, afterOutput],
       baseZero] none, unitSignature],
    .apply costFundingConstructorName
      [.apply costTokenStackConsConstructorName [unitSignature, retainedTail]]]

def target : Pattern := .apply costContactConstructorName
  [.collection .hashBag [zero, afterOutput, baseZero] none,
    .apply costFundingConstructorName [retainedTail]]

theorem source_typed : HasSort presentation.core.language FreeTypeContext.empty []
    source costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem actual_reducts : rewriteStepWithReflection presentation.reflection.1
    presentation.core.language source = [target] := by
  decide +kernel

theorem target_not_typed : ¬ HasSort presentation.core.language FreeTypeContext.empty []
    target costWrappedSortName := by
  intro typed
  have checked := checkHasType_complete_of_object typed (by decide +kernel)
  have rejected : checkHasType presentation.core.language FreeTypeContext.empty []
      target (.base costWrappedSortName) = false := by decide +kernel
  rw [rejected] at checked
  contradiction

/-- The desired unrestricted subject-reduction statement for this actual
generated language and runtime is false. -/
theorem not_unrestricted_reflective_subject_reduction :
    ¬ (∀ left right,
      HasSort presentation.core.language FreeTypeContext.empty [] left costWrappedSortName →
      right ∈ rewriteStepWithReflection presentation.reflection.1 presentation.core.language left →
      HasSort presentation.core.language FreeTypeContext.empty [] right costWrappedSortName) := by
  intro preserves
  exact target_not_typed (preserves source target source_typed
    (by rw [actual_reducts]; exact List.mem_singleton_self _))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.FiniteRestBoundary
