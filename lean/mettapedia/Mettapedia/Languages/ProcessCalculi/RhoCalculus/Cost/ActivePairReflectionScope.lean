import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairScoped

/-!
# Ambient scope boundary of the reflected active pair

The existing reflected substitution is the source's closed, quote-aware
operation. It does not remove a de Bruijn position from an arbitrary ambient
context. The scoped interpreter does remove that position. Their distinct
results below prevent using the scoped typing theorem as a subject-reduction
theorem for the reflected interpreter on arbitrary open patterns.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairReflectionScope

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveEngine

def reflectedTarget : Pattern := .apply costContactConstructorName
  [.collection .hashBag
    [.collection .hashBag
      [FiniteWhole.zero, .apply (costWrappedConstructorName "PDrop") [.bvar 1]] none,
     FiniteWhole.zero] none,
   .apply costFundingConstructorName [FiniteWhole.retainedTail]]

/-- The checked reflective engine fires on the same locally typed open
source used by the scoped activation theorem. -/
theorem actual_reflective_reducts : rewriteStepWithReflection
    ActivePair.presentation.reflection.1 ActivePair.language ActivePair.openSource =
    [reflectedTarget] := by decide +kernel

/-- The surviving ambient index has not been lowered after input-binder
elimination, so it lies outside the caller's one-name context. -/
theorem reflected_target_not_typed :
    ¬ HasSort ActivePair.language FreeTypeContext.empty
      [.base (costBaseSortName "Name")] reflectedTarget costWrappedSortName := by
  intro typed
  have inScope := typed.isWellScopedAt
  have rejected : reflectedTarget.isWellScopedAt 1 = false := by decide +kernel
  change reflectedTarget.isWellScopedAt 1 = true at inScope
  rw [rejected] at inScope
  contradiction

/-- Scoped activation has its established typed result on this very source;
the reflective result cannot be substituted for that result. -/
theorem scoped_reflective_results_differ :
    HasSort ActivePair.language FreeTypeContext.empty
      [.base (costBaseSortName "Name")] ActivePair.openTarget costWrappedSortName ∧
    ActivePair.openTarget ≠ reflectedTarget := by
  exact ⟨ActivePair.open_target_typed, by decide +kernel⟩

/-- The actual reflected interpreter does not preserve arbitrary-ambient
typing, even after removing the unmatched internal collection rest. -/
theorem not_open_reflective_subject_reduction :
    ¬ (∀ ambient left right,
      HasSort ActivePair.language FreeTypeContext.empty ambient left costWrappedSortName →
      right ∈ rewriteStepWithReflection ActivePair.presentation.reflection.1
        ActivePair.language left →
      HasSort ActivePair.language FreeTypeContext.empty ambient right costWrappedSortName) := by
  intro preserves
  exact reflected_target_not_typed
    (preserves [.base (costBaseSortName "Name")] ActivePair.openSource reflectedTarget
      ActivePair.open_source_typed
      (by rw [actual_reflective_reducts]; exact List.mem_singleton_self _))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairReflectionScope
