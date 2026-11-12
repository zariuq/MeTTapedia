import Mettapedia.Languages.MeTTa.PeTTa.ConstructorRealization

/-!
# Completed constructor schedules under arbitrary source callers

The two actual paths reach the same full return configuration. Their finite
administrative allowances can differ, but every subsequent runner allowance
has identical observations, including faults, suspension and effects in the
caller. This does not identify the cutoffs at equal initial fuel or claim
reflection of arbitrary unfinished operand schedules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation

open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Unifying

theorem Items.continuations {registry : SpaceSemantics.Program} {before after : Configuration}
    {bindings : Subst} {expressions : List Atom} {values : List Values}
    (source : Items registry before bindings expressions after values) (valid : Idempotent bindings)
    (frames : List Frame) :
    ∃ directWork expandedWork, ∀ remaining,
      run registry (directWork + remaining)
          {before with control := .arguments bindings .data expressions [] 0,frames} =
        run registry (expandedWork + remaining)
          {before with control := .evaluate bindings (ConstructorSpine.build expressions),frames} := by
  have paths := source.exact_return_boundaries valid frames
  obtain ⟨directWork,direct⟩ := steps_run_suffix paths.1
  obtain ⟨expandedWork,expanded⟩ := steps_run_suffix paths.2
  exact ⟨directWork,expandedWork,fun remaining =>
    (direct remaining).trans (expanded remaining).symm⟩

end Mettapedia.Languages.MeTTa.PeTTa.ConstructorEvaluation
