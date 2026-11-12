import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreInterchange

/-!
# The binding-aware helper step has the plain reading

The helper step lives over the declaration frames with contextual assignments: a firing makes a
fresh helper, extends the frame by it and is guarded by equations on the old names. Its guard is
an entailment from knowledge, and a placement only adds knowledge. So admission is stable under
placement: the grade of every run is its structural part, a solvable joint knowledge and a fresh
helper identity.

* `helper_stable`: admission of the helper step is stable under placement.
* `helper_checks_iff_fits`: the grade of every helper run is its structural part.
* `helper_placed_run_iff_fits`: a helper run has a placed native run exactly where it fits.

This is the instance over more than one frame of the reading in `KnowledgeTensorCore`; the
first-order step is the instance whose absence and counting checks make the grade proper.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs

variable {S : Signature} {O : Type} [DecidableEq O]

/-- **Admission of the binding-aware helper step is stable under placement.** -/
theorem helper_stable : Stable (Helpers.contextualRunInterpretation (S := S) (O := O)) := by
  intro left right placed f allowed _ prepared
  refine (placed.admitted_left_iff f allowed).mpr ⟨?_, ?_⟩
  · obtain ⟨target, σ, solved⟩ := prepared.2.2
    exact ⟨target, _, Step.models_knowledge Helpers.helperStep.toStep _ σ solved⟩
  · intro inRight
    exact Finset.disjoint_left.mp prepared.2.1.fresh
      (List.mem_toFinset.mpr (List.mem_singleton.mpr rfl)) (Finset.mem_union_right _ inRight)

/-- **The grade of every helper run is its structural part.** -/
theorem helper_checks_iff_fits {left right : Helpers.State S O}
    (placed : Helpers.ContextPlacement left right) (run : Helpers.helperStep.Run left) :
    Helpers.contextualRunInterpretation.Checks placed run ↔
      Fits Helpers.contextualRunInterpretation placed run :=
  ⟨fits_of_checks Helpers.contextualRunInterpretation placed run,
    (stable_iff_fits_implies_checks Helpers.contextualRunInterpretation).mp helper_stable placed run⟩

/-- **A helper run has a placed native run exactly where it fits.** -/
theorem helper_placed_run_iff_fits {left right : Helpers.State S O}
    (placed : Helpers.ContextPlacement left right) (run : Helpers.helperStep.Run left) :
    (∃ native : Helpers.helperStep.Run placed.state,
      Places Helpers.contextualRunInterpretation placed run native) ↔
      Fits Helpers.contextualRunInterpretation placed run :=
  (exists_places_iff_checks Helpers.contextualRunInterpretation placed run).trans
    (helper_checks_iff_fits placed run)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
