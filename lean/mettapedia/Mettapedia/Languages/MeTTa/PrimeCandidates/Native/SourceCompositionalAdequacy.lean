import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSource
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceComposition
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceOrdered

/-!
# Source composition at the shared-return candidate boundary

The source language and its three argument profiles are independently defined
by `CallTimeChoiceSource`. The target is the existing shared-return execution
machine, including retained histories. The comparison preserves ordered
outcomes, multiplicity and each branch's event trace; cell identities are
related by `ObservationRel`, not asserted to be the same representation.

This profile has first-order equation calls and de Bruijn argument binding.
It does not specify named crossings, external transactional effects, changing
equation revisions, or the whole Prime surface language. Those require their
own execution owners and a further integration theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceCompositionalAdequacy

open Mettapedia.Machines.BranchLocalNeed
open CallTimeChoice

/-- The actual candidate execution realizes each independently specified
source observation, retaining its ordered effects. -/
theorem preservation {profile : Profile} {program : SProgram} {expression : Expr}
    {results : List Result} (source : SourceObserves profile program expression results) :
    ∃ steps observations,
      SharedFinished (program.toCore profile) (expression.toCore profile id) steps true ∧
      sharedObservations (program.toCore profile) steps (expression.toCore profile id) =
        some observations ∧ List.Forall₂ ObservationRel results observations :=
  shared_observations_forward source

/-- Completion is required: an unfinished frontier is not an empty source
answer. Every actual completed target run has a source execution. -/
theorem no_invention {profile : Profile} {program : SProgram} {expression : Expr}
    {steps : Nat}
    (finished : SharedFinished (program.toCore profile)
      (expression.toCore profile id) steps true) :
    ∃ results observations, SourceObserves profile program expression results ∧
      sharedObservations (program.toCore profile) steps (expression.toCore profile id) =
        some observations ∧ List.Forall₂ ObservationRel results observations :=
  shared_observations_backward finished

/-- A nonterminating source cannot acquire a spurious completed candidate
execution. Conversely, finite source observation is enough for completion. -/
theorem completion_iff (profile : Profile) (program : SProgram) (expression : Expr)
    (keepReceipts : Bool) :
    (∃ results, SourceObserves profile program expression results) ↔
      ∃ steps, SharedFinished (program.toCore profile)
        (expression.toCore profile id) steps keepReceipts :=
  observes_iff_shared_finishes _ _ keepReceipts

/-- Exact active-context replacement composes with the candidate execution.
The common intermediate observation still includes the full branch stores. -/
theorem contextual_preservation {program : Program} {left right : Comp}
    (same : Composition.Equivalent (observed program) left right)
    (context : Composition.ActiveContext) {results : List Result}
    (source : Observes program (context.plug left) results) :
    ∃ steps observations, SharedFinished program (context.plug right) steps true ∧
      sharedObservations program steps (context.plug right) = some observations ∧
      List.Forall₂ ObservationRel results observations :=
  shared_observations_forward (((same.context context).observes results).mp source)

/-- Composition does not add completed executions either. -/
theorem contextual_no_invention {program : Program} {left right : Comp}
    (same : Composition.Equivalent (observed program) left right)
    (context : Composition.ActiveContext) {steps : Nat}
    (finished : SharedFinished program (context.plug right) steps true) :
    ∃ results observations, Observes program (context.plug left) results ∧
      sharedObservations program steps (context.plug right) = some observations ∧
      List.Forall₂ ObservationRel results observations := by
  obtain ⟨results, observations, source, readback, related⟩ :=
    shared_observations_backward finished
  exact ⟨results, observations, ((same.context context).observes results).mpr source,
    readback, related⟩

/-- Every finite pause has a source-reference prefix, with bounded
administrative overhead. This does not assume source termination. -/
theorem pause_reflection (profile : Profile) (program : SProgram) (expression : Expr)
    (steps : Nat) :
    ∃ count ≤ steps,
      (¬ SharedFinished (program.toCore profile) (expression.toCore profile id) steps true →
        steps ≤ 2 * count + 1) ∧
      sharedReadback (program.toCore profile) steps (expression.toCore profile id) =
        some (((orderedMachine (program.toCore profile)).expandFirst)^[count]
          [initialMachine (observe (expression.toCore profile id))]) :=
  shared_readback_prefix _ _ steps

/-- Every finite source-reference prefix has an actual target prefix. -/
theorem pause_realization (profile : Profile) (program : SProgram) (expression : Expr)
    (count : Nat) :
    ∃ steps ≤ 2 * count,
      sharedReadback (program.toCore profile) steps (expression.toCore profile id) =
        some (((orderedMachine (program.toCore profile)).expandFirst)^[count]
          [initialMachine (observe (expression.toCore profile id))]) :=
  shared_recorded_prefix_realization _ _ count

/-- The source compiler reserves normalization's head, so repeated consumer
preparation cannot create or destroy completion under any argument profile. -/
theorem preparation_completion_iff (profile : Profile) (program : SProgram)
    (expression : Expr) (keepReceipts : Bool) :
    (∃ steps, SharedFinished (program.toCore profile)
      (normalized (expression.toCore profile id)) steps keepReceipts) ↔
    (∃ steps, SharedFinished (program.toCore profile)
      (expression.toCore profile id) steps keepReceipts) :=
  shared_normalization_completion_iff _ (program.toCore_reserved profile) _ keepReceipts

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceCompositionalAdequacy
