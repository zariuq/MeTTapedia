import Mettapedia.GSLT.Core.OperationalReadbackAccounts

/-!
# Controls for phase readback and allowed observations

The existing two-instruction lowering supplies a nontrivial readback. Its
first instruction commits the source transition; the second completes the
implementation. The existing block account pays for both instructions.
Commitment is an aligned observation. Inspecting whether the second
instruction has already finished is not aligned, even though the compiler
has exact canonical endpoints and a valid operational correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.LoweringCanary

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open OperationalRealization

/-- Commitment is recorded before the implementation's final instruction. -/
def sourceView : target.Term → FusionCanary.source.Term
  | TargetState.start => false
  | TargetState.middle => true
  | TargetState.finish => true

def correspondence : OperationalCorrespondence FusionCanary.source target where
  related origin current := origin = sourceView current
  readStep := by
    intro origin current next related step
    cases step with
    | first => exact .inr ⟨true, ⟨related, rfl⟩, rfl⟩
    | second => exact .inl related
  forward := by
    rintro origin after current related ⟨before, finished⟩
    subst origin
    subst after
    cases current with
    | start =>
        exact ⟨TargetState.finish,
          ⟨.cons ⟨TargetStep.first⟩ (.cons ⟨TargetStep.second⟩ (.refl TargetState.finish))⟩, rfl⟩
    | middle => cases before
    | finish => cases before

def phasePotential : FusionCanary.source.Term → target.Term → Nat
  | _, TargetState.start => 0
  | _, TargetState.middle => 1
  | _, TargetState.finish => 0

/-- The actual readback is accounted using the original forward block
account, rather than a newly defined notion of cost. -/
def readbackAccount : correspondence.toOperationalReadback.Account where
  sourceAccount := lowering.blockAccount
  potential := phasePotential
  readStep := by
    intro origin current next related step
    cases step with
    | first =>
        have before : origin = false := related
        cases before
        refine .inr ⟨true, FusionCanary.source_step, rfl, ?_⟩
        have counted : Multiplicative.toAdd
            (lowering.blockAccount.of (.cons ⟨FusionCanary.source_step⟩ (.refl true))) = 2 := by
          change ((lowering.mapStep FusionCanary.source_step).append
            (.refl (lowering.mapTerm true))).length = 2
          simpa only [Route.length_append, Route.length, Nat.add_zero] using
            lowering_uses_two_target_steps
        simpa only [phasePotential, Nat.zero_add] using Nat.le_of_eq counted.symm
    | second => exact .inl ⟨related, le_rfl⟩

theorem compiled_boundary_related (origin : FusionCanary.source.Term) :
    correspondence.related origin (lowering.mapTerm origin) := by
  cases origin <;> rfl

theorem first_instruction_commits :
    correspondence.related true TargetState.middle ∧
      ¬ correspondence.related false TargetState.middle := by
  exact ⟨rfl, Bool.false_ne_true⟩

theorem pending_instruction_is_administrative :
    correspondence.related true TargetState.middle ∧
      target.Step TargetState.middle TargetState.finish ∧
      correspondence.related true TargetState.finish :=
  ⟨rfl, TargetStep.second, rfl⟩

/-- Every supplied target prefix has a retained source prefix whose existing
block account bounds its instruction count. -/
theorem every_prefix_accounted {origin : FusionCanary.source.Term}
    {final : target.Term}
    (path : ExecutionPath target (lowering.mapTerm origin) final) :
    ∃ after, ∃ sourcePath : ExecutionPath FusionCanary.source origin after,
      correspondence.related after final ∧ sourcePath.length ≤ path.length ∧
        path.length ≤ Multiplicative.toAdd (lowering.blockAccount.of sourcePath) := by
  obtain ⟨after, sourcePath, related, shorter, bounded⟩ :=
    readbackAccount.reflectPath_length_bound (compiled_boundary_related origin) path
  refine ⟨after, sourcePath, related, shorter, ?_⟩
  have initial : phasePotential origin (lowering.mapTerm origin) = 0 := by
    cases origin <;> rfl
  change path.length ≤ phasePotential origin (lowering.mapTerm origin) +
    Multiplicative.toAdd (lowering.blockAccount.of sourcePath) at bounded
  simpa only [initial, Nat.zero_add] using bounded

/-- Aligned commitment observations reach the same source and target
prefixes, through the actual comparison law. -/
theorem commitment_reachable_iff (origin : FusionCanary.source.Term) :
    (∃ after, FusionCanary.source.MultiStep origin after ∧ after = true) ↔
      ∃ final, target.MultiStep (lowering.mapTerm origin) final ∧ sourceView final = true := by
  exact correspondence.reachable_iff (fun after => after = true)
    (fun final => sourceView final = true)
    (fun related => related ▸ Iff.rfl) (compiled_boundary_related origin)

/-- Even an exact compiler boundary does not make raw implementation-phase
inspection an aligned source observation. -/
theorem finish_inspection_not_aligned :
    ¬ (∀ {origin current}, correspondence.related origin current →
      (origin = true ↔ current = TargetState.finish)) := by
  intro aligned
  have impossible := (aligned (origin := true) (current := TargetState.middle) rfl).1 rfl
  cases impossible

/-- The actual second instruction realizes completion from a committed
phase. Inspection is delayed, so its reachability still agrees with the
source, despite the failed instantaneous comparison above. -/
theorem completion_reachable_iff (origin : FusionCanary.source.Term) :
    (∃ after, FusionCanary.source.MultiStep origin after ∧ after = true) ↔
      ∃ final, target.MultiStep (lowering.mapTerm origin) final ∧
        final = TargetState.finish := by
  apply correspondence.reachable_iff_delayed (fun after => after = true)
    (fun final => final = TargetState.finish)
    (fun related completed => by simpa only [correspondence, completed, sourceView] using related)
  · intro origin current related completed
    cases current with
    | start => cases completed; cases related
    | middle =>
        exact ⟨TargetState.finish,
          executionPathToMultiStep (.cons ⟨TargetStep.second⟩ (.refl TargetState.finish)), rfl⟩
    | finish => exact ⟨TargetState.finish, .refl _, rfl⟩
  · exact compiled_boundary_related origin

/-- Counting primitive instructions is not invariant under this compiler. -/
theorem implementation_count_differs :
    (lowering.mapStep FusionCanary.source_step).length = 2 ∧
      ((Route.cons ⟨FusionCanary.source_step⟩ (Route.refl true)) :
        ExecutionPath FusionCanary.source false true).length = 1 := by
  exact ⟨lowering_uses_two_target_steps, rfl⟩

end Mettapedia.GSLT.IndexedOperational.LoweringCanary
