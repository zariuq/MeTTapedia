import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Progress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Controls.PositiveBlocks
import Mettapedia.GSLT.Core.OperationalReadbackControls

/-!
# Progress survives staged lowering with initialization

The existing two-instruction implementation supplies the first progress
certificate. A second implementation performs an initialization step before
running those instructions. Both have actual administrative transitions. Their
composed readback preserves normalization through the intermediate phase.

The spinning implementation has positive forward blocks but admits no progress
certificate, regardless of the well-founded rank type chosen for it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Progress

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open LoweringCanary

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Progress

universe uRank

/-- The pending second instruction has rank one; commitment may reset the rank. -/
def loweringProgress : Certificate correspondence.toOperationalReadback :=
  Certificate.ofNat phasePotential (by
    intro origin current next related step
    cases step with
    | first => exact .inr ⟨true, ⟨related, rfl⟩, rfl⟩
    | second => exact .inl ⟨related, by change 0 < 1; decide⟩)

theorem real_step_resets_rank :
    phasePotential false TargetState.start = 0 ∧
      phasePotential true TargetState.middle = 1 := by decide

theorem lowering_normalizes : Acc (fun next state => target.Step state next) TargetState.start :=
  loweringProgress.normalization_preserved PositiveBlocks.source_normalizes rfl

inductive BootState where
  | initial
  | ready (state : TargetState)
  deriving DecidableEq

inductive BootStep : BootState → BootState → Prop where
  | boot : BootStep .initial (.ready .start)
  | instruction {before after : TargetState} (step : TargetStep before after) :
      BootStep (.ready before) (.ready after)

def booted : GSLT where
  Term := BootState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := BootStep
  rewrites_resp_left := by
    intro before other after same step
    subst other
    exact ⟨after, step, rfl⟩
  rewrites_resp_right := by
    intro before after other step same
    exact same ▸ step

def bootView : BootState → TargetState
  | .initial => .start
  | .ready state => state

/-- The second stage retains both initialized and uninitialized phases. -/
def bootCorrespondence : OperationalCorrespondence target booted where
  related origin current := origin = bootView current
  readStep := by
    intro origin current next related step
    cases step with
    | boot => exact .inl related
    | instruction step =>
        exact .inr ⟨_, related ▸ step, rfl⟩
  forward := by
    intro origin after current related step
    cases current with
    | initial =>
        have atStart : origin = TargetState.start := related
        subst origin
        cases step with
        | first =>
            exact ⟨.ready .middle,
              ⟨.cons ⟨BootStep.boot⟩
                (.cons ⟨BootStep.instruction .first⟩ (.refl (BootState.ready .middle)))⟩, rfl⟩
    | ready state =>
        have atState : origin = state := related
        subst origin
        exact ⟨.ready after,
          ⟨.cons ⟨BootStep.instruction step⟩ (.refl (BootState.ready after))⟩, rfl⟩

def bootRank : TargetState → BootState → Nat
  | _, .initial => 1
  | _, .ready _ => 0

def bootProgress : Certificate bootCorrespondence.toOperationalReadback :=
  Certificate.ofNat bootRank (by
    intro origin current next related step
    cases step with
    | boot => exact .inl ⟨related, by change 0 < 1; decide⟩
    | instruction step => exact .inr ⟨_, related ▸ step, rfl⟩)

def composed := correspondence.comp bootCorrespondence

theorem composed_start : composed.related false BootState.initial :=
  ⟨TargetState.start, rfl, rfl⟩

/-- Both actual administrative phases terminate after composition. -/
theorem composed_normalizes : Acc (fun next state => booted.Step state next) BootState.initial :=
  loweringProgress.normalization_preserved_comp bootProgress
    PositiveBlocks.source_normalizes composed_start

def completed : ExecutionPath booted BootState.initial (.ready .finish) :=
  .cons ⟨BootStep.boot⟩
    (.cons ⟨BootStep.instruction .first⟩
      (.cons ⟨BootStep.instruction .second⟩ (.refl (BootState.ready .finish))))

theorem completed_has_three_steps : completed.length = 3 := rfl

theorem completed_readout : sourceView (bootView (BootState.ready .finish)) = true := rfl

theorem composed_observations (observe : Bool → Prop) :
    (∃ after, PositiveBlocks.source.MultiStep false after ∧ observe after) ↔
      ∃ final, booted.MultiStep BootState.initial final ∧
        observe (sourceView (bootView final)) := by
  apply composed.reachable_iff observe (fun state => observe (sourceView (bootView state)))
  · rintro origin current ⟨between, first, second⟩
    have same : origin = sourceView (bootView current) := first.trans (congrArg sourceView second)
    exact same ▸ Iff.rfl
  · exact composed_start

/-- The extra-loop implementation cannot acquire a progress certificate by changing rank types. -/
theorem spinning_has_no_progress :
    ¬ Nonempty (Certificate.{0, 0, uRank} PositiveBlocks.correspondence.toOperationalReadback) := by
  rintro ⟨progress⟩
  exact PositiveBlocks.target_does_not_normalize
    (progress.normalization_preserved PositiveBlocks.source_normalizes rfl)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Progress

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Progress.loweringProgress
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Progress.bootProgress
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Progress.composed_normalizes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Progress.composed_observations
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Progress.spinning_has_no_progress
