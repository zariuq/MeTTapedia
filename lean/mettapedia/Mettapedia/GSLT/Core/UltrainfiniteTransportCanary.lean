import Mettapedia.GSLT.Core.UltrainfiniteTransport

/-!
# Canaries for carried bisimulation transport

The positive fixture embeds a three-state source transition system into a
four-state target.  The target may contain an unrelated state; only steps
leaving image states must lift.  A carried bisimulation between two distinct
source states transports to the target and identifies their quotient classes.

The negative fixture adds one escape transition from an image state to the
unrelated target state.  Forward step preservation still holds, but no
`StepCover` exists.  Thus the lifting field is semantically load-bearing.
-/

namespace Mettapedia.GSLT.Ultrainfinite.TransportCanary

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite

private def systemOf (Term : Type) (Step : Term → Term → Prop) : GSLT where
  Term := Term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro left left' target equal step
    subst left'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro left target target' step equal
    subst target'
    exact step

private inductive SourceState where
  | left
  | right
  | done
  deriving DecidableEq

private inductive SourceTransition : SourceState → SourceState → Prop where
  | leftDone : SourceTransition .left .done
  | rightDone : SourceTransition .right .done

private def sourceSystem : GSLT := systemOf SourceState SourceTransition

private inductive TargetState where
  | image (source : SourceState)
  | unrelated
  deriving DecidableEq

private def embed : SourceState → TargetState := .image

private inductive TargetTransition : TargetState → TargetState → Prop where
  | image {source target : SourceState} : SourceTransition source target →
      TargetTransition (.image source) (.image target)

private def targetSystem : GSLT := systemOf TargetState TargetTransition

private def sourceTargetCover :
    StepCover sourceSystem targetSystem embed where
  mapStep := fun step => .image step
  liftStep := by
    intro source target step
    cases step with
    | image sourceStep => exact ⟨_, sourceStep, rfl⟩

private inductive Mirror : SourceState → SourceState → Type where
  | initial : Mirror .left .right
  | finished : Mirror .done .done

private theorem left_step_target {target : SourceState}
    (step : SourceTransition .left target) : target = .done := by
  cases step
  rfl

private theorem right_step_target {target : SourceState}
    (step : SourceTransition .right target) : target = .done := by
  cases step
  rfl

private theorem done_has_no_step {target : SourceState} :
    ¬ SourceTransition .done target := by
  intro step
  cases step

/-- The distinct initial states are behaviorally identical because each has
exactly one transition to the common terminal state. -/
private def sourceMirror : BisimulationWitness sourceSystem where
  Related := Mirror
  forward := by
    intro _left _right related leftTarget step
    cases related with
    | initial =>
        have targetEq := left_step_target step
        subst leftTarget
        exact ⟨SourceState.done, SourceTransition.rightDone,
          Mirror.finished⟩
    | finished => exact False.elim (done_has_no_step step)
  backward := by
    intro _left _right related rightTarget step
    cases related with
    | initial =>
        have targetEq := right_step_target step
        subst rightTarget
        exact ⟨SourceState.done, SourceTransition.leftDone,
          Mirror.finished⟩
    | finished => exact False.elim (done_has_no_step step)

/-- The translated witness still contains the original source relation
evidence; it is not reconstructed from quotient equality. -/
theorem mapped_witness_retains_source_evidence :
    Nonempty
      ((sourceMirror.map sourceTargetCover).Related
        (embed .left) (embed .right)) :=
  ⟨{ sourceLeft := .left
     sourceRight := .right
     left_eq := rfl
     right_eq := rfl
     related := Mirror.initial }⟩

/-- Positive behavioral result: covered translation preserves the carried
bisimulation between two distinct states. -/
theorem covered_translation_preserves_bisimilarity :
    targetSystem.Bisimilar (embed .left) (embed .right) :=
  sourceMirror.map_toBisimilar sourceTargetCover Mirror.initial

/-- The target ontology sees the equality only after the proof-relevant
witness has been transported. -/
theorem covered_translation_identifies_target_ontology :
    Mettapedia.GSLT.Meredith.Bisimulation.toBisimClass targetSystem
        (embed .left) =
      Mettapedia.GSLT.Meredith.Bisimulation.toBisimClass targetSystem
        (embed .right) :=
  sourceMirror.map_toBisimClass_eq sourceTargetCover Mirror.initial

private inductive EscapingTargetTransition :
    TargetState → TargetState → Prop where
  | image {source target : SourceState} : SourceTransition source target →
      EscapingTargetTransition (.image source) (.image target)
  | escape : EscapingTargetTransition (.image .left) .unrelated

private def escapingTargetSystem : GSLT :=
  systemOf TargetState EscapingTargetTransition

/-- Negative result: preserving every source step is not enough.  The added
escape from an image state has no source lift, so no cover can accompany the
same carrier map. -/
theorem forward_preservation_without_cover :
    (∀ {source target}, SourceTransition source target →
      escapingTargetSystem.Step (embed source) (embed target)) ∧
    ¬ Nonempty (StepCover sourceSystem escapingTargetSystem embed) := by
  constructor
  · intro source target step
    exact EscapingTargetTransition.image step
  · rintro ⟨cover⟩
    obtain ⟨sourceTarget, sourceStep, targetEq⟩ :=
      cover.liftStep EscapingTargetTransition.escape
    cases sourceStep
    cases targetEq

#print axioms mapped_witness_retains_source_evidence
#print axioms covered_translation_preserves_bisimilarity
#print axioms covered_translation_identifies_target_ontology
#print axioms forward_preservation_without_cover

end Mettapedia.GSLT.Ultrainfinite.TransportCanary
