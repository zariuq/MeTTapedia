import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentStateGroupoid
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationCoherenceModal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationOfferedCounts

/-!
# Typed publication continuations of native rearranged helper executions

The input is an actual witnessed comparison of helper runs, not an assumed
isomorphism of output values. Its retained endpoint map transports a complete
typed-publication continuation and its refinement. The same map licenses
invariant modal observations and exact counts of origin-indexed offers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.PublicationConsumer

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta TypedPublication
open Mettapedia.OSLF.Framework.DerivedModalities
open LogicOverTheStep.StepSpan LogicOverTheStep.CountingModalities

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]
  {start : State rules O} {first second : (helperStep levels O).toStep.Run start}

noncomputable def continueAfter
    (cell : Transport.RunRearrangement.Cell (helperTransport levels O) first second)
    (continuation : (realizationStep levels O).Run first.last) :
    (realizationStep levels O).Run second.last :=
  RunTransport.move (RunStateGroupoid.endpointMap levels O cell) continuation

noncomputable def resultComparison
    (cell : Transport.RunRearrangement.Cell (helperTransport levels O) first second)
    (continuation : (realizationStep levels O).Run first.last) :
    PlainIso levels continuation.last (continueAfter cell continuation).last :=
  RunTransport.endpoint (RunStateGroupoid.endpointMap levels O cell) continuation

theorem typed_rows
    (cell : Transport.RunRearrangement.Cell (helperTransport levels O) first second)
    (continuation : (realizationStep levels O).Run first.last) (occurrence : O) :
    (continueAfter cell continuation).last.label occurrence =
      (continuation.last.label occurrence).reindex (resultComparison cell continuation).frame.hom :=
  (resultComparison cell continuation).label occurrence

theorem refinement_square
    (cell : Transport.RunRearrangement.Cell (helperTransport levels O) first second)
    (continuation : (realizationStep levels O).Run first.last) :
    (continueAfter cell continuation).toLast ≫ (RunStateGroupoid.endpointMap levels O cell).frame.hom =
      (resultComparison cell continuation).frame.hom ≫ continuation.toLast :=
  RunTransport.refinement_square (RunStateGroupoid.endpointMap levels O cell) continuation

theorem occurrence_possibility
    (cell : Transport.RunRearrangement.Cell (helperTransport levels O) first second) (occurrence : O) :
    derivedDiamond (firingSpan (realizationStep levels O)) (fun state => occurrence ∈ state.present) first.last ↔
      derivedDiamond (firingSpan (realizationStep levels O)) (fun state => occurrence ∈ state.present) second.last :=
  CoherenceModal.occurrence_possible (RunStateGroupoid.endpointMap levels O cell) occurrence

theorem offered_counts {Index : Type}
    (cell : Transport.RunRearrangement.Cell (helperTransport levels O) first second)
    (offers : Index → Application levels O first.last) (observation : State rules O → Prop)
    (invariant : ∀ {left right : State rules O}, PlainIso levels left right →
      (observation left ↔ observation right)) (number : Nat) :
    countingDiamond (OfferedCounts.span offers) number observation first.last ↔
      countingDiamond (OfferedCounts.span (OfferedCounts.move
        (RunStateGroupoid.endpointMap levels O cell) offers)) number observation second.last :=
  OfferedCounts.counts (RunStateGroupoid.endpointMap levels O cell) offers observation invariant number

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.PublicationConsumer

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.PublicationConsumer.refinement_square
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.PublicationConsumer.offered_counts
