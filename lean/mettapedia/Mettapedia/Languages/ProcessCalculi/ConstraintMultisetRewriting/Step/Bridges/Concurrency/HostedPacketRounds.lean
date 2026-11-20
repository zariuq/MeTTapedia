import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketGuardedRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.HostedAnswerReadings

/-!
# Guarded packet rounds preserve the existing hosted answer observation

The intermediate family consists of the actual live firings supplied by the
hosted adapter. The packet's pair-cut checks earn native family clearness;
its native executions then read back as hosted executions. At their common
present occurrences all orders have the same existing answer observation.

Rigid source origins are retained by named histories separately. Atomic own
bags require their additional independence licence before these serial laws
apply. Finished status and complete answer bags have separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedPacketRounds

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open RuleSyntax.StepWeb.HostedNative
open RuleSyntax.StepWeb.HostedNative.Rounds

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

noncomputable def live {P : CProgram S} (N : Nodes S Γ star) (hosted : HostState S)
    (presented : Presented Γ star hosted) (occupied : Finset ℕ) (members : List (Member Γ star κ P)) :=
  members.map (Member.live N hosted presented occupied)

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem live_nonempty {P : CProgram S} (N : Nodes S Γ star) (hosted : HostState S)
    (presented : Presented Γ star hosted) (occupied : Finset ℕ) (members : List (Member Γ star κ P))
    (nonempty : members ≠ []) : live N hosted presented occupied members ≠ [] := by
  intro empty
  cases members with
  | nil => exact nonempty rfl
  | cons first rest => cases empty

theorem packetRound_iff_clear {P : CProgram S} (N : Nodes S Γ star) (hosted : HostState S)
    (presented : Presented Γ star hosted) (occupied : Finset ℕ) (members : List (Member Γ star κ P))
    (nonempty : members ≠ [])
    (shapes : ∀ index : Fin (live N hosted presented occupied members).length,
      native.Shapes (live N hosted presented occupied members)[index].toNative) :
    AnnotatedRuns.Round NativePacketStep.packetAction
        (NativePacketRounds.label (live N hosted presented occupied members))
        (NativePacketStep.configuration (state κ hosted presented occupied) 0)
        (NativePacketGuardedRounds.image (live N hosted presented occupied members)) ↔
      NativeIterated.FamilyClear (state κ hosted presented occupied)
        (live N hosted presented occupied members) :=
  NativePacketGuardedRounds.round_iff _ (live_nonempty N hosted presented occupied members nonempty) shapes

theorem packetRound_iff_concurrent {P : CProgram S} (N : Nodes S Γ star) (hosted : HostState S)
    (presented : Presented Γ star hosted) (occupied : Finset ℕ) (members : List (Member Γ star κ P))
    (nonempty : members ≠ [])
    (shapes : ∀ index : Fin (live N hosted presented occupied members).length,
      native.Shapes (live N hosted presented occupied members)[index].toNative) :
    AnnotatedRuns.Round NativePacketStep.packetAction
        (NativePacketRounds.label (live N hosted presented occupied members))
        (NativePacketStep.configuration (state κ hosted presented occupied) 0)
        (NativePacketGuardedRounds.image (live N hosted presented occupied members)) ↔
      ∃ last, NativeConcurrent.Concurrent (state κ hosted presented occupied)
        (live N hosted presented occupied members : Multiset (LiveFiring (state κ hosted presented occupied))) last :=
  NativePacketGuardedRounds.round_iff_concurrent _ (live_nonempty N hosted presented occupied members nonempty) shapes

theorem packetRound_answers {P : CProgram S} (N : Nodes S Γ star) (hosted : HostState S)
    (presented : Presented Γ star hosted) (occupied : Finset ℕ) (members : List (Member Γ star κ P))
    (nonempty : members ≠ [])
    (shapes : ∀ index : Fin (live N hosted presented occupied members).length,
      native.Shapes (live N hosted presented occupied members)[index].toNative)
    (round : AnnotatedRuns.Round NativePacketStep.packetAction
      (NativePacketRounds.label (live N hosted presented occupied members))
      (NativePacketStep.configuration (state κ hosted presented occupied) 0)
      (NativePacketGuardedRounds.image (live N hosted presented occupied members))) :
    ∃ (first : HostState S) (left : Presented Γ star first) (firstOccupied : Finset ℕ),
      HostedRun hosted presented occupied members first left firstOccupied ∧
        ∀ order : List (Member Γ star κ P), order.Perm members →
          ∃ (second : HostState S) (right : Presented Γ star second) (secondOccupied : Finset ℕ),
            HostedRun hosted presented occupied order second right secondOccupied ∧
              NativeDead.DeadEquiv (state κ first left firstOccupied) (state κ second right secondOccupied) ∧
              first.present = second.present ∧
              ∀ occurrence ∈ first.present, stateAnswer N first occurrence = stateAnswer N second occurrence :=
  HostedAnswerReadings.every_order_hosted_answers N hosted presented occupied members
    ((packetRound_iff_clear N hosted presented occupied members nonempty shapes).mp round)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedPacketRounds
