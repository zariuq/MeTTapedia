import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.HostedPacketRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ScopedResultReadouts

/-!
# Actual scoped results read back through the existing hosted answer observer

The family consists of the hosted adapter's actual live firings. Its guarded
round earns scoped admission and native clearness. The returned scoped state
is read through its real present occurrences, knowledge and conditional rows;
the same observer is then read from an actual hosted execution endpoint.

Every permitted order has an actual execution. Rigid source origins and
complete answer bags retain their separate history contracts. An atomic own
bag without the round licence is not assigned a serial hosted execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedResultReadouts

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open RuleSyntax RuleSyntax.StepWeb.HostedNative
open RuleSyntax.StepWeb.HostedNative.Rounds
open RuleSyntax.StepWeb.ObservedBags
open NativePacketStep (Terms Ports packetAction)

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- The actual scoped operation on this symbolic common image. Admission is
earned from the supplied guarded round, rather than a result oracle. -/
noncomputable def scopedResult {initial : NativeState S Nat Γ star}
    (members : List (LiveFiring initial)) (nonempty : members ≠ [])
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := Nat) (Γ := Γ) (sort := star))
      (NativePacketRounds.label members) (NativePacketStep.configuration initial 0)
      (NativePacketGuardedRounds.image members)) :=
  (scopedStep (OneFrame.frames (packetAction (S := S) (O := Nat) (Γ := Γ) (sort := star)))
    (NativePacketScopedQueries.scopedQueries members)).result
      (JointFirings.bagOf (packetAction (S := S) (O := Nat) (Γ := Γ) (sort := star))
        (NativePacketScopedQueries.memberList members))
      (NativePacketScopedRounds.scoped_of_round nonempty round)

/-- The packet result and a supplied actual hosted execution have the same
existing source answer observation, at each physically present alternative. -/
theorem packet_hosted_iff {P : CProgram S} (N : Nodes S Γ star)
    (hosted : HostState S) (presented : Presented Γ star hosted) (occupied : Finset Nat)
    (members : List (Member Γ star κ P)) (nonempty : members ≠ [])
    (shapes : ∀ index : Fin (HostedPacketRounds.live N hosted presented occupied members).length,
      native.Shapes (HostedPacketRounds.live N hosted presented occupied members)[index].toNative)
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := Nat) (Γ := Γ) (sort := star))
      (NativePacketRounds.label (HostedPacketRounds.live N hosted presented occupied members))
      (NativePacketStep.configuration (state κ hosted presented occupied) 0)
      (NativePacketGuardedRounds.image (HostedPacketRounds.live N hosted presented occupied members)))
    {order : List (Member Γ star κ P)} (permutation : order.Perm members)
    {last : HostState S} {represented : Presented Γ star last} {ledger : Finset Nat}
    (run : HostedRun hosted presented occupied order last represented ledger)
    (occurrence : Nat) (present : occurrence ∈ last.present) (value : Term S Γ star) :
    PacketResultReadouts.PacketReads (HostedPacketRounds.live N hosted presented occupied members)
        occurrence (HostedAnswerReadings.answerPattern N value) ↔
      value ∈ stateAnswer N last occurrence := by
  obtain ⟨nativeLast,sequential,same⟩ := (sequential_iff N order hosted presented occupied).2 run
  obtain ⟨witness⟩ := NativeRoundExecution.Witness.nonempty_iff.mpr sequential
  have reads := PacketResultReadouts.guarded_round_result_reads_iff
    (HostedPacketRounds.live N hosted presented occupied members)
    (HostedPacketRounds.live_nonempty N hosted presented occupied members nonempty) shapes round
    (permutation.map (Member.live N hosted presented occupied)) witness occurrence
    (HostedAnswerReadings.answerPattern N value)
  exact reads.trans ((NativeClosedReadings.deadEquiv_reads_iff same occurrence
    (HostedAnswerReadings.answerPattern N value)).symm.trans
      (HostedAnswerReadings.reading_iff_stateAnswer N last represented ledger occurrence present value))

/-- This statement reads the actual scoped returned state before interpreting
the result through the actual hosted execution and its existing answer observer. -/
theorem scoped_hosted_iff {P : CProgram S} (N : Nodes S Γ star)
    (hosted : HostState S) (presented : Presented Γ star hosted) (occupied : Finset Nat)
    (members : List (Member Γ star κ P)) (nonempty : members ≠ [])
    (shapes : ∀ index : Fin (HostedPacketRounds.live N hosted presented occupied members).length,
      native.Shapes (HostedPacketRounds.live N hosted presented occupied members)[index].toNative)
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := Nat) (Γ := Γ) (sort := star))
      (NativePacketRounds.label (HostedPacketRounds.live N hosted presented occupied members))
      (NativePacketStep.configuration (state κ hosted presented occupied) 0)
      (NativePacketGuardedRounds.image (HostedPacketRounds.live N hosted presented occupied members)))
    {order : List (Member Γ star κ P)} (permutation : order.Perm members)
    {last : HostState S} {represented : Presented Γ star last} {ledger : Finset Nat}
    (run : HostedRun hosted presented occupied order last represented ledger)
    (occurrence : Nat) (present : occurrence ∈ last.present) (value : Term S Γ star) :
    ScopedResultReadouts.StateReads (state κ hosted presented occupied)
        (scopedResult (HostedPacketRounds.live N hosted presented occupied members)
          (HostedPacketRounds.live_nonempty N hosted presented occupied members nonempty) round)
        occurrence (HostedAnswerReadings.answerPattern N value) ↔
      value ∈ stateAnswer N last occurrence :=
  (ScopedResultReadouts.scoped_packet_iff _ (NativePacketScopedRounds.scoped_of_round
    (HostedPacketRounds.live_nonempty N hosted presented occupied members nonempty) round)
      occurrence (HostedAnswerReadings.answerPattern N value)).trans
    (packet_hosted_iff N hosted presented occupied members nonempty shapes round permutation
      run occurrence present value)

/-- Every order licensed by the real guarded round has a hosted execution
whose existing source answers are exactly the actual scoped result readings. -/
theorem every_order_scoped_answers {P : CProgram S} (N : Nodes S Γ star)
    (hosted : HostState S) (presented : Presented Γ star hosted) (occupied : Finset Nat)
    (members : List (Member Γ star κ P)) (nonempty : members ≠ [])
    (shapes : ∀ index : Fin (HostedPacketRounds.live N hosted presented occupied members).length,
      native.Shapes (HostedPacketRounds.live N hosted presented occupied members)[index].toNative)
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := Nat) (Γ := Γ) (sort := star))
      (NativePacketRounds.label (HostedPacketRounds.live N hosted presented occupied members))
      (NativePacketStep.configuration (state κ hosted presented occupied) 0)
      (NativePacketGuardedRounds.image (HostedPacketRounds.live N hosted presented occupied members))) :
    ∀ order : List (Member Γ star κ P), order.Perm members →
      ∃ (last : HostState S) (represented : Presented Γ star last) (ledger : Finset Nat),
        HostedRun hosted presented occupied order last represented ledger ∧
          ∀ occurrence ∈ last.present, ∀ value : Term S Γ star,
            ScopedResultReadouts.StateReads (state κ hosted presented occupied)
                (scopedResult (HostedPacketRounds.live N hosted presented occupied members)
                  (HostedPacketRounds.live_nonempty N hosted presented occupied members nonempty) round)
                occurrence (HostedAnswerReadings.answerPattern N value) ↔
              value ∈ stateAnswer N last occurrence := by
  have clear := (HostedPacketRounds.packetRound_iff_clear N hosted presented occupied members nonempty shapes).mp round
  obtain ⟨_,_,_,_,every⟩ := every_order_hosted N hosted presented occupied members clear
  intro order permutation
  obtain ⟨last,represented,ledger,run,_⟩ := every order permutation
  exact ⟨last,represented,ledger,run,fun occurrence present value =>
    scoped_hosted_iff N hosted presented occupied members nonempty shapes round permutation
      run occurrence present value⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedResultReadouts
