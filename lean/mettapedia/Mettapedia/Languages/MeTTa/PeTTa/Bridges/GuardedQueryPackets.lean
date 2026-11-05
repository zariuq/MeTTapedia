import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedNestedQuerySource

/-!
# Completed guarded-query packets at collector exit

Every delivered packet is a true Boolean with no associated work. This is
preserved by actual nested traversal from an empty local collector. The
result discharges the associated-work check, not allocation availability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryPackets

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedPresenceConditional (Input)
open NamedGuardedInsertionSource (Body Evidence)
open NamedGuardedCandidateExecution (Advance executeAdmitted execute)
open NamedGuardedCandidateBatch (State)

variable {Context : Type}

def Ready (packet : CollectedAnswer) : Prop := packet.value = Effects.boolean true ∧ packet.associated = []

def CollectedReady (state : State Context) : Prop := ∀ packet ∈ state.scope.collected, Ready packet

theorem admitted_packets (input : Input Context) (guard : NamedPresenceConditional.Evidence input)
    (body : Body) (evidence : Evidence input guard body)
    (finished : input.caller.goals = []) (output : input.caller.destination = .var body.result)
    (after : Advance) (completed : (executeAdmitted input guard body evidence finished output).result = .advanced after) :
    ∀ packet ∈ after.answers, Ready packet := by
  unfold executeAdmitted at completed
  split at completed
  · cases completed
  next rows snapshot =>
    split at completed
    next ready =>
      split at completed
      next present =>
        split at completed
        · cases completed
        next allocated copied =>
          cases NamedGuardedCandidateExecution.Result.advanced.inj completed
          simp
      next absent =>
        split at completed
        · cases completed
        next middle firstWrite =>
          split at completed
          · cases completed
          next final secondWrite =>
            cases NamedGuardedCandidateExecution.Result.advanced.inj completed
            simp [Ready]
    · cases completed

theorem execute_packets (input : Input Context) (body : Body) (after : Advance)
    (completed : (execute input body).result = .advanced after) : ∀ packet ∈ after.answers, Ready packet := by
  unfold execute at completed
  split at completed
  next finished =>
    split at completed
    next output =>
      split at completed
      · cases completed
      next guard guardReady =>
        split at completed
        · cases completed
        next evidence bodyReady => exact admitted_packets input guard body evidence finished output after completed
    · cases completed
  · cases completed

theorem leaf_preserves (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template) :
    ScopedNestedQueryExecution.Preserves CollectedReady
      (GuardedNestedQuerySource.leaf program template Context).execute := by
  intro caller state context origins pending after valid completed
  change (GuardedNestedQuerySource.invoke program template caller state context origins pending).execution.stop =
    .complete after at completed
  unfold GuardedNestedQuerySource.invoke at completed
  dsimp only at completed
  split at completed
  · cases completed
  next principal resolved =>
    split at completed
    · cases completed
    next request requested =>
      dsimp only at completed
      split at completed
      · cases completed
      · cases completed
      next next advanced =>
        have packets := execute_packets
          ((template.candidate caller context origins request).input program state pending) template.body next advanced
        have same : state.advance next = after := ScopedNestedQueryExecution.Stop.complete.inj completed
        subst after
        intro packet member
        rcases List.mem_append.mp member with old | added
        · exact valid packet old
        · exact packets packet added

theorem completed_ready (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template)
    (legs : List NestedQuerySource.Leg) (caller : Control) (state : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (after : State Context) (empty : state.scope.collected = [])
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program template Context)
      legs caller state context origins pending).stop = .complete after) : CollectedReady after :=
  ScopedNestedQueryExecution.run_preserves program (GuardedNestedQuerySource.leaf program template Context)
    CollectedReady (leaf_preserves program template) legs caller state context origins pending after
    (by intro packet member; simp [empty] at member) completed

theorem associated_clear (packets : List CollectedAnswer) (ready : ∀ packet ∈ packets, Ready packet) :
    packets.all (fun packet => packet.associated.isEmpty) = true := by
  apply List.all_eq_true.mpr
  intro packet member
  rw [(ready packet member).2]
  rfl

theorem values_true (packets : List CollectedAnswer) (ready : ∀ packet ∈ packets, Ready packet) :
    packets.map CollectedAnswer.value = List.replicate packets.length (Effects.boolean true) := by
  induction packets with
  | nil => rfl
  | cons packet rest ih =>
    simp only [List.map_cons, List.length_cons, List.replicate_succ, (ready packet List.mem_cons_self).1,
      ih (fun item member => ready item (List.mem_cons_of_mem _ member))]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryPackets
