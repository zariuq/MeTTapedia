import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketScopedRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.PacketResultReadouts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketScopedQueriesControls

/-!
# Closed readings of the actual scoped result state

The store is a bag of physical occurrences, the commit is a bag of matches,
each guard is asked after that member's own tells, the program is fixed,
and knowledge is one store. The reader starts with the actual state's
present occurrences, knowledge and labels. The actual scoped result law
then identifies its reading with the packet update fold's reading. This
identification alone asserts no serial execution of an atomic own bag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ScopedResultReadouts

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open TaggedAssignments (Substitution)
open NativePacketStep (Terms Ports packetAction)
open NativeClosedReadings (ClosedTerm closedAt)
open RuleSyntax
open RuleSyntax.StepWeb.ObservedBags

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}

/-- A possible closed reading of the actual labelled state, with an actual
model of that state's knowledge and the actual conditional-row decoder. -/
def StateReads (initial : NativeState S O Γ sort)
    (actual : State (OneFrame.Terms (Terms S O Γ sort)) (Ports O))
    (occurrence : O) (pattern : ClosedTerm S Γ sort) : Prop :=
  Sum.inl occurrence ∈ actual.present ∧
    ∃ substitution : Substitution S,
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution actual.knowledge ∧
      NativePacketQueryView.rowMatches (NativePacketStep.baseObject initial 0)
        (closedAt initial.state.declarations pattern) substitution (actual.label (.inl occurrence))

theorem stateReads_present {initial : NativeState S O Γ sort}
    {actual : State (OneFrame.Terms (Terms S O Γ sort)) (Ports O)}
    {occurrence : O} {pattern : ClosedTerm S Γ sort} (read : StateReads initial actual occurrence pattern) :
    Sum.inl occurrence ∈ actual.present := read.1

theorem not_stateReads_of_missing {initial : NativeState S O Γ sort}
    {actual : State (OneFrame.Terms (Terms S O Γ sort)) (Ports O)}
    {occurrence : O} (missing : Sum.inl occurrence ∉ actual.present) (pattern : ClosedTerm S Γ sort) :
    ¬ StateReads initial actual occurrence pattern := fun read => missing read.1

/-- Only this structural projection lemma unfolds the embedded state. -/
theorem stateReads_embed (initial : NativeState S O Γ sort) (label : Ports O → Terms S O Γ sort)
    (configuration : Configuration (Terms S O Γ sort) (Ports O))
    (occurrence : O) (pattern : ClosedTerm S Γ sort) :
    StateReads initial (OneFrame.embed label configuration) occurrence pattern ↔
      Sum.inl occurrence ∈ configuration.present ∧
        ∃ substitution : Substitution S,
          (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution configuration.equations ∧
          NativePacketQueryView.rowMatches (NativePacketStep.baseObject initial 0)
            (closedAt initial.state.declarations pattern) substitution (label (.inl occurrence)) := Iff.rfl

theorem stateReads_eq {initial : NativeState S O Γ sort}
    {actual other : State (OneFrame.Terms (Terms S O Γ sort)) (Ports O)} (same : actual = other)
    (occurrence : O) (pattern : ClosedTerm S Γ sort) :
    StateReads initial actual occurrence pattern ↔ StateReads initial other occurrence pattern :=
  Iff.of_eq (congrArg (fun state => StateReads initial state occurrence pattern) same)

variable [DecidableEq O]

/-- The actual scoped step's state fields, rather than a supplied packet
observer, give the packet reading through the earned full result equation. -/
theorem scoped_packet_iff {initial : NativeState S O Γ sort} (members : List (LiveFiring initial))
    (admitted : (scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (NativePacketScopedQueries.scopedQueries members)).Admits (s := NativePacketRounds.source members)
        (JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
          (NativePacketScopedQueries.memberList members)))
    (occurrence : O) (pattern : ClosedTerm S Γ sort) :
    StateReads initial
        ((scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
          (NativePacketScopedQueries.scopedQueries members)).result
            (JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
              (NativePacketScopedQueries.memberList members)) admitted)
        occurrence pattern ↔ PacketResultReadouts.PacketReads members occurrence pattern :=
  stateReads_eq (NativePacketScopedRounds.scoped_result_eq_follow members admitted) occurrence pattern

section Native

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- The actual scoped state and the same supplied native execution have
exactly the same closed readings. Pair blindness is earned separately from
own admission; the native witness and its final state are not replaced. -/
theorem scoped_native_iff {initial last : NativeState S O Γ sort}
    (members : List (LiveFiring initial))
    (admitted : (scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (NativePacketScopedQueries.scopedQueries members)).Admits (s := NativePacketRounds.source members)
        (JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
          (NativePacketScopedQueries.memberList members)))
    (nonempty : members ≠ []) (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (blind : NativePacketScopedRounds.PairBlind members)
    {order : List (LiveFiring initial)} (permutation : order.Perm members)
    (witness : NativeRoundExecution.Witness initial order last)
    (occurrence : O) (pattern : ClosedTerm S Γ sort) :
    StateReads initial
        ((scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
          (NativePacketScopedQueries.scopedQueries members)).result
            (JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
              (NativePacketScopedQueries.memberList members)) admitted)
        occurrence pattern ↔ NativeClosedReadings.Reads last occurrence pattern := by
  have round := (NativePacketScopedRounds.round_iff_scoped_and_blind members nonempty).mpr ⟨admitted,blind⟩
  exact (scoped_packet_iff members admitted occurrence pattern).trans
    (PacketResultReadouts.guarded_round_result_reads_iff members nonempty shapes round permutation witness occurrence pattern)

end Native

namespace Controls

open ContextualNonprincipalCountControls
open NativePacketGuardedAdmissionControls (state)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Nat)

def zero : ClosedTerm base [] () := literal 0

theorem produced_packet :
    PacketResultReadouts.PacketReads NativePacketScopedQueriesControls.members 2 zero := by
  refine ⟨by decide,NativePacketRounds.fitData NativePacketScopedQueriesControls.constantData,?_,?_⟩
  · have model := NativePacketRounds.fitData_joint NativePacketScopedQueriesControls.constantData
      (by simp [NativePacketScopedQueriesControls.members]) NativePacketScopedQueriesControls.each_enabled
    exact (congrArg (fun equations =>
      (packetAction (S := base) (O := Nat) (Γ := []) (sort := ())).Models
        (NativePacketRounds.fitData NativePacketScopedQueriesControls.constantData) equations)
      (PacketResultReadouts.packetFinal_equations NativePacketScopedQueriesControls.members)).mpr model
  · have decoded := (PacketResultReadouts.fitData_base_output_iff
      NativePacketScopedQueriesControls.constantData ⟨0,by decide⟩ zero 2).mpr rfl
    exact decoded

/-- Reading a produced physical row of the actual atomic result requires
no invented serial witness. Both serial orders of this same bag are refused. -/
theorem actual_atomic_reads_produced :
    StateReads state
      ((scopedStep (OneFrame.frames (packetAction (S := base) (O := Nat) (Γ := []) (sort := ())))
        (NativePacketScopedQueries.scopedQueries NativePacketScopedQueriesControls.members)).result
          NativePacketScopedQueriesControls.atomicBag NativePacketScopedQueriesControls.atomic_scoped) 2 zero :=
  (scoped_packet_iff NativePacketScopedQueriesControls.members NativePacketScopedQueriesControls.atomic_scoped 2 zero).mpr
    produced_packet

theorem actual_atomic_unread (pattern : ClosedTerm base [] ()) :
    ¬ StateReads state
      ((scopedStep (OneFrame.frames (packetAction (S := base) (O := Nat) (Γ := []) (sort := ())))
        (NativePacketScopedQueries.scopedQueries NativePacketScopedQueriesControls.members)).result
          NativePacketScopedQueriesControls.atomicBag NativePacketScopedQueriesControls.atomic_scoped) 4 pattern := by
  intro read
  have packet := (scoped_packet_iff NativePacketScopedQueriesControls.members
    NativePacketScopedQueriesControls.atomic_scoped 4 pattern).mp read
  have missing : Sum.inl (4 : Nat) ∉ (PacketResultReadouts.packetFinal NativePacketScopedQueriesControls.members).present := by decide
  exact missing packet.1

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ScopedResultReadouts
