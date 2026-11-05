import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCaptureAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryAdmission

/-!
# Uniform no-reference admission of canonical live EU rounds

The actual guard declaration, evaluated operand modes, fresh local slots and
empty collapse-child tail establish admission. Live decoded worlds are
preserved after each completed child. The theorem permits explicit resource
suspension and does not assert sufficient allocator capacity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmission

open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilScopedRound
open CTLUntilAdmissionFrame (AdmissionFrame)
open CTLUntilLeafAdmission (GuardProfile)

variable {Context Label : Type} [DecidableEq Label]

theorem admitted (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (distinct : [query.names.next, query.names.prior, query.names.result, query.names.temporary].Nodup)
    (program : SpaceSemantics.Program) (profile : GuardProfile codec label query program)
    (legs : List NestedQuerySource.Leg) :
    ScopedQueryAdmission.AdmittedOn (AdmissionFrame codec label operand round query legs) (Decoded codec query.handles)
      (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context) legs) := by
  have names := distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at names
  apply ScopedQueryAdmission.run_admitted program (GuardedNestedQuerySource.leaf program query.template Context)
    (AdmissionFrame codec label operand round query) (Decoded codec query.handles)
  · intro caller state context origins pending after frame valid completed
    exact leaf_preserves codec label operand round query program query.handles
      caller state context origins pending after frame.frame valid completed
  · intro caller state context origins pending frame valid saved
    exact CTLUntilLeafAdmission.leaf_not_reference codec label operand round query program profile (by tauto)
      caller state context origins pending frame valid saved
  · exact CTLUntilCaptureAdmission.capture_admission_frame codec label operand round query distinct program
  · intro leg rest caller state context origins pending frame valid
    exact CTLUntilCaptureAdmission.phase_capture_exists codec label operand round query program leg rest
      caller state context origins pending frame.frame valid

theorem complete_or_suspended (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (distinct : [query.names.next, query.names.prior, query.names.result, query.names.temporary].Nodup)
    (program : SpaceSemantics.Program) (profile : GuardProfile codec label query program)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (frame : AdmissionFrame codec label operand round query query.legs caller)
    (valid : Decoded codec query.handles state) :
    let execution := ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context)
      query.legs caller state context origins pending
    (∃ after, execution.stop = .complete after) ∨ (∃ reason saved, execution.stop = .suspended reason saved) := by
  dsimp only
  have noReference := admitted codec label operand round query distinct program profile query.legs
    caller state context origins pending frame valid
  cases result : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context)
      query.legs caller state context origins pending).stop with
  | complete after => exact Or.inl ⟨after, rfl⟩
  | suspended reason saved => exact Or.inr ⟨reason, saved, rfl⟩
  | reference saved => exact False.elim (noReference saved result)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmission
