import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceInstances
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ResumableControls
import Mettapedia.GSLT.Core.ProgrammableSpaceReachability
import Mettapedia.GSLT.Logic.ProgrammableSpaceMaterialFamilies
import Mettapedia.GSLT.Logic.ProgrammableSpaceAtomCoding
import Mettapedia.GSLT.Logic.ProgrammableSpaceReadings

/-!
# Interleaving authored rewriting with retained MM2 matching

One admitted space executes three actual events: the transaction matcher
pauses with a private answer, authored beta runs while the packet remains
retained, and the same matcher packet resumes to publish its exhausted batch.
The structural poll account and the rewrite account remain separate. The
unchanged store during beta is the precise reason this snapshot can resume.

The example uses the full mixed source list and the actual structural matcher.
The rows are extracted from its completed result, rather than supplied as
purported matching evidence. Reachability connects every exhibited state to
source admission, and the actual publication supplies a dependent material
continuation in the existing growing execution interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceResumableInstances

open Mettapedia.GSLT.Core.ProgrammableSpace
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor
open Mettapedia.Machines.Cursor

abbrev Tag := ProgrammableSpaceInstances.Tag

def languages : Tag → Language Atom
  | .rewrite => ProgrammableSpaceRewrite.language ProgrammableSpaceRewrite.Lambda.calculus
  | .transaction => ProgrammableSpaceMM2Resumable.language

/-- The transaction policy charges the retained cursor's actual poll account.
A grant is not identified with the amount eventually consumed. -/
def transactionPolicy (budget : Nat) : Policy ProgrammableSpaceMM2Resumable.language where
  State := Nat
  permits spent _ _ _ receipt _ _ next :=
    receipt.spentBefore = spent ∧ receipt.spentAfter ≤ budget ∧
      next = receipt.spentAfter ∧ 0 < receipt.grant

def policies : (tag : Tag) → Policy (languages tag)
  | .rewrite => ProgrammableSpaceRewrite.depthPolicy ProgrammableSpaceRewrite.Lambda.calculus 1
  | .transaction => transactionPolicy 200

abbrev Workspace := Space languages policies
abbrev atoms := ProgrammableSpaceInstances.atoms
abbrev rewriteRequest := ProgrammableSpaceInstances.rewriteRequest
abbrev request := ProgrammableSpaceMM2ReceiptControls.joinRequest

def initial : Workspace := ⟨atoms, [], []⟩

def rewritePosition : Fin atoms.length := ⟨0, by decide⟩
def transactionPosition : Fin atoms.length := ⟨6, by decide⟩

theorem rewrite_admitted :
    Admitted languages policies initial .rewrite rewritePosition rewriteRequest :=
  ProgrammableSpaceRewrite.request_admitted _ _

theorem transaction_admitted :
    Admitted languages policies initial .transaction transactionPosition request :=
  ProgrammableSpaceMM2ReceiptControls.join_source_admitted

def registered : Workspace :=
  start languages policies
    (start languages policies initial .rewrite (ProgrammableSpaceRewrite.Lambda.scope [.term])
      (0 : Nat) rewritePosition rewriteRequest rewrite_admitted)
    .transaction .leaveInert (0 : Nat) transactionPosition request transaction_admitted

theorem registered_started : Started languages policies registered := by
  unfold registered
  apply start_started languages policies
  apply start_started languages policies
  exact initial_started languages policies atoms

def initialCheckpoint : ProgrammableSpaceMM2Resumable.Checkpoint :=
  .start atoms request

def pausedPacket? (result : ProgrammableSpaceMM2Matching.Result atoms request) :
    Option (ProgrammableSpaceMM2Resumable.PacketFor atoms request) :=
  match result with
  | .paused packet => some packet
  | .done _ => none

theorem paused_get (result : ProgrammableSpaceMM2Matching.Result atoms request)
    (available : (pausedPacket? result).isSome) :
    result = .paused ((pausedPacket? result).get available) := by
  cases result with
  | paused packet => rfl
  | done result => exact False.elim (Bool.false_ne_true available)

def packet100 : ProgrammableSpaceMM2Resumable.PacketFor atoms request :=
  (pausedPacket? (ProgrammableSpaceMM2Matching.run atoms request 100).2).get
    (by decide +kernel)

def checkpoint100 : ProgrammableSpaceMM2Resumable.Checkpoint where
  before := atoms
  request := request
  granted := 100
  spent := 100
  packet := packet100
  reached := by
    apply Prod.ext
    · decide +kernel
    · exact paused_get _ _

def finishedResult? (result : ProgrammableSpaceMM2Matching.Result atoms request) :
    Option (ProgrammableSpaceMM2Resumable.FinishedFor atoms request) :=
  match result with
  | .paused _ => none
  | .done result => some result

theorem finished_get (result : ProgrammableSpaceMM2Matching.Result atoms request)
    (available : (finishedResult? result).isSome) :
    result = .done ((finishedResult? result).get available) := by
  cases result with
  | paused packet => exact False.elim (Bool.false_ne_true available)
  | done result => rfl

def finished : ProgrammableSpaceMM2Resumable.FinishedFor atoms request :=
  (finishedResult? (ProgrammableSpaceMM2Matching.run atoms request 200).2).get
    (by decide +kernel)

def publication : ProgrammableSpaceMM2.Receipt := ⟨request, atoms, finished.2.1⟩

def resultAtoms : List Atom := ProgrammableSpaceSyntax.encode rewriteRequest ::
  (ProgrammableSpaceMM2ReceiptControls.context ++ [ProgrammableSpaceMM2ReceiptControls.reachable])

theorem selected : MM2MatchingBatch.SelectedFor .leaveInert atoms request.directive := by
  unfold MM2MatchingBatch.SelectedFor
  decide +kernel

theorem pause_exact : initialCheckpoint.resume 100 = (100, .paused packet100) := by
  rw [ProgrammableSpaceMM2Resumable.Checkpoint.resume_exact]
  exact checkpoint100.reached

theorem completion_exact : checkpoint100.resume 100 = (197, .done finished) := by
  rw [ProgrammableSpaceMM2Resumable.Checkpoint.resume_exact]
  apply Prod.ext
  · decide +kernel
  · exact finished_get _ _

theorem first_grant_retains_private_answer :
    checkpoint100.privateRows.length = 1 ∧ checkpoint100.remainingSyntax ≠ [] := by
  decide +kernel

theorem publication_store : publication.after = resultAtoms := by decide +kernel

theorem completed_rows_keep_actual_origins :
    publication.rows.length = 2 ∧
      publication.witnessesInSourceOrder.map (List.map Prod.snd) = [[1, 2, 3], [1, 4, 5]] := by
  decide +kernel

def pauseReceipt : ProgrammableSpaceMM2Resumable.Receipt := ⟨100, 0, 100, none⟩
def commitReceipt : ProgrammableSpaceMM2Resumable.Receipt := ⟨100, 100, 197, some publication⟩

theorem actual_pause :
    (languages .transaction).advance .leaveInert atoms (.matching initialCheckpoint)
      pauseReceipt atoms (.matching checkpoint100) :=
  ProgrammableSpaceMM2Resumable.Advance.pause initialCheckpoint 100 100 packet100
    selected pause_exact

theorem actual_commit :
    (languages .transaction).advance .leaveInert atoms (.matching checkpoint100)
      commitReceipt resultAtoms (.committed publication) := by
  have event := ProgrammableSpaceMM2Resumable.Advance.commit
    (scope := .leaveInert) checkpoint100 100 197 finished selected completion_exact
  change ProgrammableSpaceMM2Resumable.Advance .leaveInert atoms (.matching checkpoint100)
    commitReceipt publication.after (.committed publication) at event
  rwa [publication_store] at event

theorem publication_has_atomic_source_meaning :
    cRuleScopedSourceWorkQueueStep .leaveInert atoms = some resultAtoms :=
  ProgrammableSpaceMM2Resumable.completed_source_step actual_commit publication rfl

def rewriteSession : Session (languages .rewrite) (policies .rewrite) where
  origin := ⟨atoms, rewritePosition⟩
  scope := ProgrammableSpaceRewrite.Lambda.scope [.term]
  request := rewriteRequest
  residual := rewriteRequest
  policyState := (0 : Nat)

def transactionSession : Session (languages .transaction) (policies .transaction) where
  origin := ⟨atoms, transactionPosition⟩
  scope := .leaveInert
  request := request
  residual := .matching initialCheckpoint
  policyState := (0 : Nat)

def pausedSession : Session (languages .transaction) (policies .transaction) :=
  { transactionSession with residual := .matching checkpoint100, policyState := (100 : Nat) }

def rewrittenSession : Session (languages .rewrite) (policies .rewrite) :=
  { rewriteSession with residual := encodeTerm openTarget, policyState := (1 : Nat) }

def committedSession : Session (languages .transaction) (policies .transaction) :=
  { pausedSession with residual := .committed publication, policyState := (197 : Nat) }

abbrev betaReceipt := ProgrammableSpaceInstances.betaReceipt

def pauseEvent : PolicyEvent (languages .transaction) (policies .transaction) where
  origin := transactionSession.origin
  scope := transactionSession.scope
  before := atoms
  after := atoms
  residualBefore := transactionSession.residual
  residualAfter := pausedSession.residual
  receipt := pauseReceipt
  policyBefore := (0 : Nat)
  policyAfter := (100 : Nat)

def rewriteEvent : PolicyEvent (languages .rewrite) (policies .rewrite) where
  origin := rewriteSession.origin
  scope := rewriteSession.scope
  before := atoms
  after := atoms
  residualBefore := rewriteSession.residual
  residualAfter := rewrittenSession.residual
  receipt := betaReceipt
  policyBefore := (0 : Nat)
  policyAfter := (1 : Nat)

def commitEvent : PolicyEvent (languages .transaction) (policies .transaction) where
  origin := pausedSession.origin
  scope := pausedSession.scope
  before := atoms
  after := resultAtoms
  residualBefore := pausedSession.residual
  residualAfter := committedSession.residual
  receipt := commitReceipt
  policyBefore := (100 : Nat)
  policyAfter := (197 : Nat)

def afterPause : Workspace :=
  ⟨atoms, [⟨.rewrite, rewriteSession⟩, ⟨.transaction, pausedSession⟩], [⟨.transaction, pauseEvent⟩]⟩

def afterRewrite : Workspace :=
  ⟨atoms, [⟨.rewrite, rewrittenSession⟩, ⟨.transaction, pausedSession⟩],
    [⟨.transaction, pauseEvent⟩, ⟨.rewrite, rewriteEvent⟩]⟩

def afterCommit : Workspace :=
  ⟨resultAtoms, [⟨.rewrite, rewrittenSession⟩, ⟨.transaction, committedSession⟩],
    [⟨.transaction, pauseEvent⟩, ⟨.rewrite, rewriteEvent⟩, ⟨.transaction, commitEvent⟩]⟩

theorem pause_step : Step languages policies registered afterPause :=
  Step.fire (languages := languages) (policies := policies)
    ProgrammableSpaceInstances.Tag.transaction atoms atoms
    [⟨ProgrammableSpaceInstances.Tag.rewrite, rewriteSession⟩] [] [] transactionSession
    pauseReceipt (.matching checkpoint100) (100 : Nat) actual_pause
    ⟨rfl, by decide, rfl, by decide⟩

theorem rewrite_step : Step languages policies afterPause afterRewrite :=
  Step.fire (languages := languages) (policies := policies)
    ProgrammableSpaceInstances.Tag.rewrite atoms atoms []
    [⟨ProgrammableSpaceInstances.Tag.transaction, pausedSession⟩]
    [⟨ProgrammableSpaceInstances.Tag.transaction, pauseEvent⟩]
    rewriteSession betaReceipt (encodeTerm openTarget) (1 : Nat)
    ProgrammableSpaceInstances.rewrite_event_in_mixed_store ⟨by decide, rfl⟩

theorem commit_step : Step languages policies afterRewrite afterCommit :=
  Step.fire (languages := languages) (policies := policies)
    ProgrammableSpaceInstances.Tag.transaction atoms resultAtoms
    [⟨ProgrammableSpaceInstances.Tag.rewrite, rewrittenSession⟩] []
    [⟨ProgrammableSpaceInstances.Tag.transaction, pauseEvent⟩,
      ⟨ProgrammableSpaceInstances.Tag.rewrite, rewriteEvent⟩]
    pausedSession commitReceipt (.committed publication) (197 : Nat) actual_commit
    ⟨rfl, by decide, rfl, by decide⟩

/-- Both interpreters run while sharing the actual source store. -/
theorem actual_interleaved_run :
    Relation.ReflTransGen (Step languages policies) registered afterCommit :=
  ((Relation.ReflTransGen.single pause_step).tail rewrite_step).tail commit_step

theorem after_pause_started : Started languages policies afterPause :=
  step_started languages policies pause_step registered_started

theorem after_rewrite_started : Started languages policies afterRewrite :=
  step_started languages policies rewrite_step after_pause_started

theorem after_commit_started : Started languages policies afterCommit :=
  step_started languages policies commit_step after_rewrite_started

theorem actual_history_is_sound : SoundHistory languages policies afterCommit :=
  started_sound_history languages policies afterCommit after_commit_started

theorem execution_keeps_scopes_and_origins :
    afterCommit.pending.map (sessionKey languages policies) =
      registered.pending.map (sessionKey languages policies) :=
  run_keeps_session_scopes languages policies actual_interleaved_run

theorem held_packet_survives_beta :
    afterRewrite.pending[1]? = afterPause.pending[1]? ∧
      afterRewrite.atoms = checkpoint100.before := ⟨rfl, rfl⟩

theorem distinct_accounts_and_three_events :
    rewrittenSession.policyState = (1 : Nat) ∧ committedSession.policyState = (197 : Nat) ∧
      afterCommit.history.map Sigma.fst = [.transaction, .rewrite, .transaction] := ⟨rfl, rfl, rfl⟩

theorem exhausted_publication_observed :
    (languages .transaction).observes committedSession.residual ⟨resultAtoms, publication.rows⟩ :=
  ⟨publication_store.symm, rfl⟩

theorem partial_rows_are_not_an_outcome (outcome : ProgrammableSpaceMM2.Outcome) :
    ¬ (languages .transaction).observes pausedSession.residual outcome := id

theorem changed_store_blocks_held_packet (receipt : ProgrammableSpaceMM2Resumable.Receipt)
    (target : List Atom) (after : ProgrammableSpaceMM2Resumable.Residual) :
    ¬ (languages .transaction).advance .leaveInert (.symbol "new" :: atoms)
      pausedSession.residual receipt target after := by
  apply ProgrammableSpaceMM2Resumable.stale_snapshot_cannot_step
  intro impossible
  have lengths := congrArg List.length impossible
  change atoms.length + 1 = atoms.length at lengths
  omega

theorem lower_budget_rejects_actual_commit :
    ¬ (transactionPolicy 196).permits (100 : Nat) .leaveInert atoms
      (.matching checkpoint100) commitReceipt resultAtoms (.committed publication) (197 : Nat) := by
  intro permitted
  exact (by decide : ¬ (197 : Nat) ≤ 196) permitted.2.1

namespace Material

open _root_.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafDescent.Controls
open Mettapedia.GSLT

def read (atom : Atom) (space : Workspace) : Prop := atom ∈ space.atoms

abbrev coding := Logic.ProgrammableSpaceAtomCoding.coding

def beforeState : (ProgrammableSpaceMaterial.states languages policies).obj (world 4) :=
  ⟨afterRewrite, after_rewrite_started, by decide⟩

def actualContinuation := ProgrammableSpaceMaterialFamilies.actionContinuation
  languages policies read coding (world 4) beforeState afterCommit (.execute commit_step)

theorem publication_has_material_continuation :
    ProgrammableSpaceMaterialFamilies.materialContinuation languages policies read coding
        (world 4) beforeState afterCommit (.execute commit_step) ∈
      ((ProgrammableSpaceMaterialFamilies.continuations languages policies read coding).models
        (ProgrammableSpaceMaterialFamilies.parameter languages policies read coding (world 5)
          ((ProgrammableSpaceMaterial.states languages policies).map
            (ProgrammableSpaceMaterial.extend (world 4)) beforeState))).carrier :=
  ProgrammableSpaceMaterialFamilies.action_is_material_member languages policies read coding
    (world 4) beforeState afterCommit (.execute commit_step)

theorem material_decodes_actual_continuation :
    ((ProgrammableSpaceMaterialFamilies.continuations languages policies read coding).models
      (ProgrammableSpaceMaterialFamilies.parameter languages policies read coding (world 5)
        ((ProgrammableSpaceMaterial.states languages policies).map
          (ProgrammableSpaceMaterial.extend (world 4)) beforeState))).decode
        ⟨ProgrammableSpaceMaterialFamilies.materialContinuation languages policies read coding
          (world 4) beforeState afterCommit (.execute commit_step),
            publication_has_material_continuation⟩ = actualContinuation :=
  ProgrammableSpaceMaterialFamilies.decode_action_continuation languages policies read coding
    (world 4) beforeState afterCommit (.execute commit_step)

theorem publication_adds_declared_fact :
    ¬ read ProgrammableSpaceMM2ReceiptControls.reachable afterRewrite ∧
      read ProgrammableSpaceMM2ReceiptControls.reachable afterCommit := by
  unfold read
  decide +kernel

theorem private_and_foreign_steps_preserve_current_support :
    ProgrammableSpaceReadings.support coding registered.atoms =
      ProgrammableSpaceReadings.support coding afterPause.atoms ∧
    ProgrammableSpaceReadings.support coding afterPause.atoms =
      ProgrammableSpaceReadings.support coding afterRewrite.atoms := ⟨rfl, rfl⟩

/-- An inert empty source has no continuation, while the actual retained
matcher above supplies one in the very same family interpretation. -/
theorem empty_source_has_no_continuation :
    ¬ Nonempty ((ProgrammableSpaceMaterialFamilies.continuations languages policies read coding).native.obj
      (ProgrammableSpaceMaterialFamilies.parameter languages policies read coding (world 5)
        (ProgrammableSpaceMaterialFamilies.emptyState languages policies (world 5)))) := by
  rintro ⟨continuation⟩
  exact ProgrammableSpaceMaterialFamilies.empty_space_has_no_continuation
    languages policies read coding (world 5) continuation

end Material

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceResumableInstances
