import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajor
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Resumable

/-!
# The retained MM2 cursor with row-major publication

The private packet, physical rows, unfinished syntax, accumulated grants and
poll costs are the existing structural cursor. This language changes only
the completed batch's finalization profile. Its public observation uses the
row-major receipt interpretation and its atomic comparison uses the matching
row-major language; no sink-major conclusion is reused for that step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorResumable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor
open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.Core.ProgrammableSpace (Language)

abbrev Request := ProgrammableSpaceMM2.Request
abbrev Scope := ProgrammableSpaceMM2.Scope
abbrev Checkpoint := ProgrammableSpaceMM2Resumable.Checkpoint
abbrev PacketFor := ProgrammableSpaceMM2Resumable.PacketFor
abbrev FinishedFor := ProgrammableSpaceMM2Resumable.FinishedFor
abbrev Residual := ProgrammableSpaceMM2Resumable.Residual
abbrev Receipt := ProgrammableSpaceMM2Resumable.Receipt

inductive Advance (scope : Scope) : List Atom → Residual → Receipt →
    List Atom → Residual → Prop where
  | pause (checkpoint : Checkpoint) (grant spent : Nat)
      (packet : PacketFor checkpoint.before checkpoint.request)
      (selected : MM2MatchingBatch.SelectedFor scope checkpoint.before checkpoint.request.directive)
      (paused : checkpoint.resume grant = (spent, .paused packet)) :
      Advance scope checkpoint.before (.matching checkpoint)
        ⟨grant, checkpoint.spent, spent, none⟩ checkpoint.before
        (.matching (checkpoint.afterPause grant spent packet paused))
  | commit (checkpoint : Checkpoint) (grant spent : Nat)
      (result : FinishedFor checkpoint.before checkpoint.request)
      (selected : MM2MatchingBatch.SelectedFor scope checkpoint.before checkpoint.request.directive)
      (completed : checkpoint.resume grant = (spent, .done result)) :
      Advance scope checkpoint.before (.matching checkpoint)
        ⟨grant, checkpoint.spent, spent,
          some ⟨checkpoint.request, checkpoint.before, result.2.1⟩⟩
        (ProgrammableSpaceMM2RowMajor.finalize checkpoint.before checkpoint.request result.2.1)
        (.committed ⟨checkpoint.request, checkpoint.before, result.2.1⟩)

def Observes : Residual → ProgrammableSpaceMM2.Outcome → Prop
  | .matching _, _ => False
  | .committed receipt, outcome =>
      outcome.store = ProgrammableSpaceMM2RowMajor.after receipt ∧ outcome.rows = receipt.rows

def language : Language Atom where
  Scope := Scope
  Request := Request
  Residual := Residual
  Outcome := ProgrammableSpaceMM2.Outcome
  Receipt := Receipt
  admit := ProgrammableSpaceMM2.Admitted
  initial _ request space := .matching (ProgrammableSpaceMM2Resumable.Checkpoint.start space request)
  advance := Advance
  observes := Observes

def atomicResidual : Residual → ProgrammableSpaceMM2.Residual
  | .matching checkpoint => .pending checkpoint.request
  | .committed receipt => .committed receipt

/-- A private step stutters publicly; a complete step is the row-major source
event, with the same exact physical receipt and source scope. -/
theorem advance_refines_atomic {scope : Scope} {space target : List Atom}
    {before after : Residual} {receipt : Receipt}
    (step : Advance scope space before receipt target after) :
    (receipt.publication = none ∧ target = space ∧
      atomicResidual after = atomicResidual before) ∨
    ∃ publication, receipt.publication = some publication ∧
      ProgrammableSpaceMM2RowMajor.Advance scope space (atomicResidual before)
        publication target (atomicResidual after) := by
  cases step with
  | pause checkpoint grant spent packet selected paused => exact Or.inl ⟨rfl, rfl, rfl⟩
  | commit checkpoint grant spent result selected completed =>
      obtain ⟨fuel, collected⟩ := checkpoint.completed_rows grant spent result completed
      exact Or.inr ⟨_, rfl,
        .commit checkpoint.before checkpoint.request fuel result.2.1 selected collected⟩

theorem pending_does_not_publish (checkpoint : Checkpoint)
    (outcome : ProgrammableSpaceMM2.Outcome) :
    ¬ language.observes (.matching checkpoint) outcome := id

theorem private_step_preserves_store {scope : Scope} {space target : List Atom}
    {before after : Residual} {receipt : Receipt}
    (step : Advance scope space before receipt target after)
    (privateStep : receipt.publication = none) : target = space := by
  cases step with
  | pause => rfl
  | commit => cases privateStep

theorem completed_source_step {scope : Scope} {space target : List Atom}
    {before after : Residual} {receipt : Receipt}
    (step : Advance scope space before receipt target after)
    (publication : ProgrammableSpaceMM2.Receipt)
    (published : receipt.publication = some publication) :
    ProgrammableSpaceMM2RowMajor.sourceStep scope space = some target := by
  rcases advance_refines_atomic step with privateStep | ⟨actual, _, sourceStep⟩
  · rw [privateStep.1] at published
    cases published
  · exact ProgrammableSpaceMM2RowMajor.advance_source_step sourceStep

theorem stale_snapshot_cannot_step {scope : Scope} (checkpoint : Checkpoint)
    (current target : List Atom) (receipt : Receipt) (after : Residual)
    (changed : current ≠ checkpoint.before) :
    ¬ Advance scope current (.matching checkpoint) receipt target after := by
  intro step
  cases step <;> exact changed rfl

theorem committed_does_not_fire {scope : Scope} {space target : List Atom}
    (committed : ProgrammableSpaceMM2.Receipt) (receipt : Receipt) (after : Residual) :
    ¬ Advance scope space (.committed committed) receipt target after := by
  intro impossible
  cases impossible

theorem selected_checkpoint_has_publication (scope : Scope) (checkpoint : Checkpoint)
    (selected : MM2MatchingBatch.SelectedFor scope checkpoint.before checkpoint.request.directive) :
    ∃ receipt target publication,
      Advance scope checkpoint.before (.matching checkpoint) receipt target (.committed publication) ∧
      receipt.publication = some publication ∧
      target = ProgrammableSpaceMM2RowMajor.fire checkpoint.before checkpoint.request.directive := by
  obtain ⟨grant, spent, result, completed⟩ := checkpoint.finite_completion
  obtain ⟨fuel, collected⟩ := checkpoint.completed_rows grant spent result completed
  exact ⟨_, _, _, .commit checkpoint grant spent result selected completed, rfl,
    ProgrammableSpaceMM2RowMajor.completed_finalize _ _ fuel _ collected⟩

def Transition (scope : Scope) (before after : List Atom × Residual) : Prop :=
  ∃ receipt, Advance scope before.1 before.2 receipt after.1 after.2

def AtomicTransition (scope : Scope)
    (before after : List Atom × ProgrammableSpaceMM2.Residual) : Prop :=
  ∃ receipt, ProgrammableSpaceMM2RowMajor.Advance scope before.1 before.2 receipt after.1 after.2

def atomicConfiguration (state : List Atom × Residual) :
    List Atom × ProgrammableSpaceMM2.Residual := (state.1, atomicResidual state.2)

theorem transition_refines_atomic_run {scope : Scope} {before after : List Atom × Residual}
    (step : Transition scope before after) :
    Relation.ReflTransGen (AtomicTransition scope)
      (atomicConfiguration before) (atomicConfiguration after) := by
  obtain ⟨receipt, advanced⟩ := step
  rcases advance_refines_atomic advanced with ⟨_, sameStore, sameResidual⟩ |
      ⟨publication, _, source⟩
  · have same : atomicConfiguration after = atomicConfiguration before :=
      Prod.ext sameStore sameResidual
    rw [same]
  · exact Relation.ReflTransGen.single ⟨publication, source⟩

/-- Arbitrarily many private grants preserve the same atomic source meaning.
The actual fine execution still retains each checkpoint and budget receipt. -/
theorem run_refines_atomic_run {scope : Scope} {before after : List Atom × Residual}
    (execution : Relation.ReflTransGen (Transition scope) before after) :
    Relation.ReflTransGen (AtomicTransition scope)
      (atomicConfiguration before) (atomicConfiguration after) := by
  induction execution with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step previous => exact previous.trans (transition_refines_atomic_run step)

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorResumable
