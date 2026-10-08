import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2

/-!+# Retained structural matching as a programmable-space language

The active residual is the actual structural matching packet: unfinished
syntax, parent scans, private ordered rows and the accumulated poll charge.
Each grant resumes that packet. A completed batch publishes through the
rule-scoped sink executor and refines to the atomic source adapter.

The store must still be the captured store before either a private step or
publication. Concurrent edits therefore require an explicit restart or a
separate validated snapshot policy. No partial row list becomes public and
no scheduler budget is mistaken for a completion certificate. Poll charges
belong to this formal cursor; they are not C instruction or wall-time costs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Resumable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor
open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.Core.ProgrammableSpace (Language)

abbrev Request := ProgrammableSpaceMM2.Request
abbrev Scope := ProgrammableSpaceMM2.Scope

abbrev PacketFor (space : List Atom) (request : Request) :=
  Packet (StructuralQuanta.provider
    (entries (ProgrammableSpaceMM2Matching.snapshot space request)))
    (NativeControlCursor.client Row) ()

abbrev FinishedFor (space : List Atom) (request : Request) :=
  Finished (StructuralQuanta.provider
    (entries (ProgrammableSpaceMM2Matching.snapshot space request)))
    (Return := fun _ _ => List Row) ()

/-- A reachable private packet, with its complete budget and charge history. -/
structure Checkpoint where
  before : List Atom
  request : Request
  granted : Nat
  spent : Nat
  packet : PacketFor before request
  reached : ProgrammableSpaceMM2Matching.run before request granted = (spent, .paused packet)

def Checkpoint.start (space : List Atom) (request : Request) : Checkpoint where
  before := space
  request := request
  granted := 0
  spent := 0
  packet := ProgrammableSpaceMM2Matching.packet space request
  reached := rfl

/-- The matched prefix remains private even when it contains answers. -/
def Checkpoint.privateRows (checkpoint : Checkpoint) : List Row :=
  match checkpoint.packet.2.1 with
  | .pulling reversed => reversed.reverse
  | .finished rows => rows

def Checkpoint.remainingSyntax (checkpoint : Checkpoint) : StructuralQuanta.State :=
  checkpoint.packet.2.2

/-- This executes the retained provider state; it does not rerun initialization. -/
def Checkpoint.resume (checkpoint : Checkpoint) (grant : Nat) :
    Nat × ProgrammableSpaceMM2Matching.Result checkpoint.before checkpoint.request :=
  Mettapedia.Machines.Cursor.resume
    (StructuralQuanta.provider
      (entries (ProgrammableSpaceMM2Matching.snapshot checkpoint.before checkpoint.request)))
    (NativeControlCursor.client Row) (fun _ _ => 1) grant
    (checkpoint.spent, .paused checkpoint.packet)

theorem Checkpoint.resume_exact (checkpoint : Checkpoint) (grant : Nat) :
    checkpoint.resume grant = ProgrammableSpaceMM2Matching.run
      checkpoint.before checkpoint.request (checkpoint.granted + grant) := by
  rw [ProgrammableSpaceMM2Matching.pause_resume, checkpoint.reached]
  rfl

def Checkpoint.afterPause (checkpoint : Checkpoint) (grant spent : Nat)
    (packet : PacketFor checkpoint.before checkpoint.request)
    (paused : checkpoint.resume grant = (spent, .paused packet)) : Checkpoint where
  before := checkpoint.before
  request := checkpoint.request
  granted := checkpoint.granted + grant
  spent := spent
  packet := packet
  reached := (checkpoint.resume_exact grant).symm.trans paused

theorem Checkpoint.pause_then_resume (checkpoint : Checkpoint) (first spent later : Nat)
    (packet : PacketFor checkpoint.before checkpoint.request)
    (paused : checkpoint.resume first = (spent, .paused packet)) :
    (checkpoint.afterPause first spent packet paused).resume later =
      checkpoint.resume (first + later) := by
  rw [Checkpoint.resume_exact, Checkpoint.resume_exact]
  exact congrArg (ProgrammableSpaceMM2Matching.run checkpoint.before checkpoint.request)
    (Nat.add_assoc checkpoint.granted first later)

theorem Checkpoint.zero_grant (checkpoint : Checkpoint) :
    checkpoint.resume 0 = (checkpoint.spent, .paused checkpoint.packet) :=
  Mettapedia.Machines.Cursor.resume_zero _ _ _ _

/-- Reaching return proves exhaustion of the complete row collector. -/
theorem Checkpoint.completed_rows (checkpoint : Checkpoint) (grant spent : Nat)
    (result : FinishedFor checkpoint.before checkpoint.request)
    (completed : checkpoint.resume grant = (spent, .done result)) :
    ∃ fuel, HostCalls.collect
      (StructuralQuanta.pull
        (entries (ProgrammableSpaceMM2Matching.snapshot checkpoint.before checkpoint.request)))
      fuel (ProgrammableSpaceMM2Matching.initial checkpoint.before checkpoint.request) =
        some result.2.1 := by
  have exactRun := (checkpoint.resume_exact grant).symm.trans completed
  cases total : checkpoint.granted + grant with
  | zero =>
      rw [total] at exactRun
      cases Prod.mk.inj exactRun |>.2
  | succ fuel =>
      rw [total] at exactRun
      have observation := congrArg (fun outcome => NativeControlCursor.published
        (StructuralQuanta.pull
          (entries (ProgrammableSpaceMM2Matching.snapshot checkpoint.before checkpoint.request)))
        outcome.2) exactRun
      change NativeControlCursor.published _
        (ProgrammableSpaceMM2Matching.run checkpoint.before checkpoint.request (fuel + 1)).2 =
          some result.2.1 at observation
      unfold ProgrammableSpaceMM2Matching.run ProgrammableSpaceMM2Matching.packet at observation
      rw [NativeControlCursor.advance_collect] at observation
      refine ⟨fuel, ?_⟩
      simpa using observation

inductive Residual where
  | matching (checkpoint : Checkpoint)
  | committed (receipt : ProgrammableSpaceMM2.Receipt)

structure Receipt where
  grant : Nat
  spentBefore : Nat
  spentAfter : Nat
  publication : Option ProgrammableSpaceMM2.Receipt

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
        (ProgrammableSpaceMM2Matching.finalize checkpoint.before checkpoint.request result.2.1)
        (.committed ⟨checkpoint.request, checkpoint.before, result.2.1⟩)

def Observes : Residual → ProgrammableSpaceMM2.Outcome → Prop
  | .matching _, _ => False
  | .committed receipt, outcome =>
      outcome.store = receipt.after ∧ outcome.rows = receipt.rows

def language : Language Atom where
  Scope := Scope
  Request := Request
  Residual := Residual
  Outcome := ProgrammableSpaceMM2.Outcome
  Receipt := Receipt
  admit := ProgrammableSpaceMM2.Admitted
  initial _ request space := .matching (Checkpoint.start space request)
  advance := Advance
  observes := Observes

def atomicResidual : Residual → ProgrammableSpaceMM2.Residual
  | .matching checkpoint => .pending checkpoint.request
  | .committed receipt => .committed receipt

/-- A private step stutters publicly; a complete step is the existing source
event, with the same exact physical receipt and source scope. -/
theorem advance_refines_atomic {scope : Scope} {space target : List Atom}
    {before after : Residual} {receipt : Receipt}
    (step : Advance scope space before receipt target after) :
    (receipt.publication = none ∧ target = space ∧
      atomicResidual after = atomicResidual before) ∨
    ∃ publication, receipt.publication = some publication ∧
      ProgrammableSpaceMM2.Advance scope space (atomicResidual before)
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
    cRuleScopedSourceWorkQueueStep scope space = some target := by
  rcases advance_refines_atomic step with privateStep | ⟨actual, _, sourceStep⟩
  · rw [privateStep.1] at published
    cases published
  · exact ProgrammableSpaceMM2.advance_source_step sourceStep

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

/-- Exhaustion has a finite grant for every reachable paused checkpoint.
This bound belongs to the proof, not to the runtime's scheduling policy. -/
theorem Checkpoint.finite_completion (checkpoint : Checkpoint) :
    ∃ (grant spent : Nat) (result : FinishedFor checkpoint.before checkpoint.request),
      checkpoint.resume grant = (spent, .done result) := by
  let allowance := ProgrammableSpaceMM2Matching.allowance checkpoint.before checkpoint.request
  have enough : StructuralQuanta.remainingCost
      (entries (ProgrammableSpaceMM2Matching.snapshot checkpoint.before checkpoint.request))
      (ProgrammableSpaceMM2Matching.initial checkpoint.before checkpoint.request) <
        checkpoint.granted + allowance := by
    dsimp [allowance, ProgrammableSpaceMM2Matching.allowance]
    omega
  have collected := StructuralQuanta.collect_complete _ _ _ enough
  have observed := ProgrammableSpaceMM2Matching.run_observation
    checkpoint.before checkpoint.request (checkpoint.granted + allowance)
  rw [collected] at observed
  have shifted : checkpoint.resume (allowance + 1) =
      ProgrammableSpaceMM2Matching.run checkpoint.before checkpoint.request
        (checkpoint.granted + allowance + 1) := by
    rw [checkpoint.resume_exact, Nat.add_assoc]
  rw [← shifted] at observed
  cases computed : checkpoint.resume (allowance + 1) with
  | mk spent result =>
      cases result with
      | paused packet =>
          rw [computed] at observed
          cases observed
      | done result => exact ⟨allowance + 1, spent, result, computed⟩

theorem selected_checkpoint_has_publication (scope : Scope) (checkpoint : Checkpoint)
    (selected : MM2MatchingBatch.SelectedFor scope checkpoint.before checkpoint.request.directive) :
    ∃ receipt target publication,
      Advance scope checkpoint.before (.matching checkpoint) receipt target (.committed publication) ∧
      receipt.publication = some publication ∧
      target = cFireRuleScopedSourceExecFact checkpoint.before checkpoint.request.directive := by
  obtain ⟨grant, spent, result, completed⟩ := checkpoint.finite_completion
  obtain ⟨fuel, collected⟩ := checkpoint.completed_rows grant spent result completed
  exact ⟨_, _, _, .commit checkpoint grant spent result selected completed, rfl,
    ProgrammableSpaceMM2Matching.completed_finalize _ _ fuel _ collected⟩

def Transition (scope : Scope) (before after : List Atom × Residual) : Prop :=
  ∃ receipt, Advance scope before.1 before.2 receipt after.1 after.2

def AtomicTransition (scope : Scope)
    (before after : List Atom × ProgrammableSpaceMM2.Residual) : Prop :=
  ∃ receipt, ProgrammableSpaceMM2.Advance scope before.1 before.2 receipt after.1 after.2

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

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Resumable
