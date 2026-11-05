import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.CHR.Operational

/-!+# Propagation history for standing interactions

A standing interaction with no takes is admitted once per installed rule
and ordered physical read selection. Fresh schema variables and output
identities are not part of that key. Repeated direct queries remain direct
queries. Consuming interactions retain their original transition relation.

History and the interaction result are published by one transition. This
does not establish termination when new matching occurrences keep arriving,
nor does it prescribe a scheduler for several eligible selections.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PropagationHistory

universe u v w
variable {Installation : Type u} {O : Type v} {State : Type w}

structure Key (Installation : Type u) (O : Type v) where
  installation : Installation
  read : List O
  deriving DecidableEq

/-- An installation identity includes the persistent rule's owner/captures
and revision. A new freshening scope is not a new installation. -/
structure Event (Installation : Type u) (O : Type v) where
  installation : Installation
  standing : Bool
  selection : Selection O

def Event.key (event : Event Installation O) : Key Installation O :=
  ⟨event.installation,event.selection.read⟩

def Event.tracked (event : Event Installation O) : Bool :=
  event.standing && event.selection.taken.isEmpty

def Fresh (event : Event Installation O) (history : List (Key Installation O)) : Prop :=
  event.tracked = true → event.key ∉ history

def record (event : Event Installation O) (history : List (Key Installation O)) : List (Key Installation O) :=
  if event.tracked then event.key :: history else history

theorem tracked_iff (event : Event Installation O) :
    event.tracked = true ↔ event.standing = true ∧ event.selection.taken = [] := by
  simp [Event.tracked]

theorem fresh_empty (event : Event Installation O) : Fresh event [] := by
  intro _ member
  cases member

theorem record_mono (event : Event Installation O) (history : List (Key Installation O)) :
    ∀ key ∈ history, key ∈ record event history := by
  intro key member
  unfold record
  split
  · exact List.mem_cons_of_mem _ member
  · exact member

theorem propagation_recorded {event : Event Installation O} (standing : event.standing = true)
    (readOnly : event.selection.taken = []) (history : List (Key Installation O)) :
    event.key ∈ record event history := by
  simp [record,(tracked_iff event).mpr ⟨standing,readOnly⟩]

theorem propagation_cannot_replay {event : Event Installation O} (standing : event.standing = true)
    (readOnly : event.selection.taken = []) (history : List (Key Installation O)) :
    ¬ Fresh event (record event history) := by
  intro fresh
  exact fresh ((tracked_iff event).mpr ⟨standing,readOnly⟩)
    (propagation_recorded standing readOnly history)

theorem same_selection_cannot_replay {first second : Event Installation O}
    (standingFirst : first.standing = true) (readFirst : first.selection.taken = [])
    (standingSecond : second.standing = true) (readSecond : second.selection.taken = [])
    (installation : first.installation = second.installation)
    (reads : first.selection.read = second.selection.read) (history : List (Key Installation O)) :
    ¬ Fresh second (record first history) := by
  have sameKey : first.key = second.key := by simp only [Event.key,installation,reads]
  intro fresh
  exact fresh ((tracked_iff second).mpr ⟨standingSecond,readSecond⟩)
    (sameKey ▸ propagation_recorded standingFirst readFirst history)

theorem consuming_untracked {event : Event Installation O} (consumes : event.selection.taken ≠ []) :
    event.tracked = false := by
  cases tracked : event.tracked
  · rfl
  · exact False.elim (consumes ((tracked_iff event).mp tracked).2)

theorem consuming_fresh {event : Event Installation O} (consumes : event.selection.taken ≠ [])
    (history : List (Key Installation O)) : Fresh event history := by
  simp [Fresh,consuming_untracked consumes]

theorem consuming_record {event : Event Installation O} (consumes : event.selection.taken ≠ [])
    (history : List (Key Installation O)) : record event history = history := by
  simp [record,consuming_untracked consumes]

theorem direct_fresh {event : Event Installation O} (direct : event.standing = false)
    (history : List (Key Installation O)) : Fresh event history := by
  simp [Fresh,Event.tracked,direct]

theorem direct_record {event : Event Installation O} (direct : event.standing = false)
    (history : List (Key Installation O)) : record event history = history := by
  simp [record,Event.tracked,direct]

def Step (core : Event Installation O → State → State → Prop) (event : Event Installation O)
    (before : State × List (Key Installation O)) (after : State × List (Key Installation O)) : Prop :=
  core event before.1 after.1 ∧ Fresh event before.2 ∧ after.2 = record event before.2

theorem Step.core {core : Event Installation O → State → State → Prop} {event : Event Installation O}
    {before after : State × List (Key Installation O)} (step : Step core event before after) :
    core event before.1 after.1 := step.1

theorem consuming_step_iff {core : Event Installation O → State → State → Prop}
    {event : Event Installation O} (consumes : event.selection.taken ≠ [])
    (before after : State × List (Key Installation O)) :
    Step core event before after ↔ core event before.1 after.1 ∧ after.2 = before.2 := by
  simp only [Step,consuming_record consumes]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,consuming_fresh consumes _,h.2⟩⟩

inductive Run (core : Event Installation O → State → State → Prop) :
    State × List (Key Installation O) → List (Event Installation O) →
      State × List (Key Installation O) → Prop where
  | nil (state) : Run core state [] state
  | cons {before middle after event events} : Step core event before middle →
      Run core middle events after → Run core before (event :: events) after

inductive CoreRun (core : Event Installation O → State → State → Prop) :
    State → List (Event Installation O) → State → Prop where
  | nil (state) : CoreRun core state [] state
  | cons {before middle after event events} : core event before middle →
      CoreRun core middle events after → CoreRun core before (event :: events) after

theorem Run.forget {core : Event Installation O → State → State → Prop}
    {before after : State × List (Key Installation O)} {events : List (Event Installation O)}
    (run : Run core before events after) : CoreRun core before.1 events after.1 := by
  induction run with
  | nil => exact .nil _
  | cons step _ rest => exact .cons step.core rest

theorem Run.history_mono {core : Event Installation O → State → State → Prop}
    {before after : State × List (Key Installation O)} {events : List (Event Installation O)}
    (run : Run core before events after) : ∀ key ∈ before.2, key ∈ after.2 := by
  induction run with
  | nil => exact fun _ member => member
  | @cons before middle after event events step _ rest =>
      intro key member
      apply rest key
      rw [step.2.2]
      exact record_mono event before.2 key member

theorem Run.no_recorded_firing {core : Event Installation O → State → State → Prop}
    {before after : State × List (Key Installation O)} {events : List (Event Installation O)}
    (run : Run core before events after) {event : Event Installation O}
    (member : event ∈ events) (tracked : event.tracked = true) : event.key ∉ before.2 := by
  induction run with
  | nil => cases member
  | @cons before middle after first rest step _ tail =>
      rcases List.mem_cons.mp member with rfl | later
      · exact step.2.1 tracked
      · intro recorded
        apply tail later
        rw [step.2.2]
        exact record_mono first before.2 event.key recorded

/-- Even intervening firings cannot make an earlier propagation eligible
again with the same installation and read identities. -/
theorem Run.no_later_replay {core : Event Installation O → State → State → Prop}
    {before middle after : State × List (Key Installation O)} {first later : Event Installation O}
    {events : List (Event Installation O)} (step : Step core first before middle)
    (run : Run core middle events after) (trackedFirst : first.tracked = true)
    (member : later ∈ events) (trackedLater : later.tracked = true) : later.key ≠ first.key := by
  intro same
  apply run.no_recorded_firing member trackedLater
  rw [step.2.2,same]
  simp [record,trackedFirst]

theorem consuming_run_lifts {core : Event Installation O → State → State → Prop}
    {before after : State} {events : List (Event Installation O)}
    (run : CoreRun core before events after) (consumes : ∀ event ∈ events, event.selection.taken ≠ [])
    (history : List (Key Installation O)) : Run core (before,history) events (after,history) := by
  induction run with
  | nil => exact .nil _
  | @cons before middle after event events step _ rest =>
      exact .cons ((consuming_step_iff (consumes event List.mem_cons_self)
        (before,history) (middle,history)).mpr ⟨step,rfl⟩)
        (rest (fun e member => consumes e (List.mem_cons_of_mem _ member)))

theorem consuming_runs_exact {core : Event Installation O → State → State → Prop}
    {before after : State} {events : List (Event Installation O)}
    (consumes : ∀ event ∈ events, event.selection.taken ≠ []) (history : List (Key Installation O)) :
    Run core (before,history) events (after,history) ↔ CoreRun core before events after :=
  ⟨Run.forget,fun run => consuming_run_lifts run consumes history⟩

theorem fresh_occurrence_changes_key {first second : Event Installation O} {occurrence : O}
    (absent : occurrence ∉ first.selection.read) (present : occurrence ∈ second.selection.read) :
    first.key ≠ second.key := by
  intro same
  have reads := congrArg Key.read same
  change first.selection.read = second.selection.read at reads
  rw [reads] at absent
  exact absent present

def chrEvent (installation : Nat) (selection : Mettapedia.Languages.CHR.Selection) : Event Nat Nat :=
  ⟨installation,true,⟨selection.removed.map Mettapedia.Languages.CHR.Occurrence.id,
    selection.kept.map Mettapedia.Languages.CHR.Occurrence.id,[]⟩⟩

def chrKey (key : Key Nat Nat) : Mettapedia.Languages.CHR.Key := ⟨key.installation,key.read⟩

theorem chr_key_agrees (installation : Nat) (selection : Mettapedia.Languages.CHR.Selection)
    (readOnly : selection.removed = []) :
    chrKey (chrEvent installation selection).key = selection.key installation := by
  simp only [chrKey,chrEvent,Event.key,Mettapedia.Languages.CHR.Selection.key,
    Mettapedia.Languages.CHR.Selection.heads,readOnly,List.append_nil]

theorem chr_record_agrees (installation : Nat) (selection : Mettapedia.Languages.CHR.Selection)
    (readOnly : selection.removed = []) (history : List (Key Nat Nat)) :
    (record (chrEvent installation selection) history).map chrKey =
      selection.key installation :: history.map chrKey := by
  have tracked : (chrEvent installation selection).tracked = true := by
    simp [chrEvent,Event.tracked,readOnly]
  simp only [record,tracked,if_true,List.map_cons,chr_key_agrees installation selection readOnly]

namespace Controls

def readSeven : Event Nat Nat := ⟨3,true,⟨[],[7],[8]⟩⟩
def readSevenAgain : Event Nat Nat := ⟨3,true,⟨[],[7],[19]⟩⟩
def readNewOccurrence : Event Nat Nat := ⟨3,true,⟨[],[9],[20]⟩⟩
def newInstallation : Event Nat Nat := ⟨4,true,⟨[],[7],[21]⟩⟩

theorem first_admitted : Fresh readSeven [] := fresh_empty _
theorem changing_only_the_output_cannot_replay : ¬ Fresh readSevenAgain (record readSeven []) := by
  exact same_selection_cannot_replay rfl rfl rfl rfl rfl rfl []
theorem new_physical_occurrence_admitted : Fresh readNewOccurrence (record readSeven []) := by
  simp [Fresh,record,readNewOccurrence,readSeven,Event.key,Event.tracked]
theorem new_installation_admitted : Fresh newInstallation (record readSeven []) := by
  simp [Fresh,record,newInstallation,readSeven,Event.key,Event.tracked]
theorem direct_query_can_repeat : Fresh {readSeven with standing := false} (record readSeven []) :=
  direct_fresh rfl _
theorem aliased_reads_retain_multiplicity :
    (⟨3,true,⟨[],[7,7],[8]⟩⟩ : Event Nat Nat).key ≠ readSeven.key := by decide

end Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PropagationHistory
