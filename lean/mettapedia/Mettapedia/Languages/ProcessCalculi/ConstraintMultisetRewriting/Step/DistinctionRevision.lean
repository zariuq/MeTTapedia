import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionMinimization

/-!
# Behaviour-preserving revision on the transform step

A finite machine can move to a configuration of another implementation when
the two configurations agree on their current reading and have matching
future actions. The state can contain an active program as well as its data.
The revision guard computes the existing greatest behavioural equivalence.
Candidates are supplied separately, so equivalence alone cannot propose edits.

Every run that interleaves actions and admitted revisions has a run of the
original machine with the same visible action word and final reading.
This uses branching equivalence of the machine before revision is enabled.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionFinite.Machine

universe uS uA uV

variable {S : Type uS} {A : Type uA} {V : Type uV}
  [DecidableEq S] [Fintype S] [Fintype A] [DecidableEq V]

variable (M : Machine S A V)

/-- The additional action chooses an equivalent configuration from a proposal list. -/
def withRevision (proposals : S → List S) : Machine S (A ⊕ Unit) V where
  read := M.read
  next s
    | .inl action => M.next s action
    | .inr () => (proposals s).filter fun target => decide ((s, target) ∈ M.behaviour)

theorem revision_iff (proposals : S → List S) (before after : S) :
    after ∈ (M.withRevision proposals).next before (.inr ()) ↔
      after ∈ proposals before ∧ M.system.Bisimilar before after := by
  simp [withRevision, M.mem_behaviour_iff]

/-- A revision consumes the current occurrence and makes one holding the new
configuration. Its admission agrees with the independently defined equivalence. -/
theorem revision_moves_iff (proposals : S → List S) (before after : ℕ × S) :
    Race.Generic.Moves (M.withRevision proposals).step.toStep offers before (.inr ()) after ↔
      after.1 = before.1 + 1 ∧ after.2 ∈ proposals before.2 ∧
        M.system.Bisimilar before.2 after.2 := by
  rw [moves_iff, revision_iff]

private theorem match_ordinary {s t result : S} (related : (s, t) ∈ M.behaviour)
    (action : A) (member : result ∈ M.next s action) :
    ∃ other ∈ M.next t action, (result, other) ∈ M.behaviour :=
  (M.stable_good M.behaviour_stable related).2 action |>.1 result member

/-- An action word read off the actual firings of a table machine. -/
def actionWord {s : ℕ × S} (run : M.step.Run s) : List A :=
  run.word.map fun entry => entry.2.1

/-- Revisions are internal when observing the original actions. -/
def visibleActions (word : List (A ⊕ Unit)) : List A :=
  word.filterMap fun
    | .inl action => some action
    | .inr _ => none

/-- An original run matches an extended run from any behaviourally equivalent
configuration. The final states still agree on all future actions. -/
theorem reflect_revision_run (proposals : S → List S) {s : ℕ × S}
    (run : (M.withRevision proposals).step.Run s) {baseline : ℕ × S}
    (related : (s.2, baseline.2) ∈ M.behaviour) :
    ∃ original : M.step.Run baseline,
      M.actionWord original = visibleActions ((M.withRevision proposals).actionWord run) ∧
        (run.last.2, original.last.2) ∈ M.behaviour := by
  induction run generalizing baseline with
  | nil =>
      exact ⟨.nil baseline, rfl, related⟩
  | @cons source firing admitted rest ih =>
      obtain ⟨label, target⟩ := firing
      cases label with
      | inl action =>
          change target ∈ M.next source.2 action at admitted
          obtain ⟨other, allowed, same⟩ := M.match_ordinary related action admitted
          obtain ⟨tail, labels, final⟩ := ih (baseline := (baseline.1 + 1, other)) same
          exact ⟨.cons (action, other) allowed tail, congrArg (List.cons action) labels, final⟩
      | inr edit =>
          cases edit
          have revised := (M.revision_iff proposals source.2 target).mp admitted |>.2
          have same := (M.mem_behaviour_iff target baseline.2).mpr
            (M.system.bisimilar_trans (M.system.bisimilar_symm revised)
              ((M.mem_behaviour_iff _ _).mp related))
          obtain ⟨original, labels, final⟩ := ih same
          exact ⟨original, labels, final⟩

/-- Ordinary executions lift without inserting revisions. -/
def lift_ordinary_run (proposals : S → List S) :
    {s : ℕ × S} → M.step.Run s → (M.withRevision proposals).step.Run s
  | _, .nil s => .nil s
  | _, .cons f admitted rest => .cons (.inl f.1, f.2) admitted (lift_ordinary_run proposals rest)

theorem lift_ordinary_run_readback (proposals : S → List S) {s : ℕ × S} (run : M.step.Run s) :
    (M.lift_ordinary_run proposals run).last = run.last ∧
      visibleActions ((M.withRevision proposals).actionWord (M.lift_ordinary_run proposals run)) =
        M.actionWord run := by
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | cons firing admitted rest ih =>
      exact ⟨ih.1, congrArg (List.cons firing.1) ih.2⟩

/-- The allowed revisions preserve exactly the visible action words and final readings. -/
theorem revision_trace_iff (proposals : S → List S) (s : ℕ × S) (actions : List A) (value : V) :
    (∃ run : (M.withRevision proposals).step.Run s,
      visibleActions ((M.withRevision proposals).actionWord run) = actions ∧ M.read run.last.2 = value) ↔
    ∃ run : M.step.Run s, M.actionWord run = actions ∧ M.read run.last.2 = value := by
  constructor
  · rintro ⟨run, labels, result⟩
    obtain ⟨original, sameLabels, sameEnd⟩ :=
      M.reflect_revision_run proposals run (M.behaviouralSetoid.iseqv.refl s.2)
    exact ⟨original, sameLabels.trans labels, (M.behaviour_preserves sameEnd).symm.trans result⟩
  · rintro ⟨run, labels, result⟩
    obtain ⟨last, word⟩ := M.lift_ordinary_run_readback proposals run
    exact ⟨M.lift_ordinary_run proposals run, word.trans labels, by rwa [last]⟩

namespace Controls

/-- Configurations 0 and 1 act alike forever. Configuration 2 has the same
current reading but will expose the distinguished result at 3. -/
def machine : Machine (Fin 4) Unit Bool :=
  ⟨fun s => s = 3, fun s _ => [if s = 2 then 3 else s]⟩

def proposals (_ : Fin 4) : List (Fin 4) := [1, 2]

theorem equal_readings : machine.read 0 = machine.read 2 := by decide

theorem admits_only_equivalent_configuration :
    (machine.withRevision proposals).next 0 (.inr ()) = [1] := by decide +kernel

theorem accepted_revision_fires :
    Race.Generic.Moves (machine.withRevision proposals).step.toStep offers
      (0, 0) (.inr ()) (1, 1) :=
  (moves_iff _ _ _ _).mpr ⟨rfl, by rw [admits_only_equivalent_configuration]; simp⟩

theorem rejects_delayed_observation_change (clock : ℕ) :
    ¬ Race.Generic.Moves (machine.withRevision proposals).step.toStep offers
      (0, 0) (.inr ()) (clock, 2) := by
  intro moved
  have found := (moves_iff _ _ _ _).mp moved |>.2
  rw [admits_only_equivalent_configuration] at found
  simp at found

end Controls

#print axioms revision_moves_iff
#print axioms revision_trace_iff
#print axioms Controls.rejects_delayed_observation_change

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionFinite.Machine
