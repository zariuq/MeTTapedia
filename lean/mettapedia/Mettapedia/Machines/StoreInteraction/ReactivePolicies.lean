import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.ParkedWakeups

/-!
# Persistent registration, consumption, and triggering are distinct

These controls instantiate the existing reactive scheduler. A persistent
read-only registration can run forever on one unchanged fact: its semantics
is level-enabled, not implicitly once-per-tuple or false-to-true-edge enabled.
A one-shot registration stops after that same read. A one-shot consuming
receiver distinguishes the order of two otherwise independent additions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoreInteraction.ReactivePolicies

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

def label (o : Nat) : Nat := o
def readToken : Commit Nat Nat := Commit.keepOne 0
def readProc (persistent : Bool) (_ : Unit) : Parked Nat Nat :=
  ⟨{readToken}, fun _ => true, persistent⟩
def noWake (_ : Parked Nat Nat) (_ : Commit Nat Nat) : Prop := False
def ready : RState Nat Unit := ⟨{0}, {0}, Set.univ, Set.univ⟩

theorem read_is_allowed (persistent : Bool) :
    rAllowed label (readProc persistent) (fun _ => False) ready (.run () readToken) := by
  refine ⟨Set.mem_univ _, Set.mem_univ _, rfl, ?_⟩
  refine ⟨⟨by decide, by decide, by decide, ?_⟩, by decide⟩
  intro query member
  simp [readToken, Commit.keepOne] at member

theorem persistent_read_is_a_self_loop :
    rNext (readProc true) noWake ready (.run () readToken) = ready := by
  simp [rNext, readProc, ready, noWake, woken, readToken, Commit.keepOne, fire]

/-- An actual infinite run, with no store change and no rising edge. -/
def repeatedRead : Run (reactive label (readProc true) noWake (fun _ => False)) where
  state := fun _ => ready
  label := fun _ => .run () readToken
  allowed := fun _ => read_is_allowed true
  step := fun _ => persistent_read_is_a_self_loop.symm

theorem persistent_read_runs_without_new_data (n : Nat) :
    (repeatedRead.state n).store = {0} ∧ runTask () (repeatedRead.label n) := ⟨rfl, rfl⟩

theorem one_shot_read_unregisters :
    () ∉ (rNext (readProc false) noWake ready (.run () readToken)).parked := by
  simp [rNext, readProc]

theorem one_shot_read_cannot_run_again :
    ¬ rAllowed label (readProc false) (fun _ => False)
      (rNext (readProc false) noWake ready (.run () readToken)) (.run () readToken) := by
  intro allowed
  exact one_shot_read_unregisters allowed.1

def consumeZero : Commit Nat Nat := ⟨{0}, ∅, {2}, []⟩
def consumeOne : Commit Nat Nat := ⟨{1}, ∅, {3}, []⟩
def receiver (_ : Unit) : Parked Nat Nat :=
  ⟨{c | c = consumeZero ∨ c = consumeOne}, fun _ => true, false⟩
def empty : RState Nat Unit := ⟨∅, ∅, Set.univ, Set.univ⟩

def zeroFirst : List (RLabel Nat Nat Unit) :=
  [.env (Commit.makeOne 0), .run () consumeZero, .env (Commit.makeOne 1)]
def oneFirst : List (RLabel Nat Nat Unit) :=
  [.env (Commit.makeOne 1), .run () consumeOne, .env (Commit.makeOne 0)]

theorem zero_first_is_an_execution :
    (reactive label receiver noWake (fun _ => True)).Exec empty zeroFirst
      (zeroFirst.foldl (rNext receiver noWake) empty) := by
  refine .cons ?_ (.cons ?_ (.cons ?_ (.nil _)))
  · exact ⟨trivial, by decide, by decide⟩
  · refine ⟨Set.mem_univ _, Or.inl (Set.mem_univ _), Or.inl rfl, ?_⟩
    refine ⟨⟨by decide, by decide, by decide, ?_⟩, by decide⟩
    intro query member
    simp [consumeZero] at member
  · exact ⟨trivial, by decide, by decide⟩

theorem one_first_is_an_execution :
    (reactive label receiver noWake (fun _ => True)).Exec empty oneFirst
      (oneFirst.foldl (rNext receiver noWake) empty) := by
  refine .cons ?_ (.cons ?_ (.cons ?_ (.nil _)))
  · exact ⟨trivial, by decide, by decide⟩
  · refine ⟨Set.mem_univ _, Or.inl (Set.mem_univ _), Or.inr rfl, ?_⟩
    refine ⟨⟨by decide, by decide, by decide, ?_⟩, by decide⟩
    intro query member
    simp [consumeOne] at member
  · exact ⟨trivial, by decide, by decide⟩

theorem additions_are_observably_ordered_by_a_one_shot_receiver :
    (zeroFirst.foldl (rNext receiver noWake) empty).store = {1, 2} ∧
      (oneFirst.foldl (rNext receiver noWake) empty).store = {0, 3} := by decide

/-! Fairness of a registration is not fairness of each of its matches. -/

def readSecond : Commit Nat Nat := Commit.keepOne 1
def twoReadProc (_ : Unit) : Parked Nat Nat :=
  ⟨{c | c = readToken ∨ c = readSecond}, fun _ => true, true⟩
def twoReady : RState Nat Unit := ⟨{0, 1}, {0, 1}, Set.univ, Set.univ⟩

theorem first_of_two_is_allowed :
    rAllowed label twoReadProc (fun _ => False) twoReady (.run () readToken) := by
  refine ⟨Set.mem_univ _, Set.mem_univ _, Or.inl rfl, ?_⟩
  refine ⟨⟨by decide, by decide, by decide, ?_⟩, by decide⟩
  intro query member
  simp [readToken, Commit.keepOne] at member

theorem second_of_two_is_allowed :
    rAllowed label twoReadProc (fun _ => False) twoReady (.run () readSecond) := by
  refine ⟨Set.mem_univ _, Set.mem_univ _, Or.inr rfl, ?_⟩
  refine ⟨⟨by decide, by decide, by decide, ?_⟩, by decide⟩
  intro query member
  simp [readSecond, Commit.keepOne] at member

theorem first_of_two_is_a_self_loop :
    rNext twoReadProc noWake twoReady (.run () readToken) = twoReady := by
  simp [rNext, twoReadProc, twoReady, noWake, woken, readToken, Commit.keepOne, fire]

def unfairMatches : Run (reactive label twoReadProc noWake (fun _ => False)) where
  state := fun _ => twoReady
  label := fun _ => .run () readToken
  allowed := fun _ => first_of_two_is_allowed
  step := fun _ => first_of_two_is_a_self_loop.symm

theorem registration_is_strongly_fair : unfairMatches.StronglyFair (runTask ()) := by
  intro _ N
  exact ⟨N, le_rfl, rfl⟩

theorem second_match_is_never_served (n : Nat) :
    unfairMatches.label n ≠ .run () readSecond := by
  intro same
  have equal : readToken = readSecond := (RLabel.run.inj same).2
  have keeps := congrArg Commit.kept equal
  simp [readToken, readSecond, Commit.keepOne] at keeps

theorem process_fairness_does_not_imply_match_fairness :
    unfairMatches.StronglyFair (runTask ()) ∧
      (∀ n, rAllowed label twoReadProc (fun _ => False)
        (unfairMatches.state n) (.run () readSecond)) ∧
      ∀ n, unfairMatches.label n ≠ .run () readSecond :=
  ⟨registration_is_strongly_fair, fun _ => second_of_two_is_allowed, second_match_is_never_served⟩

end Mettapedia.Machines.StoreInteraction.ReactivePolicies
