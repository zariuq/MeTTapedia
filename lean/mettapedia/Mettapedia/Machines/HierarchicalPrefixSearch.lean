import Mettapedia.Machines.ResumablePrefixClock

/-!
# Retained hierarchical prefix search

Every admitted word owns a live process. Its local worker is stepped until
it stops; a successful readout publishes a child and redirects that same
branch's future allocations to the child's resumable search. Other local
workers and children remain present, including divergent competitors.

Depth is an explicit structural bound. For incremental compression it can
be set to the original source length, because every accepted child strictly
shortens the residual. No halting or incompressibility oracle is used.

The bound measures recursive clock turns, charging phase-loading and
publication/delegation turns. At most one underlying worker step occurs in
one root turn. Concrete phase construction, initialization and readout costs
are not identified with unit Turing-machine transitions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HierarchicalPrefixSearch

open KolmogorovComplexity
open Mettapedia.UniversalAI.TimeBoundedAIXI

namespace Clock
export ResumablePrefixClock (run run_zero run_succ run_add run_preserves run_mono)
end Clock

variable {σ κ α β : Type}

inductive Branch (σ α β : Type) where
  | running (state : σ)
  | rejected
  | child (answer : α) (state : β)

def branchTick (worker : PrefixPortfolio.Worker σ α)
    (spawn : α → β) (descend : β → β) (word : BinString) : Branch σ α β → Branch σ α β
  | .running state =>
      match worker.step word state with
      | some next => .running next
      | none =>
          match worker.read word state with
          | none => .rejected
          | some answer => .child answer (spawn answer)
  | .rejected => .rejected
  | .child answer state => .child answer (descend state)

def HasChild (answer : α) (property : β → Prop) (branch : Branch σ α β) : Prop :=
  ∃ state, branch = .child answer state ∧ property state

theorem branch_child_run (worker : PrefixPortfolio.Worker σ α)
    (spawn : α → β) (descend : β → β) (word : BinString)
    (count : Nat) (answer : α) (state : β) :
    Clock.run (branchTick worker spawn descend word) count (.child answer state) =
      .child answer (Clock.run descend count state) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simpa only [Clock.run_succ, branchTick] using ih (descend state)

theorem branch_child_preserved (worker : PrefixPortfolio.Worker σ α)
    (spawn : α → β) (descend : β → β) (word : BinString)
    (answer : α) (property : β → Prop)
    (preserved : ∀ state, property state → property (descend state)) :
    ∀ branch, HasChild answer property branch →
      HasChild answer property (branchTick worker spawn descend word branch) := by
  rintro _ ⟨state, rfl, holds⟩
  exact ⟨descend state, rfl, preserved state holds⟩

theorem branch_reaches_child (worker : PrefixPortfolio.Worker σ α)
    (spawn : α → β) (descend : β → β) (word : BinString)
    (work : Nat) (state : σ) (answer : α)
    (found : worker.read word (StepCounting.runFor (worker.step word) work state) = some answer) :
    ∃ used, used ≤ work + 1 ∧
      Clock.run (branchTick worker spawn descend word) used (.running state) =
        .child answer (spawn answer) := by
  induction work generalizing state with
  | zero =>
      have stopped := worker.stopped word state answer found
      have read : worker.read word state = some answer := found
      exact ⟨1, by omega, by simp [branchTick, stopped, read]⟩
  | succ work ih =>
      cases transition : worker.step word state with
      | none =>
          have read : worker.read word state = some answer := by
            simpa [StepCounting.runFor, transition] using found
          exact ⟨1, by omega, by simp [branchTick, transition, read]⟩
      | some next =>
          have read : worker.read word (StepCounting.runFor (worker.step word) work next) = some answer := by
            simpa only [StepCounting.runFor, transition] using found
          obtain ⟨used, bounded, reached⟩ := ih next read
          exact ⟨used + 1, by omega, by simpa only [Clock.run_succ, branchTick, transition] using reached⟩

theorem branch_services_child (worker : PrefixPortfolio.Worker σ α)
    (spawn : α → β) (descend : β → β) (word : BinString)
    (work childWork : Nat) (answer : α) (property : β → Prop)
    (preserved : ∀ state, property state → property (descend state))
    (found : (worker.searcher word).result work = some answer)
    (childFound : property (Clock.run descend childWork (spawn answer))) :
    HasChild answer property (Clock.run (branchTick worker spawn descend word)
      (work + 1 + childWork) (.running (worker.initial word))) := by
  obtain ⟨used, bounded, spawned⟩ := branch_reaches_child worker spawn descend word
    work (worker.initial word) answer found
  have reached : HasChild answer property
      (Clock.run (branchTick worker spawn descend word) (used + childWork) (.running (worker.initial word))) := by
    rw [Clock.run_add, spawned, branch_child_run]
    exact ⟨_, rfl, childFound⟩
  exact Clock.run_mono _ _ (branch_child_preserved worker spawn descend word answer property preserved)
    (by omega) _ reached

def State (σ κ α : Type) : Nat → Type
  | 0 => κ
  | depth + 1 => κ × ResumablePrefixClock.Clock (Branch σ α (State σ κ α depth))

def initial (worker : κ → PrefixPortfolio.Worker σ α) :
    (depth : Nat) → κ → State σ κ α depth
  | 0, input => input
  | _depth + 1, input => (input, ResumablePrefixClock.initial fun word => .running ((worker input).initial word))

def tick (worker : κ → PrefixPortfolio.Worker σ α) (accepts : BinString → Bool)
    (nextInput : κ → α → κ) : (depth : Nat) → State σ κ α depth → State σ κ α depth
  | 0, input => input
  | depth + 1, (input, clock) =>
      (input, ResumablePrefixClock.tick accepts
        (branchTick (worker input) (fun answer => initial worker depth (nextInput input answer))
          (tick worker accepts nextInput depth)) clock)

theorem run_node (worker : κ → PrefixPortfolio.Worker σ α) (accepts : BinString → Bool)
    (nextInput : κ → α → κ) (depth count : Nat) (input : κ)
    (clock : ResumablePrefixClock.Clock (Branch σ α (State σ κ α depth))) :
    Clock.run (tick worker accepts nextInput (depth + 1)) count (input, clock) =
      (input, Clock.run (ResumablePrefixClock.tick accepts
        (branchTick (worker input) (fun answer => initial worker depth (nextInput input answer))
          (tick worker accepts nextInput depth))) count clock) := by
  induction count generalizing clock with
  | zero => rfl
  | succ count ih =>
      simpa only [ResumablePrefixClock.run, StepCounting.runFor, tick] using ih
        (ResumablePrefixClock.tick accepts
          (branchTick (worker input) (fun answer => initial worker depth (nextInput input answer))
            (tick worker accepts nextInput depth)) clock)

def Follows : (depth : Nat) → List (BinString × α) → State σ κ α depth → Prop
  | _depth, [], _state => True
  | 0, _entry :: _rest, _state => False
  | depth + 1, (word, answer) :: rest, (_input, clock) =>
      HasChild answer (Follows depth rest) (clock.values word)

theorem follows_preserved (worker : κ → PrefixPortfolio.Worker σ α) (accepts : BinString → Bool)
    (nextInput : κ → α → κ) (depth : Nat) (path : List (BinString × α)) :
    ∀ state, Follows depth path state → Follows depth path (tick worker accepts nextInput depth state) := by
  induction depth generalizing path with
  | zero => cases path <;> simp [Follows]
  | succ depth ih =>
      intro state holds
      cases path with
      | nil => trivial
      | cons entry rest =>
          obtain ⟨word, answer⟩ := entry
          obtain ⟨input, clock⟩ := state
          exact ResumablePrefixClock.tick_preserves_at accepts _ word _
            (branch_child_preserved (worker input) _ _ word answer _ (ih rest)) clock holds

theorem follows_run (worker : κ → PrefixPortfolio.Worker σ α) (accepts : BinString → Bool)
    (nextInput : κ → α → κ) (depth count : Nat) (path : List (BinString × α))
    (state : State σ κ α depth) (holds : Follows depth path state) :
    Follows depth path (Clock.run (tick worker accepts nextInput depth) count state) :=
  Clock.run_preserves _ _ (follows_preserved worker accepts nextInput depth path) count state holds

abbrev TimedEntry (α : Type) := (BinString × α) × Nat

inductive TimedPath (worker : κ → PrefixPortfolio.Worker σ α) (nextInput : κ → α → κ) :
    κ → List (TimedEntry α) → Prop
  | nil (input : κ) : TimedPath worker nextInput input []
  | cons {input : κ} {word : BinString} {answer : α} {work : Nat} {rest : List (TimedEntry α)}
      (found : ((worker input).searcher word).result work = some answer)
      (later : TimedPath worker nextInput (nextInput input answer) rest) :
      TimedPath worker nextInput input (((word, answer), work) :: rest)

def nestedBound : List (TimedEntry α) → Nat
  | [] => 0
  | ((word, _answer), work) :: rest => 8 * 2 ^ word.length * (work + 1 + nestedBound rest)

/-- The whole live hierarchy, not a successful-branch-only transition
relation, reaches every admitted timed path within the nested allocation
bound. All unrelated branches remain in the same operational state. -/
theorem path_by_bound (worker : κ → PrefixPortfolio.Worker σ α) (accepts : BinString → Bool)
    (free : PrefixFree {word | accepts word = true}) (nextInput : κ → α → κ)
    {input : κ} {entries : List (TimedEntry α)}
    (path : TimedPath worker nextInput input entries)
    (admitted : ∀ entry ∈ entries, accepts entry.1.1 = true)
    (depth : Nat) (bounded : entries.length ≤ depth) :
    Follows depth (entries.map Prod.fst)
      (Clock.run (tick worker accepts nextInput depth) (nestedBound entries) (initial worker depth input)) := by
  induction path generalizing depth with
  | nil input => cases depth <;> trivial
  | @cons input word answer work rest found later ih =>
      cases depth with
      | zero => simp at bounded
      | succ depth =>
          have tailBound : rest.length ≤ depth := by simpa using bounded
          have tailAdmitted : ∀ entry ∈ rest, accepts entry.1.1 = true :=
            fun entry member => admitted entry (List.mem_cons_of_mem _ member)
          have childFound := ih tailAdmitted depth tailBound
          let spawn := fun answer => initial worker depth (nextInput input answer)
          let descend := tick worker accepts nextInput depth
          let service := branchTick (worker input) spawn descend
          let property : Branch σ α (State σ κ α depth) → Prop :=
            HasChild answer (@Follows σ κ α depth (rest.map Prod.fst))
          have preserved := branch_child_preserved (worker input) spawn descend word answer
            (@Follows σ κ α depth (rest.map Prod.fst))
            (follows_preserved worker accepts nextInput depth (rest.map Prod.fst))
          have childServices : property (Clock.run (service word) (work + 1 + nestedBound rest)
              (.running ((worker input).initial word))) :=
            branch_services_child (worker input) spawn descend word work (nestedBound rest) answer
              (@Follows σ κ α depth (rest.map Prod.fst))
              (follows_preserved worker accepts nextInput depth (rest.map Prod.fst)) found childFound
          have valid : accepts word = true := admitted ((word, answer), work) (by simp)
          obtain ⟨clockBound, observed⟩ := ResumablePrefixClock.services_by_bound accepts free service
            (fun word => Branch.running ((worker input).initial word)) word valid
            (work + 1 + nestedBound rest) property preserved childServices
          let phase := word.length + Nat.clog 2 (work + 1 + nestedBound rest)
          let budget := ResumablePrefixClock.turnsFrom accepts 0 (phase + 1)
          have outerBound : budget ≤ nestedBound (((word, answer), work) :: rest) := by
            simpa only [nestedBound, max_eq_left (by omega : 1 ≤ work + 1 + nestedBound rest)] using clockBound
          have reached : Follows (depth + 1) (((word, answer) :: rest.map Prod.fst))
              (Clock.run (tick worker accepts nextInput (depth + 1)) budget
                (initial worker (depth + 1) input)) := by
            rw [initial, run_node]
            exact observed
          exact Clock.run_mono _ _ (follows_preserved worker accepts nextInput (depth + 1) _)
            outerBound _ reached

end Mettapedia.Machines.HierarchicalPrefixSearch
