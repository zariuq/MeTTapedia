import Mettapedia.Machines.HierarchicalPrefixSearch

/-!
# Sound histories and explicit cumulative weights for hierarchical search

Every local state in a sound search is a real finite prefix of its worker.
Every published child has a real worker readout and a sound retained child
search. This invariant covers all branches, not only a selected witness.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HierarchicalPrefixSearch

open KolmogorovComplexity
open Mettapedia.UniversalAI.TimeBoundedAIXI

variable {σ κ α β : Type}

def BranchSound (worker : PrefixPortfolio.Worker σ α) (nextInput : α → κ)
    (childSound : κ → β → Prop) (word : BinString) : Branch σ α β → Prop
  | .running state => ∃ work, StepCounting.runFor (worker.step word) work (worker.initial word) = state
  | .rejected => True
  | .child answer state =>
      (∃ work, (worker.searcher word).result work = some answer) ∧ childSound (nextInput answer) state

theorem branch_sound_tick (worker : PrefixPortfolio.Worker σ α) (nextInput : α → κ)
    (childSound : κ → β → Prop) (spawn : α → β) (descend : β → β)
    (initialSound : ∀ answer, childSound (nextInput answer) (spawn answer))
    (descendSound : ∀ input state, childSound input state → childSound input (descend state))
    (word : BinString) (branch : Branch σ α β)
    (sound : BranchSound worker nextInput childSound word branch) :
    BranchSound worker nextInput childSound word (branchTick worker spawn descend word branch) := by
  cases branch with
  | running state =>
      obtain ⟨work, reached⟩ := sound
      cases transition : worker.step word state with
      | none =>
          cases read : worker.read word state with
          | none => simp only [branchTick, transition, read, BranchSound]
          | some answer =>
              simp only [branchTick, transition, read, BranchSound]
              constructor
              · exact ⟨work, by change worker.read word _ = some answer; rw [reached]; exact read⟩
              · exact initialSound answer
      | some next =>
          simp only [branchTick, transition, BranchSound]
          refine ⟨work + 1, ?_⟩
          rw [StepCounting.runFor_add, reached]
          simp only [StepCounting.runFor, transition]
  | rejected => trivial
  | child answer state => exact ⟨sound.1, descendSound _ state sound.2⟩

def Sound (worker : κ → PrefixPortfolio.Worker σ α) (nextInput : κ → α → κ) :
    (depth : Nat) → κ → State σ κ α depth → Prop
  | 0, input, state => state = input
  | depth + 1, input, (current, clock) =>
      current = input ∧ ∀ word,
        BranchSound (worker input) (nextInput input) (Sound worker nextInput depth) word (clock.values word)

theorem initial_sound (worker : κ → PrefixPortfolio.Worker σ α) (nextInput : κ → α → κ)
    (depth : Nat) (input : κ) : Sound worker nextInput depth input (initial worker depth input) := by
  cases depth with
  | zero => rfl
  | succ depth => exact ⟨rfl, fun _word => ⟨0, rfl⟩⟩

theorem tick_sound (worker : κ → PrefixPortfolio.Worker σ α) (accepts : BinString → Bool)
    (nextInput : κ → α → κ) (depth : Nat) (input : κ) (state : State σ κ α depth)
    (sound : Sound worker nextInput depth input state) :
    Sound worker nextInput depth input (tick worker accepts nextInput depth state) := by
  induction depth generalizing input with
  | zero => exact sound
  | succ depth ih =>
      obtain ⟨current, clock⟩ := state
      obtain ⟨rfl, branches⟩ := sound
      constructor
      · rfl
      · exact ResumablePrefixClock.tick_preserves_all accepts _
          (BranchSound (worker current) (nextInput current) (Sound worker nextInput depth))
          (fun word branch proper => branch_sound_tick (worker current) (nextInput current)
            (Sound worker nextInput depth) _ _
            (fun answer => initial_sound worker nextInput depth (nextInput current answer))
            (fun input child valid => ih input child valid) word branch proper) clock branches

theorem run_sound (worker : κ → PrefixPortfolio.Worker σ α) (accepts : BinString → Bool)
    (nextInput : κ → α → κ) (depth count : Nat) (input : κ) (state : State σ κ α depth)
    (sound : Sound worker nextInput depth input state) :
    Sound worker nextInput depth input (Clock.run (tick worker accepts nextInput depth) count state) :=
  Clock.run_preserves _ _ (fun state valid => tick_sound worker accepts nextInput depth input state valid)
    count state sound

inductive PathRuns (worker : κ → PrefixPortfolio.Worker σ α) (nextInput : κ → α → κ) :
    κ → List (BinString × α) → Prop
  | nil (input : κ) : PathRuns worker nextInput input []
  | cons {input : κ} {word : BinString} {answer : α} {rest : List (BinString × α)}
      (found : ∃ work, ((worker input).searcher word).result work = some answer)
      (later : PathRuns worker nextInput (nextInput input answer) rest) :
      PathRuns worker nextInput input ((word, answer) :: rest)

theorem follows_sound (worker : κ → PrefixPortfolio.Worker σ α) (nextInput : κ → α → κ)
    (depth : Nat) (input : κ) (state : State σ κ α depth) (path : List (BinString × α))
    (sound : Sound worker nextInput depth input state) (seen : Follows depth path state) :
    PathRuns worker nextInput input path := by
  induction depth generalizing input path with
  | zero =>
      cases path with
      | nil => exact .nil input
      | cons entry rest => exact False.elim seen
  | succ depth ih =>
      cases path with
      | nil => exact .nil input
      | cons entry rest =>
          obtain ⟨word, answer⟩ := entry
          obtain ⟨current, clock⟩ := state
          obtain ⟨rfl, branches⟩ := sound
          obtain ⟨child, stored, later⟩ := seen
          have proper := branches word
          rw [stored] at proper
          exact .cons proper.1 (ih _ child rest proper.2 later)

theorem every_observed_path_runs (worker : κ → PrefixPortfolio.Worker σ α)
    (accepts : BinString → Bool) (nextInput : κ → α → κ)
    (depth count : Nat) (input : κ) (path : List (BinString × α))
    (seen : Follows depth path (Clock.run (tick worker accepts nextInput depth) count
      (initial worker depth input))) : PathRuns worker nextInput input path :=
  follows_sound worker nextInput depth input _ path
    (run_sound worker accepts nextInput depth count input _ (initial_sound worker nextInput depth input)) seen

def observes [DecidableEq α] : (depth : Nat) → List (BinString × α) → State σ κ α depth → Bool
  | _depth, [], _state => true
  | 0, _entry :: _rest, _state => false
  | depth + 1, (word, answer) :: rest, (_input, clock) =>
      match clock.values word with
      | .child actual child => decide (actual = answer) && observes depth rest child
      | _ => false

theorem observes_iff_follows [DecidableEq α] (depth : Nat) (path : List (BinString × α))
    (state : State σ κ α depth) : observes depth path state = true ↔ Follows depth path state := by
  induction depth generalizing path with
  | zero => cases path <;> simp [observes, Follows]
  | succ depth ih =>
      cases path with
      | nil => simp [observes, Follows]
      | cons entry rest =>
          obtain ⟨word, answer⟩ := entry
          obtain ⟨input, clock⟩ := state
          cases stored : clock.values word with
          | running config => simp [observes, Follows, stored, HasChild]
          | rejected => simp [observes, Follows, stored, HasChild]
          | child actual child =>
              simp only [observes, Follows, stored, Bool.and_eq_true, decide_eq_true_eq, ih, HasChild,
                Branch.child.injEq]
              constructor
              · rintro ⟨rfl, found⟩
                exact ⟨child, ⟨rfl, rfl⟩, found⟩
              · rintro ⟨next, ⟨rfl, rfl⟩, found⟩
                exact ⟨rfl, found⟩

/-- The coefficient at depth i contains every earlier complete codeword
length and three clock-factor bits per level. Nothing is hidden in an
uncharged, per-program constant. -/
def weightedTerms (exponent : Nat) (entries : List (TimedEntry α)) : List Nat :=
  match entries with
  | [] => []
  | ((word, _answer), work) :: rest =>
      2 ^ (exponent + word.length + 3) * (work + 1) :: weightedTerms (exponent + word.length + 3) rest
termination_by structural entries

theorem weightedTerms_sum (entries : List (TimedEntry α)) (exponent : Nat) :
    (weightedTerms exponent entries).sum = 2 ^ exponent * nestedBound entries := by
  induction entries generalizing exponent with
  | nil => simp [weightedTerms, nestedBound]
  | cons entry rest ih =>
      obtain ⟨⟨word, answer⟩, work⟩ := entry
      simp only [weightedTerms, List.sum_cons, ih, nestedBound, pow_add]
      norm_num
      ring

theorem nestedBound_eq_weighted_sum (entries : List (TimedEntry α)) :
    nestedBound entries = (weightedTerms 0 entries).sum := by
  simpa using (weightedTerms_sum entries 0).symm

end Mettapedia.Machines.HierarchicalPrefixSearch
