import Mettapedia.Machines.PrefixPortfolio

/-!
# Single-turn execution of retained prefix portfolios

A turn either loads the next finite inclusive dyadic phase or services one
allocated slot. Workers need not halt: a worker may itself be another clock.
The correspondence to the batched portfolio is proved, not assumed.

The turn bound charges one phase-loading turn and every worker/delegation
slot. It does not assign unit machine cost to constructing the phase list,
initializing a worker, or inspecting an encoded output. Those costs remain
outside this clock model's machine-transition accounting.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResumablePrefixClock

open KolmogorovComplexity
open Mettapedia.UniversalAI.TimeBoundedAIXI

variable {σ : Type*}

def run (step : σ → σ) (count : Nat) (state : σ) : σ :=
  StepCounting.runFor (fun current => some (step current)) count state

@[simp] theorem run_zero (step : σ → σ) (state : σ) : run step 0 state = state := rfl

@[simp] theorem run_succ (step : σ → σ) (count : Nat) (state : σ) :
    run step (count + 1) state = run step count (step state) := rfl

theorem run_add (step : σ → σ) (first second : Nat) (state : σ) :
    run step (first + second) state = run step second (run step first state) :=
  StepCounting.runFor_add _ first second state

theorem run_preserves (step : σ → σ) (property : σ → Prop)
    (preserved : ∀ state, property state → property (step state))
    (count : Nat) (state : σ) (holds : property state) : property (run step count state) := by
  induction count generalizing state with
  | zero => exact holds
  | succ count ih => exact ih (step state) (preserved state holds)

theorem run_mono (step : σ → σ) (property : σ → Prop)
    (preserved : ∀ state, property state → property (step state))
    {first second : Nat} (enough : first ≤ second) (state : σ)
    (holds : property (run step first state)) : property (run step second state) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  rw [run_add]
  exact run_preserves step property preserved extra _ holds

def slots (accepts : BinString → Bool) (phase : Nat) : List BinString :=
  (PrefixPortfolio.words accepts phase).flatMap fun word =>
    List.replicate (2 ^ (phase - word.length)) word

theorem slots_length (accepts : BinString → Bool) (phase : Nat) :
    (slots accepts phase).length = PrefixPortfolio.phaseCost accepts phase := by
  simp [slots, PrefixPortfolio.phaseCost, List.length_flatMap]

def serve (step : BinString → σ → σ) (state : BinString → σ) (word : BinString) : BinString → σ :=
  Function.update state word (step word (state word))

def serveSlots (step : BinString → σ → σ) (selected : List BinString)
    (state : BinString → σ) : BinString → σ := selected.foldl (serve step) state

theorem serveSlots_replicate (step : BinString → σ → σ) (count : Nat)
    (state : BinString → σ) (word : BinString) :
    serveSlots step (List.replicate count word) state =
      Function.update state word (run (step word) count (state word)) := by
  induction count generalizing state with
  | zero => simp [serveSlots]
  | succ count ih =>
      simp only [List.replicate_succ, serveSlots, List.foldl_cons]
      rw [show (List.replicate count word).foldl (serve step) (serve step state word) =
        Function.update (serve step state word) word
          (run (step word) count (serve step state word word)) from ih (serve step state word)]
      funext target
      by_cases same : target = word
      · subst target
        simp [serve, run_succ]
      · simp [serve, same]

theorem serveSlots_blocks (step : BinString → σ → σ) (selected : List BinString)
    (quota : BinString → Nat) (state : BinString → σ) :
    serveSlots step (selected.flatMap fun word => List.replicate (quota word) word) state =
      PrefixPortfolio.serviceList (fun word current => some (step word current)) quota selected state := by
  induction selected generalizing state with
  | nil => rfl
  | cons word rest ih =>
      simp only [List.flatMap_cons, serveSlots, List.foldl_append, PrefixPortfolio.serviceList,
        List.foldl_cons]
      rw [show (List.replicate (quota word) word).foldl (serve step) state =
        Function.update state word (run (step word) (quota word) (state word)) from
          serveSlots_replicate step _ state word]
      exact ih _

theorem serveSlots_phase (step : BinString → σ → σ) (accepts : BinString → Bool)
    (phase : Nat) (state : BinString → σ) :
    serveSlots step (slots accepts phase) state =
      PrefixPortfolio.runPhase accepts (fun word current => some (step word current)) phase state :=
  serveSlots_blocks step _ _ state

structure Clock (σ : Type*) where
  phase : Nat
  pending : List BinString
  values : BinString → σ

def initial (values : BinString → σ) : Clock σ := ⟨0, [], values⟩

def tick (accepts : BinString → Bool) (step : BinString → σ → σ) (clock : Clock σ) : Clock σ :=
  match clock.pending with
  | [] => ⟨clock.phase + 1, slots accepts clock.phase, clock.values⟩
  | word :: rest => ⟨clock.phase, rest, serve step clock.values word⟩

theorem drain_pending (accepts : BinString → Bool) (step : BinString → σ → σ)
    (pending : List BinString) (phase : Nat) (values : BinString → σ) :
    run (tick accepts step) pending.length ⟨phase, pending, values⟩ =
      ⟨phase, [], serveSlots step pending values⟩ := by
  induction pending generalizing values with
  | nil => rfl
  | cons word rest ih =>
      simpa only [List.length_cons, run_succ, tick, serveSlots, List.foldl_cons] using
        ih (serve step values word)

def phaseTurns (accepts : BinString → Bool) (phase : Nat) : Nat :=
  1 + (slots accepts phase).length

theorem complete_phase (accepts : BinString → Bool) (step : BinString → σ → σ)
    (phase : Nat) (values : BinString → σ) :
    run (tick accepts step) (phaseTurns accepts phase) ⟨phase, [], values⟩ =
      ⟨phase + 1, [], PrefixPortfolio.runPhase accepts
        (fun word current => some (step word current)) phase values⟩ := by
  unfold phaseTurns
  rw [Nat.add_comm 1, run_succ]
  simpa only [tick, serveSlots_phase] using
    drain_pending accepts step (slots accepts phase) (phase + 1) values

def turnsFrom (accepts : BinString → Bool) (start count : Nat) : Nat :=
  match count with
  | 0 => 0
  | count + 1 => phaseTurns accepts start + turnsFrom accepts (start + 1) count
termination_by structural count

theorem complete_phases (accepts : BinString → Bool) (step : BinString → σ → σ)
    (count start : Nat) (values : BinString → σ) :
    run (tick accepts step) (turnsFrom accepts start count) ⟨start, [], values⟩ =
      ⟨start + count, [], PrefixPortfolio.runFrom accepts
        (fun word current => some (step word current)) start count values⟩ := by
  induction count generalizing start values with
  | zero => simp [turnsFrom, PrefixPortfolio.runFrom]
  | succ count ih =>
      rw [turnsFrom, run_add, complete_phase, ih]
      simp only [PrefixPortfolio.runFrom, Nat.add_comm, Nat.add_left_comm]

theorem turnsFrom_geometric (accepts : BinString → Bool)
    (free : PrefixFree {word | accepts word = true}) (count start : Nat) :
    turnsFrom accepts start count + 2 ^ (start + 1) ≤ 2 ^ (start + count + 1) := by
  induction count generalizing start with
  | zero => simp [turnsFrom]
  | succ count ih =>
      have prior := ih (start + 1)
      have cost := PrefixPortfolio.phaseCost_le accepts free start
      have positive := Nat.two_pow_pos start
      have double : 2 ^ (start + 1 + 1) = 2 * (2 * 2 ^ start) := by
        simp [pow_succ, Nat.mul_comm]
      have shifted : start + 1 + count + 1 = start + (count + 1) + 1 := by omega
      rw [double, shifted] at prior
      simp only [turnsFrom, phaseTurns, slots_length, pow_succ] at ⊢
      omega

theorem tick_preserves_at (accepts : BinString → Bool) (step : BinString → σ → σ)
    (word : BinString) (property : σ → Prop)
    (preserved : ∀ state, property state → property (step word state))
    (clock : Clock σ) (holds : property (clock.values word)) :
    property ((tick accepts step clock).values word) := by
  cases pending : clock.pending with
  | nil => simpa [tick, pending] using holds
  | cons selected rest =>
      by_cases same : word = selected
      · subst selected
        simpa [tick, pending, serve] using preserved _ holds
      · simpa [tick, pending, serve, same] using holds

theorem tick_preserves_all (accepts : BinString → Bool) (step : BinString → σ → σ)
    (property : BinString → σ → Prop)
    (preserved : ∀ word state, property word state → property word (step word state))
    (clock : Clock σ) (holds : ∀ word, property word (clock.values word)) :
    ∀ word, property word ((tick accepts step clock).values word) :=
  fun word => tick_preserves_at accepts step word (property word) (preserved word) clock (holds word)

/-- A persistent branch property receives its required number of actual
service calls. Divergence and newly useful work on other branches do not
alter this bound. The clock's phase-loading turns are included. -/
theorem services_by_bound (accepts : BinString → Bool)
    (free : PrefixFree {word | accepts word = true}) (step : BinString → σ → σ)
    (values : BinString → σ) (word : BinString) (valid : accepts word = true)
    (work : Nat) (property : σ → Prop)
    (preserved : ∀ state, property state → property (step word state))
    (reached : property (run (step word) work (values word))) :
    let phase := word.length + Nat.clog 2 work
    let budget := turnsFrom accepts 0 (phase + 1)
    budget ≤ 8 * 2 ^ word.length * max work 1 ∧
      property ((run (tick accepts step) budget (initial values)).values word) := by
  dsimp only
  let phase := word.length + Nat.clog 2 work
  have eligible : word.length ≤ phase := by dsimp [phase]; omega
  have quotaEnough : work ≤ PrefixPortfolio.quota accepts phase word := by
    rw [PrefixPortfolio.quota, if_pos ⟨valid, eligible⟩]
    simpa [phase] using Nat.le_pow_clog (by norm_num : 1 < (2 : Nat)) work
  have enough := quotaEnough.trans (by simpa using
    PrefixPortfolio.last_quota_le_workFrom accepts phase 0 word)
  constructor
  · have geometric := turnsFrom_geometric accepts free (phase + 1) 0
    have logBound := LevinSearch.Family.pow_clog_le work
    calc turnsFrom accepts 0 (phase + 1) ≤ 2 ^ (phase + 2) := by simpa using geometric.trans' (by omega)
      _ = 4 * 2 ^ word.length * 2 ^ Nat.clog 2 work := by dsimp [phase]; ring
      _ ≤ 4 * 2 ^ word.length * (2 * max work 1) := Nat.mul_le_mul_left _ logBound
      _ = 8 * 2 ^ word.length * max work 1 := by ring
  · rw [initial, complete_phases]
    change property (PrefixPortfolio.runFrom accepts
      (fun word current => some (step word current)) 0 (phase + 1) values word)
    rw [PrefixPortfolio.runFrom_at]
    exact run_mono (step word) property preserved enough (values word) reached

end Mettapedia.Machines.ResumablePrefixClock
