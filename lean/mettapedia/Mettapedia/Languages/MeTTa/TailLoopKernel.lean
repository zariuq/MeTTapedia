import Mettapedia.Languages.MeTTa.HE.FuelConvergence
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Range

/-!
# The deterministic-tail loop kernel

Semantic license for the engine's "loop lane": a deterministic tail-recursive
evaluation (single-branch tail self-call, effects emitted per unfolding) may be
executed as an accumulator loop instead of by structural recursion, with the
same answer and the same effect BAG (multiset — order is non-semantic).

Contents, all proved:

* `runFuel` (the evaluator's shape: recursion on fuel, effects collected on
  the way out) and `runIter` (the loop lane's shape: an accumulator threaded
  forward) agree exactly (`runIter_eq_runFuel`), via the accumulator law
  `runIterAux_eq`.
* Deterministic tail machines are a POSITIVE class for the corpus's fuel
  convergence abstraction: once a run halts, more fuel changes nothing
  (`runFuel_mono`, `stableFrom_of_halts`, `converges_of_halts`) — in contrast
  to the general driver, where `FuelConvergence` exists precisely because
  inclusion monotonicity FAILS.
* Per-unfolding invariants transfer to whole-run results
  (`invariant_transfer`) — the loop lane's entry-guard contract.
* A concrete countdown/effect instance (`addLoop`) with its effect bag in
  closed form (`addLoop_run`): the Lean mirror of the 100k add-atom loop.

What this does NOT claim: resource behaviour (frame count, memory) is an
engine-implementation property outside this semantics; the kernel licenses the
transformation's observable equality, and the engine's differential gates
check the implementation against it.
-/

namespace Mettapedia.Languages.MeTTa.TailLoopKernel

open Mettapedia.Languages.MeTTa.HE.FuelConvergence

universe u v w

/-- One unfolding of a deterministic tail evaluation: either continue at a new
state, emitting a bag of effects, or halt with a result. -/
inductive Step (σ : Type u) (ε : Type v) (ρ : Type w) where
  | next (s : σ) (out : Multiset ε)
  | halt (r : ρ)

/-- A deterministic tail machine: the single-branch tail-call shape the loop
lane accepts.  Nondeterministic tails are outside this structure by
construction — they fall back to the general evaluator. -/
structure TailMachine (σ : Type u) (ε : Type v) (ρ : Type w) where
  step : σ → Step σ ε ρ

variable {σ : Type u} {ε : Type v} {ρ : Type w}

/-- Evaluator shape: structural recursion on fuel; the effect bag of a
continuation is prepended on the way out of the recursion. -/
def runFuel (M : TailMachine σ ε ρ) : Nat → σ → Option (ρ × Multiset ε)
  | 0, _ => none
  | n + 1, s =>
    match M.step s with
    | .halt r => some (r, 0)
    | .next s' out => (runFuel M n s').map fun p => (p.1, out + p.2)

/-- Loop shape: the effect bag is an accumulator threaded FORWARD, as the
engine's loop lane executes it. -/
def runIterAux (M : TailMachine σ ε ρ) : Nat → σ → Multiset ε →
    Option (ρ × Multiset ε)
  | 0, _, _ => none
  | n + 1, s, acc =>
    match M.step s with
    | .halt r => some (r, acc)
    | .next s' out => runIterAux M n s' (acc + out)

/-- The loop lane's entry point. -/
def runIter (M : TailMachine σ ε ρ) (n : Nat) (s : σ) :
    Option (ρ × Multiset ε) :=
  runIterAux M n s 0

/-! ### Equation lemmas — no proof below ever faces a naked match scrutinee -/

@[simp] theorem runFuel_zero (M : TailMachine σ ε ρ) (s : σ) :
    runFuel M 0 s = none := rfl

theorem runFuel_succ_halt {M : TailMachine σ ε ρ} {s : σ} {r : ρ}
    (h : M.step s = .halt r) (n : Nat) :
    runFuel M (n + 1) s = some (r, 0) := by
  simp [runFuel, h]

theorem runFuel_succ_next {M : TailMachine σ ε ρ} {s s' : σ}
    {out : Multiset ε} (h : M.step s = .next s' out) (n : Nat) :
    runFuel M (n + 1) s =
      (runFuel M n s').map fun p => (p.1, out + p.2) := by
  simp [runFuel, h]

@[simp] theorem runIterAux_zero (M : TailMachine σ ε ρ) (s : σ)
    (acc : Multiset ε) : runIterAux M 0 s acc = none := rfl

theorem runIterAux_succ_halt {M : TailMachine σ ε ρ} {s : σ} {r : ρ}
    (h : M.step s = .halt r) (n : Nat) (acc : Multiset ε) :
    runIterAux M (n + 1) s acc = some (r, acc) := by
  simp [runIterAux, h]

theorem runIterAux_succ_next {M : TailMachine σ ε ρ} {s s' : σ}
    {out : Multiset ε} (h : M.step s = .next s' out) (n : Nat)
    (acc : Multiset ε) :
    runIterAux M (n + 1) s acc = runIterAux M n s' (acc + out) := by
  simp [runIterAux, h]

/-- Accumulator law: running with a primed accumulator is running clean and
adding the accumulator to the emitted bag. -/
theorem runIterAux_eq (M : TailMachine σ ε ρ) :
    ∀ (n : Nat) (s : σ) (acc : Multiset ε),
      runIterAux M n s acc = (runFuel M n s).map fun p => (p.1, acc + p.2) := by
  intro n
  induction n with
  | zero => intro s acc; rfl
  | succ n ih =>
    intro s acc
    cases hstep : M.step s with
    | halt r =>
      rw [runIterAux_succ_halt hstep, runFuel_succ_halt hstep]
      simp
    | next s' out =>
      rw [runIterAux_succ_next hstep, runFuel_succ_next hstep,
          ih s' (acc + out)]
      cases h : runFuel M n s' with
      | none => rfl
      | some p => simp [add_assoc]

/-- **The loop lane is semantics-preserving**: iterative execution equals the
recursive evaluation, answer and effect bag alike. -/
theorem runIter_eq_runFuel (M : TailMachine σ ε ρ) (n : Nat) (s : σ) :
    runIter M n s = runFuel M n s := by
  rw [runIter, runIterAux_eq]
  cases h : runFuel M n s with
  | none => rfl
  | some p => simp

/-- Deterministic tails are fuel-monotone: a halted run is unchanged by more
fuel.  (The general driver does NOT have this property — that failure is why
`FuelConvergence` exists; this class is its positive instance.) -/
theorem runFuel_mono (M : TailMachine σ ε ρ) :
    ∀ {n : Nat} {s : σ} {v : ρ × Multiset ε}, runFuel M n s = some v →
      ∀ {m : Nat}, n ≤ m → runFuel M m s = some v := by
  intro n
  induction n with
  | zero => intro s v h; exact absurd h (by simp [runFuel])
  | succ n ih =>
    intro s v h m hle
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 :=
      ⟨m - 1, by omega⟩
    have hle' : n ≤ m' := by omega
    cases hstep : M.step s with
    | halt r =>
      rw [runFuel_succ_halt hstep] at h ⊢
      exact h
    | next s' out =>
      rw [runFuel_succ_next hstep] at h ⊢
      cases hrec : runFuel M n s' with
      | none => rw [hrec] at h; simp at h
      | some p =>
        rw [hrec] at h
        rw [ih hrec hle']
        exact h

/-- A halting deterministic tail run is `StableFrom` its halting fuel — the
weld to the corpus's convergence abstraction. -/
theorem stableFrom_of_halts (M : TailMachine σ ε ρ) {N : Nat} {s : σ}
    {v : ρ × Multiset ε} (h : runFuel M N s = some v) :
    StableFrom (fun n => runFuel M n s) N := by
  intro n hn
  simp only
  rw [runFuel_mono M h hn, h]

/-- Every halting deterministic tail run converges. -/
theorem converges_of_halts (M : TailMachine σ ε ρ) {N : Nat} {s : σ}
    {v : ρ × Multiset ε} (h : runFuel M N s = some v) :
    Converges (fun n => runFuel M n s) :=
  ⟨N, stableFrom_of_halts M h⟩

/-- **Invariant transfer** (the loop lane's entry-guard contract): an invariant
preserved by every unfolding, and discharged into `Q` at the halt, holds of
every whole-run result — at any fuel. -/
theorem invariant_transfer (M : TailMachine σ ε ρ)
    (P : σ → Prop) (Q : ρ → Prop)
    (hstep : ∀ s, P s → (match M.step s with
      | .next s' _ => P s'
      | .halt r => Q r)) :
    ∀ {n : Nat} {s : σ} {r : ρ} {out : Multiset ε},
      runFuel M n s = some (r, out) → P s → Q r := by
  intro n
  induction n with
  | zero => intro s r out h; exact absurd h (by simp [runFuel])
  | succ n ih =>
    intro s r out h hP
    cases hstep' : M.step s with
    | halt r' =>
      rw [runFuel_succ_halt hstep'] at h
      obtain ⟨rfl, -⟩ : r' = r ∧ (0 : Multiset ε) = out := by
        simpa using h
      have := hstep s hP
      rw [hstep'] at this
      exact this
    | next s' out' =>
      rw [runFuel_succ_next hstep'] at h
      cases hrec : runFuel M n s' with
      | none => rw [hrec] at h; simp at h
      | some p =>
        rw [hrec] at h
        have hP' : P s' := by
          have := hstep s hP
          rw [hstep'] at this
          exact this
        obtain ⟨r₀, out₀⟩ := p
        obtain ⟨rfl, -⟩ : r₀ = r ∧ out' + out₀ = out := by
          simpa using h
        exact ih hrec hP'

/-! ## The concrete mirror: a countdown loop emitting one effect per step -/

/-- The 100k-add-atom loop's semantic skeleton: count down from `n`, emitting
`item k` at each step `k`, halting at zero. -/
def addLoop (item : Nat → ε) : TailMachine Nat ε Unit where
  step n :=
    match n with
    | 0 => .halt ()
    | k + 1 => .next k {item (k + 1)}

/-- Closed-form effect bag: running the countdown from `N` with fuel `N + 1`
halts and emits exactly the bag `{item 1, …, item N}`.  Positive instance with
content: the bag is characterized, not just existence. -/
theorem addLoop_run (item : Nat → ε) :
    ∀ N : Nat, runFuel (addLoop item) (N + 1) N =
      some ((), (Multiset.range N).map fun k => item (k + 1)) := by
  intro N
  induction N with
  | zero =>
    rw [runFuel_succ_halt (show (addLoop item).step 0 = .halt () from rfl)]
    simp
  | succ N ih =>
    rw [runFuel_succ_next
          (show (addLoop item).step (N + 1) = .next N {item (N + 1)} from rfl),
        ih]
    simp [Multiset.range_succ, Multiset.singleton_add]

/-- The loop lane computes the same closed form (equivalence instantiated). -/
theorem addLoop_runIter (item : Nat → ε) (N : Nat) :
    runIter (addLoop item) (N + 1) N =
      some ((), (Multiset.range N).map fun k => item (k + 1)) := by
  rw [runIter_eq_runFuel]
  exact addLoop_run item N

/-- Negative boundary, stated honestly: fuel `N` is one short of the halting
budget for a countdown from `N`, so the run is `none` — the kernel never
fabricates a result below the halting budget. -/
theorem addLoop_run_underfueled (item : Nat → ε) :
    ∀ N : Nat, runFuel (addLoop item) N N = none := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [runFuel_succ_next
          (show (addLoop item).step (N + 1) = .next N {item (N + 1)} from rfl),
        ih]
    rfl

end Mettapedia.Languages.MeTTa.TailLoopKernel
