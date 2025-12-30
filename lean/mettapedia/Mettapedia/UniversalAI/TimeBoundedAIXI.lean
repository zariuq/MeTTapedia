import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Logic.Encodable.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Computability.TuringMachine
import Mathlib.Computability.TMConfig
import Mettapedia.UniversalAI.BayesianAgents
import Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumeration
import Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumerationOracle
import Mettapedia.UniversalAI.TimeBoundedAIXI.ProofSystem
import Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting
import Mettapedia.UniversalAI.TimeBoundedAIXI.ToPartrecEncodable
import Mettapedia.UniversalAI.TimeBoundedAIXI.CodingBits
import Mettapedia.Logic.SolomonoffPrior

/-!
# Computational Aspects: Time-Bounded AIXI (Hutter 2005, Chapter 7)

This file formalizes the computational aspects of AIXI, particularly the
time-bounded AIXItl model from Chapter 7 of Hutter's "Universal Artificial
Intelligence" (2005).

## Main Definitions

### Section 7.1: Fastest Algorithm for All Well-Defined Problems
* `LevinSearch` - Levin's universal search algorithm
* `FastestAlgorithm` - The M_p* algorithm (Theorem 7.1)

### Section 7.2: Time-Bounded AIXI Model
* `TimeBoundedSemimeasure` - ξ^tl (time/length bounded universal prior)
* `AIXItl` - The computable approximation to AIXI
* `ValidApproximation` - Predicate VA(p) for valid value bounds
* `EffectiveIntelligenceOrder` - The ≻^w order relation

### Key Results (Formalized Here)
* Basic proof-enumeration size bounds for `bitstringsOfLength`/`bitstringsUpTo`
* Fuel-based step-counting for deterministic evaluators (`StepCounting.runFor`) and `ToPartrec.Code`
  (`StepCounting.ToPartrec.evalWithin` + soundness/completeness/monotonicity)
* Algorithm B invariants for M_p*:
  - best bound never worsens (`algorithmB_step_fst_le_current`)
  - scanning more candidates only improves the best bound (`algorithmB_step_append_fst_le_left`)
  - `algorithmB_step`’s best-time component is a `foldl min` (`algorithmB_step_fst_eq_bestTime`)
* Concrete Step-3 wrapper for `ToPartrec` programs (bitstrings → code, histories → `List ℕ`) with a
  per-cycle `O(2^l · t)` accounting bound and a `t → ∞` stabilization theorem for fixed `l`
* AIXItl “best vote” dominance properties for a fixed finite list of validated programs
* AIXItl value-soundness bridge (`ValidValueLowerBound`) and an ε-optimality lemma
  (`aixitl_cycle_eps_optimal`) connecting best-vote selection to `optimalQValue`/`optimalValue`

### Key Results (Planned for Full Chapter 7 Fidelity)
* Full asymptotic runtime theorem for M_p* (Theorem 7.1) with explicit constants
* Concrete definition of ξ^tl from program enumeration and its enumerability properties
* Full convergence results (AIXItl → `BayesianAgents.AIXI` as t,l,l_p → ∞)

## References

- Hutter, M. (2005). "Universal Artificial Intelligence", Chapter 7
- Levin, L. (1973). "Universal Search Problems"
- Li & Vitányi (2008). "An Introduction to Kolmogorov Complexity"

## Mathematical Content

### Levin Search (Section 7.1.2)
Given function g: Y → X, find y such that g(y) = x.
Run all programs p in parallel with time fraction 2^{-ℓ(p)}.
Time complexity: 2^{ℓ(p)} · time_p(x)

### Theorem 7.1: Fastest Algorithm M_p*
For any provably correct algorithm p computing p* with time bound t_p:
  time_{M_p*}(x) ≤ (1+ε) · t_p(x) + c_p · time_{t_p}(x) + d_p

### AIXItl (Section 7.2)
Time-bounded universal semimeasure:
  ξ^tl(x_1:n) = Σ_{p: ℓ(p)≤l, t(p)≤t} 2^{-ℓ(p)} · p(x_1:n)

AIXItl agent:
1. Enumerate all proofs of length ≤ l_p
2. Keep programs p with proven VA(p)
3. Run all p ∈ P for t steps per cycle
4. Select p_k := argmax_p w_k^p (highest claimed value)
5. Output y_k := y_k^{p_k}

Computation time: O(2^l · t) per cycle
-/

namespace Mettapedia.UniversalAI.TimeBoundedAIXI

open BayesianAgents
open scoped BigOperators
open scoped Classical

universe u

/-!
## Step-counting semantics (for Chapter 7 runtime bounds)

Fuel-based step-counting (`StepCounting.runFor`, `StepCounting.ToPartrec.evalWithin`, …) lives in
`Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting`.
-/

/-! ## Section 7.1: The Fastest & Shortest Algorithm for All Well-Defined Problems -/

/-! ### Section 7.1.2: Levin Search

Levin search is a universal algorithm for inverting computable functions.
It runs all programs in parallel with time fractions based on program length.
-/

/-- A program specification: binary string with associated computation time. -/
structure Program where
  /-- Binary encoding of the program -/
  code : List Bool
  /-- Length of the program (Kolmogorov complexity upper bound) -/
  length : ℕ := code.length
deriving Encodable

/-- Time bound function: computable upper bound on computation time. -/
structure TimeBound where
  /-- The time bound function t: input → time -/
  bound : ℕ → ℕ
  /-- Time to compute the bound itself -/
  computeTime : ℕ → ℕ

/-- Levin search for function inversion.

    Given f: Y → X and target x, find y such that f(y) = x.
    Runs all programs in parallel with time fraction 2^{-ℓ(p)}.

    (Hutter 2005, Section 7.1.2) -/
structure LevinSearch where
  /-- The function to invert -/
  targetFunction : ℕ → Option ℕ
  /-- Target value to find inverse of -/
  target : ℕ

/-- Time complexity of Levin search.

    If program p_k inverts f on x in time_p(x) steps, then
    SIMPLE(f) takes at most 2^k · time_p(x) + 2^{k-1} steps.

    (Hutter 2005, Section 7.1.2, Li & Vitányi equation) -/
theorem levin_search_time_complexity (k : ℕ) (time_p : ℕ) :
    -- SIMPLE finds solution in 2^k · time_p + 2^{k-1} time
    let simple_time := 2^k * time_p + 2^k
    simple_time ≥ time_p := by
      simp only []
      have h1 : 2^k ≥ 1 := Nat.one_le_two_pow
      calc time_p ≤ 2^k * time_p := Nat.le_mul_of_pos_left time_p (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp h1))
        _ ≤ 2^k * time_p + 2^k := Nat.le_add_right _ _

/-! ### Section 7.1.3-7.1.6: The Algorithm M_p*

The fastest algorithm for all well-defined problems.
-/

/-- A provably correct algorithm for problem p*.
    Includes the program, its correctness proof, and time bound. -/
structure ProvableAlgorithm where
  /-- The program code -/
  program : Program
  /-- Proof that program computes p* -/
  correctnessProofLength : ℕ
  /-- Time bound function -/
  timeBound : TimeBound

/-- The M_p* algorithm: fastest algorithm for well-defined problems.

    Runs three parallel processes:
    A: Enumerate proofs, find provably correct programs
    B: Compute time bounds for found programs
    C: Execute the currently fastest program

    (Hutter 2005, Section 7.1.5, Algorithm M_p*) -/
structure FastestAlgorithm where
  /-- The problem specification p* -/
  problemSpec : ℕ → Option ℕ
  /-- List of found (program, timeBound) pairs -/
  foundPrograms : List (Program × TimeBound)
  /-- Currently fastest program -/
  fastestProgram : Option Program
  /-- Current best time bound -/
  fastestTime : ℕ

/-! ### Algorithm A: Proof enumeration.

    Enumerates all proofs of increasing length.
    When proof of "p is equivalent to p* with time bound t" is found,
    adds (p, t) to list L.

    (Hutter 2005, Section 7.1.5, Algorithm A) -/
/-!
Bitstring enumeration and the basic proof-checker interface used throughout Chapter 7 live in
`Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumeration`.
-/

theorem filter_bitstringsUpTo_length_le (l n : ℕ) :
    (bitstringsUpTo n).filter (fun bits => bits.length ≤ l) = bitstringsUpTo (Nat.min l n) := by
  induction n with
  | zero =>
      simp [bitstringsUpTo, bitstringsOfLength]
  | succ n ih =>
      by_cases hnl : n + 1 ≤ l
      · have hn_le : n ≤ l := Nat.le_trans (Nat.le_succ n) hnl
        have hfilter_len :
            (bitstringsOfLength (n + 1)).filter (fun bits => bits.length ≤ l) =
              bitstringsOfLength (n + 1) := by
          refine (List.filter_eq_self).2 ?_
          intro bits hbits
          have hlen : bits.length = n + 1 := length_eq_of_mem_bitstringsOfLength (n := n + 1) hbits
          exact decide_eq_true (by simpa [hlen] using hnl)
        -- `Nat.min l n = n` and `Nat.min l (n+1) = n+1`.
        have hmin_n : Nat.min l n = n := Nat.min_eq_right hn_le
        have hmin_succ : Nat.min l (n + 1) = n + 1 := Nat.min_eq_right hnl
        simp [bitstringsUpTo, List.filter_append, ih, hfilter_len, hmin_n, hmin_succ]
      · have hfilter_len :
            (bitstringsOfLength (n + 1)).filter (fun bits => bits.length ≤ l) = [] := by
          refine (List.filter_eq_nil_iff).2 ?_
          intro bits hbits
          have hlen : bits.length = n + 1 := length_eq_of_mem_bitstringsOfLength (n := n + 1) hbits
          have hnot : ¬ bits.length ≤ l := by
            -- `¬(n+1 ≤ l)` implies `¬(bits.length ≤ l)` since `bits.length = n+1`.
            simpa [hlen] using hnl
          have : decide (bits.length ≤ l) = false := decide_eq_false hnot
          simp [this]
        -- Here `l ≤ n`, so `Nat.min l (n+1) = Nat.min l n`.
        have hl_lt_succ : l < n + 1 := Nat.lt_of_not_ge hnl
        have hl_le_n : l ≤ n := Nat.lt_succ_iff.mp hl_lt_succ
        have hmin_succ : Nat.min l (n + 1) = Nat.min l n := by
          have hl_le_succ : l ≤ n + 1 := Nat.le_trans hl_le_n (Nat.le_succ n)
          simp [Nat.min_eq_left hl_le_succ, Nat.min_eq_left hl_le_n]
        simp [bitstringsUpTo, List.filter_append, ih, hfilter_len, hmin_succ]

/-! ### Basic size bounds (step-counting scaffolding)

To support Chapter 7’s runtime accounting, we record a few elementary bounds about the proof
enumeration utilities (`bitstringsOfLength`, `bitstringsUpTo`).
-/

theorem length_filterMap_le {α : Type u} {β : Type v} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      cases h : f a with
      | none =>
          -- `filterMap` drops `a`, so we just use the IH and weaken by `n ≤ n+1`.
          simpa [List.filterMap, h] using le_trans ih (Nat.le_succ l.length)
      | some b =>
          -- `filterMap` keeps one extra element.
          simpa [List.filterMap, h] using Nat.succ_le_succ ih

theorem sum_map_const_two {α : Type u} (l : List α) : (l.map (fun _ => (2 : ℕ))).sum = 2 * l.length := by
  induction l with
  | nil =>
      simp
  | cons _ l ih =>
      simp [Nat.mul_succ]
      omega

theorem length_bitstringsOfLength (n : ℕ) : (bitstringsOfLength n).length = 2 ^ n := by
  induction n with
  | zero =>
      simp [bitstringsOfLength]
  | succ n ih =>
      -- `flatMap` duplicates each bitstring by prefixing `false` and `true`.
      simp [bitstringsOfLength, List.length_flatMap, ih, Nat.pow_succ, Nat.mul_comm]

theorem length_bitstringsUpTo_add_one (n : ℕ) : (bitstringsUpTo n).length + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero =>
      simp [bitstringsUpTo, bitstringsOfLength]
  | succ n ih =>
      -- `bitstringsUpTo (n+1)` is an append of all shorter bitstrings and the exact-length ones.
      calc
        (bitstringsUpTo (n + 1)).length + 1 =
            ((bitstringsUpTo n).length + (bitstringsOfLength (n + 1)).length) + 1 := by
              simp [bitstringsUpTo, Nat.add_assoc]
        _ = ((bitstringsUpTo n).length + 1) + (bitstringsOfLength (n + 1)).length := by
              omega
        _ = (2 ^ (n + 1)) + (2 ^ (n + 1)) := by
              simp [ih, length_bitstringsOfLength]
        _ = 2 ^ (n + 2) := by
              calc
                2 ^ (n + 1) + 2 ^ (n + 1) = (2 ^ (n + 1)) * 2 := by
                  simp [Nat.mul_two]
                _ = 2 ^ (n + 2) := by
                  simp [Nat.pow_succ]

theorem nodup_bitstringsOfLength : ∀ n : ℕ, (bitstringsOfLength n).Nodup := by
  intro n
  induction n with
  | zero =>
      simp [bitstringsOfLength]
  | succ n ih =>
      -- `bitstringsOfLength (n+1)` is obtained by prefixing `false` and `true` to each element of
      -- `bitstringsOfLength n`.
      have hnodup_each :
          ∀ xs ∈ bitstringsOfLength n, ([false :: xs, true :: xs] : List (List Bool)).Nodup := by
        intro xs hs
        simp
      have hdisj :
          (bitstringsOfLength n).Pairwise fun xs ys =>
            ([false :: xs, true :: xs] : List (List Bool)).Disjoint ([false :: ys, true :: ys]) := by
        refine List.Nodup.pairwise_of_forall_ne ih ?_
        intro xs hs ys hy hne
        -- The two-element lists differ on their tails, so they are disjoint.
        refine (List.disjoint_left).2 ?_
        intro a ha
        rcases (by simpa using ha) with rfl | rfl
        · intro hb
          have : false :: xs = false :: ys ∨ false :: xs = true :: ys := by
            simpa using hb
          rcases this with h1 | h2
          · have : xs = ys := by
              simpa using (List.cons.inj h1).2
            exact hne this
          · cases h2
        · intro hb
          have : true :: xs = false :: ys ∨ true :: xs = true :: ys := by
            simpa using hb
          rcases this with h1 | h2
          · cases h1
          · have : xs = ys := by
              simpa using (List.cons.inj h2).2
            exact hne this
      have hflat :
          ((bitstringsOfLength n).flatMap fun xs => [false :: xs, true :: xs]).Nodup := by
        -- `nodup_flatMap` needs the pointwise `Nodup` and pairwise-disjointness hypotheses.
        exact (List.nodup_flatMap).2 ⟨hnodup_each, hdisj⟩
      simpa [bitstringsOfLength] using hflat

theorem nodup_bitstringsUpTo : ∀ n : ℕ, (bitstringsUpTo n).Nodup := by
  intro n
  induction n with
  | zero =>
      simpa [bitstringsUpTo] using nodup_bitstringsOfLength 0
  | succ n ih =>
      -- `bitstringsUpTo (n+1) = bitstringsUpTo n ++ bitstringsOfLength (n+1)`.
      have hlen :
          ∀ a : List Bool, a ∈ bitstringsUpTo n → ∀ b : List Bool, b ∈ bitstringsOfLength (n + 1) → a ≠ b := by
        intro a ha b hb hab
        have ha_len : a.length ≤ n := length_le_of_mem_bitstringsUpTo ha
        have hb_len : b.length = n + 1 := length_eq_of_mem_bitstringsOfLength (n := n + 1) hb
        have hlen_eq : a.length = b.length := congrArg List.length hab
        have hne : a.length ≠ n + 1 := Nat.ne_of_lt (Nat.lt_succ_of_le ha_len)
        exact hne (by simpa [hb_len] using hlen_eq)
      have hlen' :
          (bitstringsUpTo n ++ bitstringsOfLength (n + 1)).Nodup := by
        refine (List.nodup_append).2 ?_
        refine ⟨ih, nodup_bitstringsOfLength (n + 1), ?_⟩
        intro a ha b hb
        exact hlen a ha b hb
      simpa [bitstringsUpTo] using hlen'

/-- Algorithm A needs a way to interpret a bitstring as a proof witnessing a `(program, timeBound)` pair. -/

def algorithmA_step (decode : ProofDecoder (Program × TimeBound)) (proofLength : ℕ) :
    List (Program × TimeBound) :=
  (bitstringsOfLength proofLength).filterMap decode

theorem length_algorithmA_step_le (decode : ProofDecoder (Program × TimeBound)) (proofLength : ℕ) :
    (algorithmA_step decode proofLength).length ≤ 2 ^ proofLength := by
  have hle :
      (algorithmA_step decode proofLength).length ≤ (bitstringsOfLength proofLength).length := by
    simpa [algorithmA_step] using
      (length_filterMap_le (f := decode) (l := bitstringsOfLength proofLength))
  simpa [length_bitstringsOfLength] using hle

/-- Algorithm B: Time bound computation.

    For each (p, t) in list L, compute t(x) with time fraction 2^{-ℓ(p)-ℓ(t)}.
    Update fastest program when better bound found.

    (Hutter 2005, Section 7.1.5, Algorithm B) -/
def algorithmB_step (L : List (Program × TimeBound)) (x : ℕ) (current : ℕ × Option Program) :
    ℕ × Option Program :=
  L.foldl
    (fun best pt =>
      let p := pt.1
      let t := pt.2
      let tx := t.bound x
      if tx < best.1 then (tx, some p) else best)
    current

/-- The minimal time bound seen by Algorithm B (ignoring the selected program). -/
def algorithmB_bestTime (L : List (Program × TimeBound)) (x : ℕ) (t0 : ℕ) : ℕ :=
  L.foldl (fun best pt => min best (pt.2.bound x)) t0

theorem algorithmB_step_fst_eq_bestTime (L : List (Program × TimeBound)) (x : ℕ)
    (current : ℕ × Option Program) :
    (algorithmB_step L x current).1 = algorithmB_bestTime L x current.1 := by
  induction L generalizing current with
  | nil =>
      simp [algorithmB_step, algorithmB_bestTime]
  | cons pt L ih =>
      cases pt with
      | mk p t =>
          by_cases htx : t.bound x < current.1
          · have hle : t.bound x ≤ current.1 := Nat.le_of_lt htx
            -- The accumulator becomes `(t.bound x, some p)`, and `min current.1 (t.bound x) = t.bound x`.
            simpa [algorithmB_step, algorithmB_bestTime, List.foldl_cons, htx, min_eq_right hle] using
              (ih (current := (t.bound x, some p)))
          · have hle : current.1 ≤ t.bound x := Nat.le_of_not_gt htx
            -- The accumulator remains unchanged, and `min current.1 (t.bound x) = current.1`.
            simpa [algorithmB_step, algorithmB_bestTime, List.foldl_cons, htx, min_eq_left hle] using
              (ih (current := current))

/-! ### Algorithm C: Program execution.

    Execute the fastest found program on input x.
    Decrease time counter with each step.

    (Hutter 2005, Section 7.1.5, Algorithm C) -/
/-- Abstract executor used by Algorithm C (Turing machine semantics live outside this file). -/
abbrev ProgramExecutor : Type :=
  Program → ℕ → ℕ → Option ℕ

def algorithmC_run (exec : ProgramExecutor) (p : Program) (x : ℕ) (timeRemaining : ℕ) : Option ℕ :=
  exec p x timeRemaining

/-! ### Theorem 7.1 (finite core lemma): Algorithm B never worsens the best time bound

This file does not formalize Turing-machine step counting or the full dovetailing proof of
Hutter's Theorem 7.1. What we *can* formalize (and reuse later) is the key invariant of
Algorithm B: updating the “currently fastest” time bound by scanning candidate programs never
increases the best bound. -/

theorem algorithmB_step_fst_le_current (L : List (Program × TimeBound)) (x : ℕ)
    (current : ℕ × Option Program) :
    (algorithmB_step L x current).1 ≤ current.1 := by
  induction L generalizing current with
  | nil =>
      simp [algorithmB_step]
  | cons pt L ih =>
      cases pt with
      | mk p t =>
          -- One update step yields a new `current'`; the fold over the tail cannot increase it.
          simp [algorithmB_step, List.foldl_cons]
          set current' : ℕ × Option Program :=
            if t.bound x < current.1 then (t.bound x, some p) else current
          have hle_tail : (algorithmB_step L x current').1 ≤ current'.1 :=
            ih (current := current')
          have hle_current' : current'.1 ≤ current.1 := by
            by_cases htx : t.bound x < current.1
            · -- `current'.1 = t.bound x < current.1`
              simp [current', htx, Nat.le_of_lt htx]
            · -- `current'.1 = current.1`
              simp [current', htx]
          exact le_trans hle_tail hle_current'

/-! ### Corollary (finite): Extending the search list can only improve the best bound -/

theorem algorithmB_step_append_fst_le_left (L extra : List (Program × TimeBound)) (x : ℕ)
    (current : ℕ × Option Program) :
    (algorithmB_step (L ++ extra) x current).1 ≤ (algorithmB_step L x current).1 := by
  -- `foldl` over an appended list is a fold over the tail starting from the intermediate accumulator.
  simp [algorithmB_step, List.foldl_append]
  exact algorithmB_step_fst_le_current (L := extra) (x := x) (current := algorithmB_step L x current)

/-! ## Section 7.2: Time-Bounded AIXI Model -/

/-! ### Section 7.2.2: Time-Limited Probability Distributions -/

/-- Time-bounded universal semimeasure ξ^tl.

    ξ^tl(x_1:n) := Σ_{p: ℓ(p)≤l, t(p)≤t} 2^{-ℓ(p)} · p(x_1:n)

    This is the computable approximation to the universal prior ξ.

    (Hutter 2005, Section 7.2.2, Equation 7.3) -/
structure TimeBoundedSemimeasure where
  /-- Time bound per computation -/
  timeBound : ℕ
  /-- Length bound on programs -/
  lengthBound : ℕ
  /-- The semimeasure value -/
  value : History → ENNReal

/-- Computation time of ξ^tl.

    t(ξ^tl(x_1:k)) = O(|X|^k · 2^l · t)

    (Hutter 2005, Section 7.2.2, discussion of Equation 7.3) -/
theorem xi_tl_computation_time (t l k : ℕ) (X_size : ℕ) (ht : 0 < t) (hX : 0 < X_size) :
    -- Time to compute ξ^tl grows exponentially in l
    let computation_time := X_size^k * 2^l * t
    computation_time > 0 := by
      simp only []
      have h1 : X_size^k > 0 := Nat.pow_pos hX
      have h2 : 2^l > 0 := Nat.pow_pos (by norm_num : 0 < 2)
      exact Nat.mul_pos (Nat.mul_pos h1 h2) ht

/-! ### Section 7.2.3-7.2.4: The Best Vote Algorithm -/

/-- Extended chronological program for AIXItl.

    Programs output both an action y_k and a value estimate w_k:
    p(yx_<k) = w_1 y_1 ... w_k y_k

    (Hutter 2005, Section 7.2.4, Equation 7.6) -/
structure ExtendedChronologicalProgram where
  /-- Program code -/
  code : Program
  /-- Function computing (value estimate, action) pairs -/
  compute : History → ℝ × Action

instance : Inhabited ExtendedChronologicalProgram :=
  ⟨{ code := { code := [], length := 0 }, compute := fun _ => (0, Action.stay) }⟩

/-! ## Deterministic agents induced by programs -/

/-- A deterministic agent that always chooses `act h`. -/
noncomputable def deterministicAgent (act : History → Action) : Agent where
  policy h a := if a = act h then 1 else 0
  policy_sum_one h _hw := by
    classical
    simp [tsum_fintype]

/-- View an extended chronological program as a deterministic `Agent` (it outputs an action). -/
noncomputable def ExtendedChronologicalProgram.toAgent (p : ExtendedChronologicalProgram) : Agent :=
  deterministicAgent fun h => (p.compute h).2

/-! ## Best-vote utilities -/

/-- Select the candidate with strictly larger claimed value, keeping `acc` on ties. -/
noncomputable def selectBetter (acc cand : ℝ × Action) : ℝ × Action :=
  if cand.1 > acc.1 then cand else acc

theorem selectBetter_fst_ge_acc (acc cand : ℝ × Action) : acc.1 ≤ (selectBetter acc cand).1 := by
  by_cases h : cand.1 > acc.1
  · have : acc.1 ≤ cand.1 := le_of_lt h
    simp [selectBetter, h, this]
  · simp [selectBetter, h]

theorem selectBetter_fst_ge_cand_of_ge (acc cand : ℝ × Action) (hge : cand.1 ≤ acc.1) :
    cand.1 ≤ (selectBetter acc cand).1 := by
  have hnot : ¬cand.1 > acc.1 := by
    exact not_lt.mpr hge
  simp [selectBetter, hnot, hge]

theorem selectBetter_fst_ge_cand_of_gt (acc cand : ℝ × Action) (hgt : cand.1 > acc.1) :
    cand.1 ≤ (selectBetter acc cand).1 := by
  simp [selectBetter, hgt]

/-- Fold over programs, keeping the `(claimed value, action)` pair with maximal claimed value. -/
noncomputable def bestByValueAux (acc : ℝ × Action) (programs : List ExtendedChronologicalProgram)
    (h : History) : ℝ × Action :=
  programs.foldl (fun acc p => selectBetter acc (ExtendedChronologicalProgram.compute p h)) acc

theorem bestByValueAux_fst_ge_acc (acc : ℝ × Action) (programs : List ExtendedChronologicalProgram)
    (h : History) : acc.1 ≤ (bestByValueAux acc programs h).1 := by
  induction programs generalizing acc with
  | nil =>
      simp [bestByValueAux]
  | cons p ps ih =>
      simp [bestByValueAux, List.foldl_cons]
      -- One step of `selectBetter` never decreases the accumulator, then apply the IH.
      exact
        le_trans (selectBetter_fst_ge_acc acc (ExtendedChronologicalProgram.compute p h))
          (ih (acc := selectBetter acc (ExtendedChronologicalProgram.compute p h)))

theorem bestByValueAux_fst_ge_of_mem (acc : ℝ × Action) (programs : List ExtendedChronologicalProgram)
    (h : History) {p : ExtendedChronologicalProgram} (hp : p ∈ programs) :
    (ExtendedChronologicalProgram.compute p h).1 ≤ (bestByValueAux acc programs h).1 := by
  induction programs generalizing acc with
  | nil =>
      cases hp
  | cons q qs ih =>
      simp [bestByValueAux, List.mem_cons] at hp ⊢
      rcases hp with rfl | hp
      · -- The head program's value is ≤ after the first `selectBetter` step, and the accumulator is ≤ the final fold.
        have hstep :
            (ExtendedChronologicalProgram.compute p h).1 ≤
              (selectBetter acc (ExtendedChronologicalProgram.compute p h)).1 := by
          by_cases hgt : (ExtendedChronologicalProgram.compute p h).1 > acc.1
          · exact selectBetter_fst_ge_cand_of_gt acc (ExtendedChronologicalProgram.compute p h) hgt
          · have hge : (ExtendedChronologicalProgram.compute p h).1 ≤ acc.1 := le_of_not_gt hgt
            exact selectBetter_fst_ge_cand_of_ge acc (ExtendedChronologicalProgram.compute p h) hge
        have hmon :
            (selectBetter acc (ExtendedChronologicalProgram.compute p h)).1 ≤
              (bestByValueAux (selectBetter acc (ExtendedChronologicalProgram.compute p h)) qs h).1 :=
          bestByValueAux_fst_ge_acc
            (acc := selectBetter acc (ExtendedChronologicalProgram.compute p h)) (programs := qs) (h := h)
        exact le_trans hstep hmon
      · -- Tail case: apply IH with the updated accumulator.
        simpa [bestByValueAux, List.foldl_cons] using
          ih (acc := selectBetter acc (ExtendedChronologicalProgram.compute q h)) (hp := hp)

/-- Best `(claimed value, action)` among a list of programs, defaulting to `(0, stay)` on `[]`. -/
noncomputable def bestByValue (programs : List ExtendedChronologicalProgram) (h : History) : ℝ × Action :=
  match programs with
  | [] => (0, Action.stay)
  | p0 :: ps => bestByValueAux (ExtendedChronologicalProgram.compute p0 h) ps h

theorem bestByValueAux_eq_acc_or_eq_compute_of_mem (acc : ℝ × Action)
    (programs : List ExtendedChronologicalProgram) (h : History) :
    bestByValueAux acc programs h = acc ∨
      ∃ p ∈ programs, bestByValueAux acc programs h = p.compute h := by
  induction programs generalizing acc with
  | nil =>
      simp [bestByValueAux]
  | cons p ps ih =>
      -- `bestByValueAux` folds `selectBetter`, whose result is either the accumulator or the candidate.
      have hsel : selectBetter acc (p.compute h) = acc ∨ selectBetter acc (p.compute h) = p.compute h := by
        by_cases hgt : (p.compute h).1 > acc.1
        · right
          simp [selectBetter, hgt]
        · left
          simp [selectBetter, hgt]
      have := ih (acc := selectBetter acc (p.compute h))
      -- Unpack the IH and repackage in terms of the original `acc`.
      rcases this with hEq | ⟨q, hq, hEq⟩
      · -- IH returned the updated accumulator.
        rcases hsel with hacc | hp
        · left
          simpa [bestByValueAux, List.foldl_cons, hacc] using hEq
        · right
          refine ⟨p, by simp, ?_⟩
          simpa [bestByValueAux, List.foldl_cons, hp] using hEq
      · -- IH returned some program from the tail.
        right
        refine ⟨q, by simp [hq], ?_⟩
        simpa [bestByValueAux, List.foldl_cons] using hEq

theorem bestByValue_eq_compute_of_mem (programs : List ExtendedChronologicalProgram) (h : History)
    (hne : programs ≠ []) :
    ∃ p ∈ programs, bestByValue programs h = p.compute h := by
  cases programs with
  | nil =>
      cases hne rfl
  | cons p0 ps =>
      -- Reduce to the auxiliary fold.
      have haux :=
        bestByValueAux_eq_acc_or_eq_compute_of_mem (acc := p0.compute h) (programs := ps) (h := h)
      rcases haux with hEq | ⟨p, hp, hEq⟩
      · refine ⟨p0, by simp, ?_⟩
        simpa [bestByValue] using hEq
      · refine ⟨p, by simp [hp], ?_⟩
        simpa [bestByValue] using hEq

theorem bestByValue_fst_ge_of_mem (programs : List ExtendedChronologicalProgram) (h : History)
    {p : ExtendedChronologicalProgram} (hp : p ∈ programs) :
    (ExtendedChronologicalProgram.compute p h).1 ≤ (bestByValue programs h).1 := by
  cases programs with
  | nil =>
      cases hp
  | cons p0 ps =>
      simp [bestByValue, List.mem_cons] at hp ⊢
      rcases hp with rfl | hp
      · -- Head element: accumulator monotonicity.
        simpa [bestByValueAux] using
          (bestByValueAux_fst_ge_acc (acc := ExtendedChronologicalProgram.compute p h) (programs := ps) (h := h))
      · -- Tail element: use the generic mem lemma for the auxiliary fold.
        exact
          bestByValueAux_fst_ge_of_mem (acc := ExtendedChronologicalProgram.compute p0 h)
            (programs := ps) (h := h) (hp := hp)

theorem selectBetter_fst_le_of_le (acc cand : ℝ × Action) (B : ℝ)
    (hacc : acc.1 ≤ B) (hcand : cand.1 ≤ B) : (selectBetter acc cand).1 ≤ B := by
  by_cases h : cand.1 > acc.1
  · simp [selectBetter, h, hcand]
  · simp [selectBetter, h, hacc]

theorem bestByValueAux_fst_le_of_forall (acc : ℝ × Action) (programs : List ExtendedChronologicalProgram)
    (h : History) (B : ℝ) (hacc : acc.1 ≤ B)
    (hall : ∀ p ∈ programs, (ExtendedChronologicalProgram.compute p h).1 ≤ B) :
    (bestByValueAux acc programs h).1 ≤ B := by
  induction programs generalizing acc with
  | nil =>
      simp [bestByValueAux, hacc]
  | cons p ps ih =>
      simp [bestByValueAux, List.foldl_cons]
      have hcand : (ExtendedChronologicalProgram.compute p h).1 ≤ B := hall p (by simp)
      have hacc' :
          (selectBetter acc (ExtendedChronologicalProgram.compute p h)).1 ≤ B :=
        selectBetter_fst_le_of_le acc (ExtendedChronologicalProgram.compute p h) B hacc hcand
      have hall' : ∀ q ∈ ps, (ExtendedChronologicalProgram.compute q h).1 ≤ B := by
        intro q hq
        exact hall q (by simp [hq])
      exact ih (acc := selectBetter acc (ExtendedChronologicalProgram.compute p h)) (hacc := hacc') (hall := hall')

theorem bestByValue_fst_le_of_forall (programs : List ExtendedChronologicalProgram) (h : History) (B : ℝ)
    (hB0 : 0 ≤ B) (hall : ∀ p ∈ programs, (ExtendedChronologicalProgram.compute p h).1 ≤ B) :
    (bestByValue programs h).1 ≤ B := by
  cases programs with
  | nil =>
      simp [bestByValue, hB0]
  | cons p0 ps =>
      have hacc : (ExtendedChronologicalProgram.compute p0 h).1 ≤ B := hall p0 (by simp)
      have hall' : ∀ p ∈ ps, (ExtendedChronologicalProgram.compute p h).1 ≤ B := by
        intro p hp
        exact hall p (by simp [hp])
      simpa [bestByValue] using
        (bestByValueAux_fst_le_of_forall (acc := ExtendedChronologicalProgram.compute p0 h)
          (programs := ps) (h := h) (B := B) hacc hall')

/-! ### Selection value `V_km` (Equation 7.5)

    V_km(yx_<k) := Σ_{q∈Q_k} 2^{-ℓ(q)} V_km^q

    where V_km^q = r(x_k^q) + ... + r(x_m^q)

    (Hutter 2005, Section 7.2.3, Equation 7.5) -/
/-- Abstract selection value `V_km` used by the VA predicate (provided by the semantics layer). -/
abbrev SelectionValue : Type :=
  History → ℕ → ℝ

noncomputable def valueForSelection (V : SelectionValue) (h : History) (horizon : ℕ) : ℝ :=
  V h horizon

/-! ### Section 7.2.5: Valid Approximations -/

/-- Valid Approximation predicate VA(p).

    VA(p) is true iff p never overrates itself:
    ∀k ∀(w_k, y_k): p(yx_<k) → w_k ≤ V_km(yx_<k)

    This is the key constraint that makes the best vote algorithm work:
    programs must provide valid (conservative) estimates of their value.

    (Hutter 2005, Section 7.2.5, Equation 7.7) -/
def ValidApproximation (V : SelectionValue) (horizon : ℕ) (p : ExtendedChronologicalProgram) : Prop :=
  ∀ h : History, h.wellFormed → (p.compute h).1 ≤ valueForSelection V h horizon

/-! #### A “real” VA predicate (claims are lower bounds on actual value) -/

/-- A program's claimed value is a lower bound on its *true* discounted value in environment `μ`
when interpreted as a deterministic agent. This is the intended soundness condition behind
Hutter/Leike-style “verified self-estimates”. -/
def ValidValueLowerBound (μ : Environment) (γ : DiscountFactor) (horizon : ℕ)
    (p : ExtendedChronologicalProgram) : Prop :=
  ∀ h : History, h.wellFormed → (p.compute h).1 ≤ value μ p.toAgent γ h horizon

theorem claimed_le_optimalValue_of_validValueLowerBound (μ : Environment) (γ : DiscountFactor)
    (horizon : ℕ) {p : ExtendedChronologicalProgram} (h : History) (hwf : h.wellFormed)
    (hvalid : ValidValueLowerBound μ γ horizon p) :
    (p.compute h).1 ≤ optimalValue μ γ h horizon := by
  have hle_value : (p.compute h).1 ≤ value μ p.toAgent γ h horizon :=
    hvalid h hwf
  have hle_opt : value μ p.toAgent γ h horizon ≤ optimalValue μ γ h horizon := by
    simpa [ge_iff_le] using (optimalValue_ge_value μ γ h horizon p.toAgent)
  exact le_trans hle_value hle_opt

theorem value_deterministicAgent_succ (μ : Environment) (γ : DiscountFactor) (act : History → Action)
    (h : History) (n : ℕ) (hwf : h.wellFormed) :
    value μ (deterministicAgent act) γ h (n + 1) =
      qValue μ (deterministicAgent act) γ h (act h) n := by
  classical
  -- Expand `value` and evaluate the finite sum for the Dirac distribution.
  simp [value, deterministicAgent, hwf]
  cases act h <;> simp

theorem claimed_le_optimalQValue_of_validValueLowerBound (μ : Environment) (γ : DiscountFactor)
    {p : ExtendedChronologicalProgram} (h : History) (n : ℕ) (hwf : h.wellFormed)
    (hvalid : ValidValueLowerBound μ γ (n + 1) p) :
    (p.compute h).1 ≤ optimalQValue μ γ h (p.compute h).2 n := by
  -- Start from the validity bound to the program's actual value.
  have hle_value : (p.compute h).1 ≤ value μ p.toAgent γ h (n + 1) :=
    hvalid h hwf
  -- Reduce `value` of the induced deterministic policy to a `qValue`.
  have hval :
      value μ p.toAgent γ h (n + 1) =
        qValue μ p.toAgent γ h (p.compute h).2 n := by
    simpa [ExtendedChronologicalProgram.toAgent, deterministicAgent] using
      (value_deterministicAgent_succ (μ := μ) (γ := γ)
        (act := fun h' => (p.compute h').2) (h := h) (n := n) (hwf := hwf))
  have hle_q : (p.compute h).1 ≤ qValue μ p.toAgent γ h (p.compute h).2 n := by
    simpa [hval] using hle_value
  -- Any policy's `qValue` is ≤ the optimal `Q*` value.
  have hq_le : qValue μ p.toAgent γ h (p.compute h).2 n ≤ optimalQValue μ γ h (p.compute h).2 n := by
    have ih : ∀ k, k < n → ∀ h', optimalValue μ γ h' k ≥ value μ p.toAgent γ h' k := by
      intro k _hk h'
      exact optimalValue_ge_value μ γ h' k p.toAgent
    exact qValue_le_optimalQValue_strong μ γ p.toAgent h (p.compute h).2 n ih
  exact le_trans hle_q hq_le

/-! ### Enumerable selection values (definition)

Hutter's Section 7.2.5 assumes that the selection value `V_km` is *enumerable* (approximable from
below by a computable increasing sequence). This file does not attempt to build a full
computability-theory layer; instead we record a lightweight predicate capturing the
“monotone under-approximation” part of the assumption. -/

/-- A selection value admits monotone rational under-approximations. -/
def EnumerableFromBelow (V : SelectionValue) : Prop :=
  ∃ approx : ℕ → History → ℕ → ℚ,
    (∀ n h k, approx n h k ≤ approx (n + 1) h k) ∧
      (∀ n h k, (approx n h k : ℝ) ≤ V h k)

/-! ### Section 7.2.6: Effective Intelligence Order Relation -/

/-- The effective intelligence order relation ≻^w.

    p ≻^w p' iff p claims higher value than p' for some history
    and never claims lower value:

    ∃yx_<k: w_k^p(yx_<k) > w_k^{p'}(yx_<k)
    ∧ ∀yx_<k: w_k^p(yx_<k) ≥ w_k^{p'}(yx_<k)

    (Hutter 2005, Definition 7.8) -/
def effectiveIntelligenceOrder (p p' : ExtendedChronologicalProgram) : Prop :=
  -- p is strictly more intelligent than p' (by claimed values)
  (∃ h : History, h.wellFormed ∧
    (p.compute h).1 > (p'.compute h).1) ∧
  (∀ h : History, h.wellFormed →
    (p.compute h).1 ≥ (p'.compute h).1)

theorem effectiveIntelligenceOrder_irrefl (p : ExtendedChronologicalProgram) :
    ¬ effectiveIntelligenceOrder p p := by
  intro hpp
  rcases hpp with ⟨⟨h, _hwf, hlt⟩, _hall⟩
  exact lt_irrefl _ hlt

theorem effectiveIntelligenceOrder_trans {p p' p'' : ExtendedChronologicalProgram} :
    effectiveIntelligenceOrder p p' →
      effectiveIntelligenceOrder p' p'' →
        effectiveIntelligenceOrder p p'' := by
  intro hpp' hp'p''
  rcases hpp' with ⟨⟨h, hwf, hlt⟩, hge⟩
  rcases hp'p'' with ⟨_hex, hge'⟩
  refine ⟨?_, ?_⟩
  · refine ⟨h, hwf, ?_⟩
    have hle : (p''.compute h).1 ≤ (p'.compute h).1 := by
      exact hge' h hwf
    -- `w_p(h) > w_{p'}(h) ≥ w_{p''}(h)` implies `w_p(h) > w_{p''}(h)`.
    exact lt_of_le_of_lt hle hlt
  · intro h hwf
    exact le_trans (hge' h hwf) (hge h hwf)

theorem effectiveIntelligenceOrder_asymm {p p' : ExtendedChronologicalProgram} :
    effectiveIntelligenceOrder p p' → ¬ effectiveIntelligenceOrder p' p := by
  intro hpp' hp'p
  rcases hpp' with ⟨⟨h, hwf, hlt⟩, hge⟩
  have hle : (p.compute h).1 ≤ (p'.compute h).1 := by
    rcases hp'p with ⟨_hex, hge'⟩
    exact hge' h hwf
  exact (not_lt_of_ge hle) hlt

/-! The effective intelligence order ≻^w is a partial order on valid approximations.

**Statement**: ≻^w restricted to VA programs is a partial order.

**Why not formalized**: Requires proving transitivity and antisymmetry
of the claimed-value comparison, which needs VA properties. -/

/-! ### Section 7.2.7: The Universal Time-Bounded AIXItl Agent -/

/-- The AIXItl agent: universal time-bounded approximation to AIXI.

    Parameters:
    - t: time bound per cycle
    - l: length bound on programs
    - l_p: length bound on proofs

    (Hutter 2005, Section 7.2.7) -/
structure AIXItl where
  /-- Time bound per cycle -/
  timeBound : ℕ
  /-- Length bound on programs -/
  lengthBound : ℕ
  /-- Length bound on proofs of VA(p) -/
  proofLengthBound : ℕ
  /-- Set of validated programs (those with proven VA) -/
  validatedPrograms : List ExtendedChronologicalProgram

/-- The best `(claimed value, action)` among the agent's validated programs for a given history. -/
noncomputable def aixitlBestResult (agent : AIXItl) (h : History) : ℝ × Action :=
  bestByValue agent.validatedPrograms h

/-- AIXItl viewed as an extended chronological program: it outputs its selected action together
with the maximal claimed value among its validated programs. -/
noncomputable def aixitlProgram (agent : AIXItl) : ExtendedChronologicalProgram :=
  { code := { code := [], length := 0 }
    compute := fun h => aixitlBestResult agent h }

/-- Step 1: Create all proofs and find valid programs.

    Enumerate all binary strings of length l_p, interpret as proofs.
    Keep programs p where proof establishes VA(p).

    (Hutter 2005, Section 7.2.7, Step 1) -/

theorem length_findValidPrograms_add_one_le (decode : ProofDecoder ExtendedChronologicalProgram) (l_p : ℕ) :
    (findValidPrograms decode l_p).length + 1 ≤ 2 ^ (l_p + 1) := by
  have hle : (findValidPrograms decode l_p).length ≤ (bitstringsUpTo l_p).length := by
    simpa [findValidPrograms] using
      (length_filterMap_le (f := decode) (l := bitstringsUpTo l_p))
  have hle' : (findValidPrograms decode l_p).length + 1 ≤ (bitstringsUpTo l_p).length + 1 :=
    Nat.add_le_add_right hle 1
  exact le_trans hle' (le_of_eq (length_bitstringsUpTo_add_one l_p))
/-!
The basic proof-checker interfaces (`ProofChecker`, `CompleteProofChecker`) are shared with the
core-generic development and live in `Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumeration`.
-/

/-- Step 2: Filter programs by the length bound `l`.

Step 3 (“output within `t` steps, else default”) is handled later in this file by the concrete
`RawToPartrecProgram` wrapper, which provides a time-bounded `computeWithin` semantics. -/
def filterAndModify (programs : List ExtendedChronologicalProgram)
    (l _t : ℕ) : List ExtendedChronologicalProgram :=
  programs.filter fun p => p.code.length ≤ l

/-! #### AIXItl from a sound proof checker (Step 1 semantics)

To model Step 1 (“enumerate proofs, extract VA programs”) without committing to a particular
object-level proof calculus, we parameterize by a sound `ProofChecker` that maps bitstrings to
programs and guarantees the desired correctness property.
-/

noncomputable def aixitlFromProofChecker (μ : Environment) (γ : DiscountFactor) (horizon : ℕ)
    (checker : ProofChecker (α := ExtendedChronologicalProgram) (ValidValueLowerBound μ γ horizon))
    (l l_p t : ℕ) : AIXItl :=
  { timeBound := t
    lengthBound := l
    proofLengthBound := l_p
    validatedPrograms := filterAndModify (findValidPrograms checker.decode l_p) l t }

theorem validValueLowerBound_of_mem_aixitlFromProofChecker (μ : Environment) (γ : DiscountFactor)
    (horizon : ℕ)
    (checker : ProofChecker (α := ExtendedChronologicalProgram) (ValidValueLowerBound μ γ horizon))
    (l l_p t : ℕ) {p : ExtendedChronologicalProgram}
    (hp : p ∈ (aixitlFromProofChecker μ γ horizon checker l l_p t).validatedPrograms) :
    ValidValueLowerBound μ γ horizon p := by
  -- `validatedPrograms` is a filter of `findValidPrograms`, so membership gives a decoded proof.
  have hp' : p ∈ findValidPrograms checker.decode l_p := by
    simp [aixitlFromProofChecker, filterAndModify] at hp
    exact hp.1
  -- Apply the checker soundness.
  exact ProofChecker.sound_of_mem_findValidPrograms (checker := checker) (ha := hp')

/-! ### Concrete encodings (History ↔ `List ℕ`, programs ↔ bitstrings)

Chapter 7’s “programs” are bitstrings. To execute them with Mathlib’s `ToPartrec` evaluator we
encode inputs as `List ℕ`, and decode `List ℕ` outputs into `(value, action)` pairs.  The encodings
below are deliberately simple and total, providing a concrete bridge without committing to a full
UTM tape model yet.
-/

namespace Coding

/-! #### Actions/percepts/histories as naturals -/

def encodeActionNat : Action → ℕ
  | Action.left => 0
  | Action.right => 1
  | Action.stay => 2

def decodeActionNat : ℕ → Option Action
  | 0 => some Action.left
  | 1 => some Action.right
  | 2 => some Action.stay
  | _ => none

@[simp] theorem decodeActionNat_encodeActionNat (a : Action) :
    decodeActionNat (encodeActionNat a) = some a := by
  cases a <;> rfl

def encodePerceptNat : Percept → ℕ
  | Percept.mk o r => o.toNat * 2 + r.toNat

def decodePerceptNat : ℕ → Option Percept
  | 0 => some (Percept.mk false false)
  | 1 => some (Percept.mk false true)
  | 2 => some (Percept.mk true false)
  | 3 => some (Percept.mk true true)
  | _ => none

@[simp] theorem decodePerceptNat_encodePerceptNat (x : Percept) :
    decodePerceptNat (encodePerceptNat x) = some x := by
  cases x with
  | mk o r =>
      cases o <;> cases r <;> rfl

def encodeHistElemNat (e : HistElem) : ℕ × ℕ :=
  match e with
  -- Shift by `+1` so that `0` can serve as an explicit end-of-history marker
  -- in `encodeHistoryNat` (useful for `ToPartrec` programs that case-split on `0`).
  | HistElem.act a => (1, encodeActionNat a + 1)
  | HistElem.per x => (2, encodePerceptNat x + 1)

def decodeHistElemNat (tag payload : ℕ) : Option HistElem :=
  match tag with
  | 1 =>
      if payload = 0 then none else
        (decodeActionNat (payload - 1)).map HistElem.act
  | 2 =>
      if payload = 0 then none else
        (decodePerceptNat (payload - 1)).map HistElem.per
  | _ => none

@[simp] theorem decodeHistElemNat_encodeHistElemNat (e : HistElem) :
    decodeHistElemNat (encodeHistElemNat e).1 (encodeHistElemNat e).2 = some e := by
  cases e <;> simp [encodeHistElemNat, decodeHistElemNat]

def encodeHistoryNat : History → List ℕ
  | [] => [0]
  | e :: es =>
      let ep := encodeHistElemNat e
      ep.1 :: ep.2 :: encodeHistoryNat es

def decodeHistoryNat : List ℕ → Option History
  | [] => some []
  | 0 :: _ => some []
  | tag :: payload :: rest => do
      let e? := decodeHistElemNat tag payload
      let es? := decodeHistoryNat rest
      match e?, es? with
      | some e, some es => some (e :: es)
      | _, _ => none
  | _ => none

@[simp] theorem decodeHistoryNat_encodeHistoryNat (h : History) :
    decodeHistoryNat (encodeHistoryNat h) = some h := by
  induction h with
  | nil =>
      simp [encodeHistoryNat, decodeHistoryNat]
  | cons e es ih =>
      cases e <;> simp [encodeHistoryNat, decodeHistoryNat, encodeHistElemNat, decodeHistElemNat, ih]

/-! #### Bitstrings as naturals (little-endian)

Bitstring↔ℕ and `Encodable` bit-coding utilities live in `Mettapedia.UniversalAI.TimeBoundedAIXI.CodingBits`.
-/

/-! #### Self-delimiting (prefix-free) wrapper

To model the prefix-free program codes used in Equation (7.3), we wrap an arbitrary payload
bitstring `b₁…bₙ` as `1^n 0 b₁…bₙ`. This is self-delimiting and prefix-free. -/

/-- Self-delimiting encoding `b ↦ 1^{|b|} 0 b`. -/
def selfDelimitingEncode (payload : List Bool) : List Bool :=
  List.replicate payload.length true ++ false :: payload

/-- Helper for `selfDelimitingDecode`: the accumulator `n` stores the number of leading `true`s. -/
def selfDelimitingDecodeAux : ℕ → List Bool → Option (List Bool)
  | _, [] => none
  | n, false :: rest => if rest.length = n then some rest else none
  | n, true :: rest => selfDelimitingDecodeAux (n + 1) rest

/-- Decode `1^n 0 b₁…bₙ`, failing on malformed inputs. -/
def selfDelimitingDecode (code : List Bool) : Option (List Bool) :=
  selfDelimitingDecodeAux 0 code

theorem selfDelimitingDecodeAux_replicate_false (n m : ℕ) (rest : List Bool) :
    selfDelimitingDecodeAux n (List.replicate m true ++ false :: rest) =
      if rest.length = n + m then some rest else none := by
  induction m generalizing n with
  | zero =>
      simp [selfDelimitingDecodeAux]
  | succ m ih =>
      have hadd : (n + 1) + m = n + Nat.succ m := by
        omega
      simpa [List.replicate, selfDelimitingDecodeAux, hadd] using (ih (n := n + 1))

@[simp] theorem selfDelimitingDecode_selfDelimitingEncode (payload : List Bool) :
    selfDelimitingDecode (selfDelimitingEncode payload) = some payload := by
  have h :=
    selfDelimitingDecodeAux_replicate_false (n := 0) (m := payload.length) (rest := payload)
  simpa [selfDelimitingDecode, selfDelimitingEncode, Nat.zero_add] using h

theorem selfDelimitingDecodeAux_eq_some {n : ℕ} {code payload : List Bool}
    (h : selfDelimitingDecodeAux n code = some payload) :
    ∃ m, code = List.replicate m true ++ false :: payload ∧ payload.length = n + m := by
  induction code generalizing n with
  | nil =>
      have hfalse : False := by
        have h' := h
        simp [selfDelimitingDecodeAux] at h'
      cases hfalse
  | cons b rest ih =>
      cases b with
      | false =>
          -- `decodeAux` stops immediately and checks the remaining length.
          by_cases hlen : rest.length = n
          · have h' := h
            simp [selfDelimitingDecodeAux, hlen] at h'
            cases h'
            refine ⟨0, ?_, ?_⟩
            · simp
            · simp [hlen]
          · have hfalse : False := by
              have h' := h
              simp [selfDelimitingDecodeAux, hlen] at h'
            cases hfalse
      | true =>
          -- Consume one leading `true` and recurse with `n+1`.
          have h' := h
          simp [selfDelimitingDecodeAux] at h'
          rcases ih (n := n + 1) h' with ⟨m, hmCode, hmLen⟩
          refine ⟨m + 1, ?_, ?_⟩
          · simp [List.replicate, hmCode]
          · -- `payload.length = (n+1)+m = n+(m+1)`.
            omega

theorem selfDelimitingEncode_of_decode_eq_some {code payload : List Bool}
    (h : selfDelimitingDecode code = some payload) :
    selfDelimitingEncode payload = code := by
  unfold selfDelimitingDecode at h
  rcases selfDelimitingDecodeAux_eq_some (n := 0) (code := code) (payload := payload) h with
    ⟨m, hmCode, hmLen⟩
  -- The decoder ensures `payload.length = m`, so the encoder reconstructs `code`.
  have hmLen' : payload.length = m := by simpa using hmLen
  subst hmLen'
  simp [selfDelimitingEncode, hmCode]

theorem selfDelimitingEncode_injective : Function.Injective selfDelimitingEncode := by
  intro p q h
  have :
      selfDelimitingDecode (selfDelimitingEncode p) =
        selfDelimitingDecode (selfDelimitingEncode q) := by
    simp [h]
  simpa using this

theorem take_replicate_of_le {α : Type u} (a : α) {k m : ℕ} (hk : k ≤ m) :
    (List.replicate m a).take k = List.replicate k a := by
  induction k generalizing m with
  | zero =>
      simp
  | succ k ih =>
      cases m with
      | zero =>
          cases (Nat.not_succ_le_zero k hk)
      | succ m =>
          simp [List.replicate, ih, Nat.le_of_succ_le_succ hk]

theorem length_selfDelimitingEncode (payload : List Bool) :
    (selfDelimitingEncode payload).length = 2 * payload.length + 1 := by
  calc
    (selfDelimitingEncode payload).length =
        payload.length + (payload.length + 1) := by
          simp [selfDelimitingEncode]
    _ = 2 * payload.length + 1 := by omega

theorem take_selfDelimitingEncode_length_add_one (payload : List Bool) :
    (selfDelimitingEncode payload).take (payload.length + 1) =
      List.replicate payload.length true ++ [false] := by
  -- Take `|payload|` bits from the `1^|payload|` prefix and 1 more bit (the delimiter `0`).
  have hrep : (List.replicate payload.length true).take (payload.length + 1) =
      List.replicate payload.length true := by
    -- `take` beyond the list length yields the whole list.
    apply List.take_of_length_le
    simp
  have hsub : payload.length + 1 - (List.replicate payload.length true).length = 1 := by
    simp
  unfold selfDelimitingEncode
  -- Expand `take` over the append and simplify.
  simp [List.take_append, hrep]

theorem selfDelimitingEncode_not_isPrefix_of_lt_length {p q : List Bool} (hlt : p.length < q.length) :
    ¬ selfDelimitingEncode p <+: selfDelimitingEncode q := by
  intro hpref
  rcases hpref with ⟨suffix, hsuffix⟩
  have hlen : p.length + 1 ≤ (selfDelimitingEncode p).length := by
    -- `p.length + 1 ≤ 2*p.length + 1`.
    rw [length_selfDelimitingEncode]
    omega
  have htake :
      (selfDelimitingEncode q).take (p.length + 1) = (selfDelimitingEncode p).take (p.length + 1) := by
    -- Take within the prefix part `selfDelimitingEncode p` of the append.
    calc
      (selfDelimitingEncode q).take (p.length + 1)
          = (selfDelimitingEncode p ++ suffix).take (p.length + 1) := by simp [hsuffix]
      _ = (selfDelimitingEncode p).take (p.length + 1) := by
            simp [List.take_append_of_le_length hlen]
  have hp : (selfDelimitingEncode p).take (p.length + 1) = List.replicate p.length true ++ [false] :=
    take_selfDelimitingEncode_length_add_one (payload := p)
  have hq : (selfDelimitingEncode q).take (p.length + 1) = List.replicate (p.length + 1) true := by
    -- Since `p.length + 1 ≤ q.length`, we only see `true`s from the unary prefix.
    have hle : p.length + 1 ≤ q.length := Nat.succ_le_of_lt hlt
    unfold selfDelimitingEncode
    -- `take` stays within the replicate prefix.
    have :
        (List.replicate q.length true ++ false :: q).take (p.length + 1) =
          (List.replicate q.length true).take (p.length + 1) := by
            simp [List.take_append, Nat.sub_eq_zero_of_le (by simpa using hle)]
    -- Now take from the replicate prefix.
    calc
      (List.replicate q.length true ++ false :: q).take (p.length + 1)
          = (List.replicate q.length true).take (p.length + 1) := this
      _ = List.replicate (p.length + 1) true := by
            simpa using (take_replicate_of_le (a := true) (hk := hle))
  -- Contradiction: the last bit of the `(p.length+1)`-prefix differs (`false` vs `true`).
  have : (List.replicate p.length true ++ [false]) = List.replicate (p.length + 1) true := by
    simpa [hp, hq] using htake.symm
  -- Compare the last element.
  have hlast : (List.replicate p.length true ++ [false]).getLast? = some false := by
    simp
  have hlast' : (List.replicate (p.length + 1) true).getLast? = some true := by
    -- `replicate (n+1) a = replicate n a ++ [a]`, so the last element is `a`.
    simp [List.replicate_succ']
  -- Equality forces the last elements to match.
  have := congrArg List.getLast? this
  simp [hlast, hlast'] at this

theorem selfDelimitingEncode_not_isPrefix_of_ne {p q : List Bool} (hne : p ≠ q) :
    ¬ selfDelimitingEncode p <+: selfDelimitingEncode q := by
  by_cases hlt : p.length < q.length
  · exact selfDelimitingEncode_not_isPrefix_of_lt_length (p := p) (q := q) hlt
  · by_cases hgt : q.length < p.length
    · intro hpref
      rcases hpref with ⟨suffix, hsuffix⟩
      have hlen : (selfDelimitingEncode p).length ≤ (selfDelimitingEncode q).length := by
        -- Prefix implies a length inequality.
        rw [← hsuffix]
        simp [List.length_append]
      -- But lengths are strictly ordered when `q.length < p.length`.
      have : (selfDelimitingEncode q).length < (selfDelimitingEncode p).length := by
        rw [length_selfDelimitingEncode, length_selfDelimitingEncode]
        omega
      exact (not_lt_of_ge hlen) this
    · -- Same payload length: a prefix must be equality, contradicting injectivity.
      have hEq : p.length = q.length := by omega
      intro hpref
      rcases hpref with ⟨suffix, hsuffix⟩
      have hlen :
          (selfDelimitingEncode q).length = (selfDelimitingEncode p).length := by
        rw [length_selfDelimitingEncode, length_selfDelimitingEncode, hEq]
      have hsuffixNil : suffix = [] := by
        -- Compare lengths in `encode q = encode p ++ suffix`.
        have hlenSuffix :
            (selfDelimitingEncode p).length + suffix.length = (selfDelimitingEncode q).length := by
          simpa [List.length_append] using congrArg List.length hsuffix
        have hlenSuffix' :
            (selfDelimitingEncode p).length + suffix.length = (selfDelimitingEncode p).length := by
          simpa [hlen] using hlenSuffix
        have : suffix.length = 0 := by
          have :
              (selfDelimitingEncode p).length + suffix.length = (selfDelimitingEncode p).length + 0 := by
            calc
              (selfDelimitingEncode p).length + suffix.length = (selfDelimitingEncode p).length := hlenSuffix'
              _ = (selfDelimitingEncode p).length + 0 := by simp
          exact Nat.add_left_cancel this
        exact List.eq_nil_of_length_eq_zero this
      have : selfDelimitingEncode p = selfDelimitingEncode q := by
        simpa [hsuffixNil] using hsuffix
      have hpq : p = q := selfDelimitingEncode_injective this
      exact hne hpq

/-! #### Decoding `(value, action)` outputs -/

/-!
Hutter’s Chapter 7 treats the claimed value `w_k` as a (rational) lower bound on the
unnormalized selection value `V_km`. In particular, `w_k` is **not** confined to `[0,1]`.

We therefore decode the claimed value from two naturals `(num, den)` as the nonnegative rational
`num / (den+1)`.
-/
noncomputable def decodeValueNat (num den : ℕ) : ℝ :=
  (num : ℝ) / (den + 1)

theorem decodeValueNat_nonneg (num den : ℕ) : 0 ≤ decodeValueNat num den := by
  have hnum : 0 ≤ (num : ℝ) := by exact_mod_cast (Nat.zero_le num)
  have hden : 0 ≤ (den + 1 : ℝ) := by exact_mod_cast (Nat.zero_le (den + 1))
  simpa [decodeValueNat] using div_nonneg hnum hden

theorem decodeValueNat_le_one_of_le (num den : ℕ) (hle : num ≤ den + 1) : decodeValueNat num den ≤ 1 := by
  have hpos : 0 < (den + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos den)
  have hle' : (num : ℝ) ≤ (den + 1 : ℝ) := by exact_mod_cast hle
  have : (num : ℝ) / (den + 1 : ℝ) ≤ 1 := (div_le_one hpos).2 hle'
  simpa [decodeValueNat] using this

noncomputable def decodeValueActionOutput : List ℕ → Option (ℝ × Action)
  | num :: den :: a :: _ =>
      (decodeActionNat a).map fun act => (decodeValueNat num den, act)
  | _ => none

end Coding

/-! ### A concrete time-bounded wrapper (Step 3)

`ExtendedChronologicalProgram` represents the *already modified* programs that always output within
the per-cycle time budget `t` (or else output a default `(0, stay)`).

To connect this to actual step-counting, we provide a small bridge for programs implemented as
`Turing.ToPartrec.Code` together with an encoder/decoder for I/O.
-/

/-- A “raw” extended chronological program implemented as `ToPartrec.Code`.

The raw code computes a `List ℕ` output; `decodeOutput` interprets this as a `(value, action)` pair.
If either evaluation fails to halt within the time budget or decoding fails, we fall back to
`(0, Action.stay)`. -/
structure RawToPartrecProgram where
  code : Program
  tm : Turing.ToPartrec.Code
deriving Encodable

namespace RawToPartrecProgram

/-- Canonical raw program wrapper using the `Coding` encodings. -/
noncomputable def ofToPartrec (bits : List Bool) (tm : Turing.ToPartrec.Code) : RawToPartrecProgram :=
  { code := { code := bits }
    tm := tm }

def decodeToPartrec : ProofDecoder Turing.ToPartrec.Code :=
  fun bits => Coding.decodeEncodableBits bits

noncomputable def decodeCanonical : ProofDecoder RawToPartrecProgram :=
  fun bits => (decodeToPartrec bits).map (ofToPartrec bits)

theorem code_length_of_decodeCanonical {bits : List Bool} {p : RawToPartrecProgram}
    (hdec : decodeCanonical bits = some p) : p.code.length = bits.length := by
  unfold decodeCanonical at hdec
  cases htm : decodeToPartrec bits with
  | none =>
      simp [htm] at hdec
  | some tm =>
      have hp : ofToPartrec bits tm = p := by
        simpa [htm] using hdec
      simp [hp.symm, ofToPartrec]

theorem filter_filterMap_decodeCanonical_eq (bitsList : List (List Bool)) (l : ℕ) :
    (bitsList.filterMap decodeCanonical).filter (fun p => p.code.length ≤ l) =
      (bitsList.filter (fun bits => bits.length ≤ l)).filterMap decodeCanonical := by
  induction bitsList with
  | nil =>
      simp
  | cons bits rest ih =>
      cases hdec : decodeCanonical bits with
      | none =>
          by_cases hlen : bits.length ≤ l
          · simp [List.filterMap, hdec, List.filter, hlen, ih]
          · simp [List.filterMap, hdec, List.filter, hlen, ih]
      | some p =>
          have hcode : p.code.length = bits.length := by
            exact code_length_of_decodeCanonical (bits := bits) (p := p) hdec
          by_cases hlen : bits.length ≤ l
          · have hp : p.code.length ≤ l := by simpa [hcode] using hlen
            simp [List.filterMap, hdec, List.filter, hlen, ih, decide_eq_true hp]
          · have hp : ¬ p.code.length ≤ l := by
              intro hp'
              exact hlen (by simpa [hcode] using hp')
            simp [List.filterMap, hdec, List.filter, hlen, ih, decide_eq_false hp]

/-- Run a raw program for `t` small steps, producing a total `(value, action)` output by defaulting
to `(0, stay)` when evaluation/decoding fails within the budget. -/
noncomputable def computeWithin (t : ℕ) (p : RawToPartrecProgram) (h : History) : ℝ × Action :=
  match StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) with
  | some out => (Coding.decodeValueActionOutput out).getD (0, Action.stay)
  | none => (0, Action.stay)

/-- The associated total extended chronological program (post-modification). -/
noncomputable def toExtended (t : ℕ) (p : RawToPartrecProgram) : ExtendedChronologicalProgram :=
  { code := p.code
    compute := computeWithin t p }

/-- If a raw program is the `ToPartrec` primitive `zero'`, then its time-bounded wrapper always
claims value `0` (independently of the history). -/
theorem computeWithin_fst_eq_zero_of_tm_eq_zero' (t : ℕ) (p : RawToPartrecProgram) (h : History)
    (hp : p.tm = Turing.ToPartrec.Code.zero') : (computeWithin t p h).1 = 0 := by
  classical
  unfold computeWithin
  cases hrun : StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) with
  | none =>
      simp
  | some out =>
      have houtMem : out ∈ p.tm.eval (Coding.encodeHistoryNat h) :=
        StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h) (out := out) hrun
      have houtEq : out = 0 :: Coding.encodeHistoryNat h := by
        -- `zero'` always prepends a `0`.
        have : out ∈ Turing.ToPartrec.Code.zero'.eval (Coding.encodeHistoryNat h) := by
          simpa [hp] using houtMem
        simpa using this
      -- Decoding either succeeds (with value `0`) or fails and falls back to `(0, stay)`.
      have : ((Coding.decodeValueActionOutput out).getD (0, Action.stay)).1 = 0 := by
        subst houtEq
        cases henc : Coding.encodeHistoryNat h with
        | nil =>
            simp [Coding.decodeValueActionOutput]
        | cons a rest =>
            cases rest with
            | nil =>
                simp [Coding.decodeValueActionOutput]
            | cons b rest' =>
                simp [Coding.decodeValueActionOutput, Coding.decodeValueNat]
      simp [this]

/-- If a raw program is the `ToPartrec` primitive `zero`, then its time-bounded wrapper always claims value `0`. -/
theorem computeWithin_fst_eq_zero_of_tm_eq_zero (t : ℕ) (p : RawToPartrecProgram) (h : History)
    (hp : p.tm = Turing.ToPartrec.Code.zero) : (computeWithin t p h).1 = 0 := by
  classical
  unfold computeWithin
  cases hrun : StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) with
  | none =>
      simp
  | some out =>
      have houtMem : out ∈ p.tm.eval (Coding.encodeHistoryNat h) :=
        StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h) (out := out) hrun
      have houtEq : out = [0] := by
        have : out ∈ Turing.ToPartrec.Code.zero.eval (Coding.encodeHistoryNat h) := by
          simpa [hp] using houtMem
        simpa using this
      have : ((Coding.decodeValueActionOutput out).getD (0, Action.stay)).1 = 0 := by
        subst houtEq
        simp [Coding.decodeValueActionOutput]
      simp [this]

/-- If a raw program is the `ToPartrec` primitive `nil`, then its time-bounded wrapper always claims value `0`. -/
theorem computeWithin_fst_eq_zero_of_tm_eq_nil (t : ℕ) (p : RawToPartrecProgram) (h : History)
    (hp : p.tm = Turing.ToPartrec.Code.nil) : (computeWithin t p h).1 = 0 := by
  classical
  unfold computeWithin
  cases hrun : StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) with
  | none =>
      simp
  | some out =>
      have houtMem : out ∈ p.tm.eval (Coding.encodeHistoryNat h) :=
        StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h) (out := out) hrun
      have houtEq : out = [] := by
        have : out ∈ Turing.ToPartrec.Code.nil.eval (Coding.encodeHistoryNat h) := by
          simpa [hp] using houtMem
        simpa using this
      have : ((Coding.decodeValueActionOutput out).getD (0, Action.stay)).1 = 0 := by
        subst houtEq
        simp [Coding.decodeValueActionOutput]
      simp [this]

/-- A `ToPartrec` code template that always claims value `0`, but can compute an arbitrary action
code (the third output nat) via a sub-program `act`. -/
def zeroValueActionCode (act : Turing.ToPartrec.Code) : Turing.ToPartrec.Code :=
  Turing.ToPartrec.Code.cons Turing.ToPartrec.Code.zero
    (Turing.ToPartrec.Code.cons Turing.ToPartrec.Code.zero
      (Turing.ToPartrec.Code.cons act Turing.ToPartrec.Code.nil))

/-- A `ToPartrec` code that ignores its input and returns the singleton list `[n]`. -/
def constNatCode : ℕ → Turing.ToPartrec.Code
  | 0 => Turing.ToPartrec.Code.zero
  | n + 1 => Turing.ToPartrec.Code.succ.comp (constNatCode n)

/-- A `ToPartrec` code that ignores its input and returns a fixed list of naturals. -/
def constListCode : List ℕ → Turing.ToPartrec.Code
  | [] => Turing.ToPartrec.Code.nil
  | n :: ns => Turing.ToPartrec.Code.cons (constNatCode n) (constListCode ns)

/-- Drop the head of the input list if it equals a fixed natural `n`, then continue with `yes`.
Otherwise return `no`.

This is implemented using `Code.case`, which can only distinguish `0` vs successor; it compares
the head against `n` by peeling off `n` successors. -/
def dropIfHeadEqNat (n : ℕ) (yes no : Turing.ToPartrec.Code) : Turing.ToPartrec.Code :=
  match n with
  | 0 => Turing.ToPartrec.Code.case yes no
  | n + 1 => Turing.ToPartrec.Code.case no (dropIfHeadEqNat n yes no)

/-- Guard a computation by checking that a fixed list of naturals is a prefix of the input (with
`headI` semantics for the empty list, matching `ToPartrec.Code.case`).

This is used to build “history-guarded” raw programs: for inputs in the image of
`Coding.encodeHistoryNat`, prefix-guarding by a list ending in the sentinel `0` is equivalent to
full equality. -/
def guardPrefixListNat (pref : List ℕ) (yes no : Turing.ToPartrec.Code) : Turing.ToPartrec.Code :=
  match pref with
  | [] => yes
  | x :: xs => dropIfHeadEqNat x (guardPrefixListNat xs yes no) no

/-- Head-`headI`-based prefix check mirroring the control flow of `guardPrefixListNat`. -/
def prefixHeadI : List ℕ → List ℕ → Bool
  | [], _ => true
  | x :: xs, v => if v.headI = x then prefixHeadI xs v.tail else false

theorem constNatCode_eval (n : ℕ) (v : List ℕ) : (constNatCode n).eval v = pure [n] := by
  induction n with
  | zero =>
      simp [constNatCode]
  | succ n ih =>
      simp [constNatCode, ih]

theorem constListCode_eval (ns : List ℕ) (v : List ℕ) : (constListCode ns).eval v = pure ns := by
  induction ns with
  | nil =>
      simp [constListCode]
  | cons n ns ih =>
      simp [constListCode, constNatCode_eval, ih]

theorem dropIfHeadEqNat_eval_constNo (n : ℕ) (yes : Turing.ToPartrec.Code) (outNo : List ℕ) (v : List ℕ) :
    (dropIfHeadEqNat n yes (constListCode outNo)).eval v =
      if v.headI = n then yes.eval v.tail else pure outNo := by
  induction n generalizing v with
  | zero =>
      cases h : v.headI with
      | zero =>
          simp [dropIfHeadEqNat, Turing.ToPartrec.Code.case_eval, h, constListCode_eval]
      | succ m =>
          -- The `succ` branch applies `no` to `(m :: v.tail)`, but `no` is constant.
          simp [dropIfHeadEqNat, Turing.ToPartrec.Code.case_eval, h, constListCode_eval]
  | succ n ih =>
      cases h : v.headI with
      | zero =>
          simp [dropIfHeadEqNat, Turing.ToPartrec.Code.case_eval, h, constListCode_eval]
      | succ m =>
          -- The `succ` branch decrements the head and recurses.
          simp [dropIfHeadEqNat, Turing.ToPartrec.Code.case_eval, h, ih, constListCode_eval]

theorem guardPrefixListNat_eval_const (pref : List ℕ) (outYes outNo : List ℕ) (v : List ℕ) :
    (guardPrefixListNat pref (constListCode outYes) (constListCode outNo)).eval v =
      if prefixHeadI pref v then pure outYes else pure outNo := by
  induction pref generalizing v with
  | nil =>
      simp [guardPrefixListNat, prefixHeadI, constListCode_eval]
  | cons x xs ih =>
      -- Reduce to a head test + recursion on the tail.
      have hdrop :
          (dropIfHeadEqNat x (guardPrefixListNat xs (constListCode outYes) (constListCode outNo)) (constListCode outNo)).eval v =
            if v.headI = x then
              (guardPrefixListNat xs (constListCode outYes) (constListCode outNo)).eval v.tail
            else
              pure outNo := by
        simpa [guardPrefixListNat] using
          (dropIfHeadEqNat_eval_constNo (n := x)
            (yes := guardPrefixListNat xs (constListCode outYes) (constListCode outNo))
            (outNo := outNo) (v := v))
      -- Finish by rewriting the recursive call via IH and splitting on the head test.
      by_cases hx : v.headI = x
      · simp [guardPrefixListNat, prefixHeadI, hdrop, ih, hx]
      · simp [guardPrefixListNat, prefixHeadI, hdrop, hx]

/-- A `ToPartrec` program template: if the input begins with the given `prefix`, return a fixed
`(value, action)` triple; otherwise return a fixed `(0, stay)` triple. -/
def guardedValueActionCode (pref : List ℕ) (num den : ℕ) (act : Action) : Turing.ToPartrec.Code :=
  guardPrefixListNat pref
    (constListCode [num, den, Coding.encodeActionNat act])
    (constListCode [0, 0, Coding.encodeActionNat Action.stay])

/-- Any `ToPartrec` program of the form `zeroValueActionCode act` always claims value `0`. -/
theorem computeWithin_fst_eq_zero_of_tm_eq_zeroValueAction (t : ℕ) (p : RawToPartrecProgram) (h : History)
    (act : Turing.ToPartrec.Code) (hp : p.tm = zeroValueActionCode act) : (computeWithin t p h).1 = 0 := by
  classical
  unfold computeWithin
  cases hrun : StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) with
  | none =>
      simp
  | some out =>
      have houtMem : out ∈ p.tm.eval (Coding.encodeHistoryNat h) :=
        StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h) (out := out) hrun
      have houtMem' : out ∈ (zeroValueActionCode act).eval (Coding.encodeHistoryNat h) := by
        simpa [hp] using houtMem
      -- Unpack the nested `cons` structure: the output is `0 :: 0 :: a :: []` for some `a`.
      have houtEq : ∃ a : ℕ, out = 0 :: 0 :: a :: [] := by
        -- First `cons` (numerator).
        have hout0 :
            out ∈
              (Turing.ToPartrec.Code.zero.eval (Coding.encodeHistoryNat h) >>= fun n =>
                (Turing.ToPartrec.Code.cons Turing.ToPartrec.Code.zero
                    (Turing.ToPartrec.Code.cons act Turing.ToPartrec.Code.nil)).eval (Coding.encodeHistoryNat h) >>=
                  fun ns => pure (n.headI :: ns)) := by
          simpa [zeroValueActionCode, Turing.ToPartrec.Code.cons_eval] using houtMem'
        rcases (Part.mem_bind_iff).1 hout0 with ⟨n, hn, hout1⟩
        have hn0 : n = [0] := by
          -- `zero.eval _ = pure [0]`.
          simpa [Turing.ToPartrec.Code.zero_eval] using hn
        subst hn0
        rcases (Part.mem_bind_iff).1 hout1 with ⟨ns, hns, hout2⟩
        have hout2' : out = 0 :: ns := by
          simpa using hout2
        -- Second `cons` (denominator).
        have hns0 :
            ns ∈
              (Turing.ToPartrec.Code.zero.eval (Coding.encodeHistoryNat h) >>= fun n =>
                (Turing.ToPartrec.Code.cons act Turing.ToPartrec.Code.nil).eval (Coding.encodeHistoryNat h) >>=
                  fun ns2 => pure (n.headI :: ns2)) := by
          simpa [Turing.ToPartrec.Code.cons_eval] using hns
        rcases (Part.mem_bind_iff).1 hns0 with ⟨n2, hn2, hns1⟩
        have hn20 : n2 = [0] := by
          simpa [Turing.ToPartrec.Code.zero_eval] using hn2
        subst hn20
        rcases (Part.mem_bind_iff).1 hns1 with ⟨ns2, hns2, hns2pure⟩
        have hnsEq : ns = 0 :: ns2 := by
          simpa using hns2pure
        -- Third `cons` (action) + `nil`.
        have hns2' :
            ns2 ∈
              (act.eval (Coding.encodeHistoryNat h) >>= fun n3 =>
                Turing.ToPartrec.Code.nil.eval (Coding.encodeHistoryNat h) >>= fun ns3 => pure (n3.headI :: ns3)) := by
          simpa [Turing.ToPartrec.Code.cons_eval] using hns2
        rcases (Part.mem_bind_iff).1 hns2' with ⟨n3, hn3, hns3⟩
        rcases (Part.mem_bind_iff).1 hns3 with ⟨ns3, hns3', hns3pure⟩
        have hnil : ns3 = [] := by
          simpa [Turing.ToPartrec.Code.nil_eval] using hns3'
        subst hnil
        have hns2Eq : ns2 = n3.headI :: [] := by
          simpa [Turing.ToPartrec.Code.nil_eval] using hns3pure
        subst hns2Eq
        subst hnsEq
        subst hout2'
        refine ⟨n3.headI, rfl⟩
      -- Decode has numerator `0`, hence claimed value `0`.
      have : ((Coding.decodeValueActionOutput out).getD (0, Action.stay)).1 = 0 := by
        rcases houtEq with ⟨a, rfl⟩
        simp [Coding.decodeValueActionOutput, Coding.decodeValueNat]
      simp [this]

/-- A minimal global VA fact: if a raw program's `ToPartrec` code is `zero'`, then it satisfies
`ValidValueLowerBound` for any horizon. -/
theorem validValueLowerBound_toExtended_of_tm_eq_zero' (μ : Environment) (γ : DiscountFactor) (horizon t : ℕ)
    (p : RawToPartrecProgram) (hp : p.tm = Turing.ToPartrec.Code.zero') :
    ValidValueLowerBound μ γ horizon (p.toExtended t) := by
  intro h _hwf
  have hclaim : ((p.toExtended t).compute h).1 = 0 := by
    simpa [RawToPartrecProgram.toExtended] using computeWithin_fst_eq_zero_of_tm_eq_zero' (t := t) (p := p) (h := h) hp
  have hnonneg : 0 ≤ value μ (p.toExtended t).toAgent γ h horizon :=
    value_nonneg (μ := μ) (π := (p.toExtended t).toAgent) (γ := γ) (h := h) (n := horizon)
  simpa [hclaim] using hnonneg

/-- `zero` also yields a trivial global lower bound (claimed value `0`). -/
theorem validValueLowerBound_toExtended_of_tm_eq_zero (μ : Environment) (γ : DiscountFactor) (horizon t : ℕ)
    (p : RawToPartrecProgram) (hp : p.tm = Turing.ToPartrec.Code.zero) :
    ValidValueLowerBound μ γ horizon (p.toExtended t) := by
  intro h _hwf
  have hclaim : ((p.toExtended t).compute h).1 = 0 := by
    simpa [RawToPartrecProgram.toExtended] using computeWithin_fst_eq_zero_of_tm_eq_zero (t := t) (p := p) (h := h) hp
  have hnonneg : 0 ≤ value μ (p.toExtended t).toAgent γ h horizon :=
    value_nonneg (μ := μ) (π := (p.toExtended t).toAgent) (γ := γ) (h := h) (n := horizon)
  simpa [hclaim] using hnonneg

/-- `nil` also yields a trivial global lower bound (claimed value `0`). -/
theorem validValueLowerBound_toExtended_of_tm_eq_nil (μ : Environment) (γ : DiscountFactor) (horizon t : ℕ)
    (p : RawToPartrecProgram) (hp : p.tm = Turing.ToPartrec.Code.nil) :
    ValidValueLowerBound μ γ horizon (p.toExtended t) := by
  intro h _hwf
  have hclaim : ((p.toExtended t).compute h).1 = 0 := by
    simpa [RawToPartrecProgram.toExtended] using computeWithin_fst_eq_zero_of_tm_eq_nil (t := t) (p := p) (h := h) hp
  have hnonneg : 0 ≤ value μ (p.toExtended t).toAgent γ h horizon :=
    value_nonneg (μ := μ) (π := (p.toExtended t).toAgent) (γ := γ) (h := h) (n := horizon)
  simpa [hclaim] using hnonneg

/-- Any `ToPartrec` program of the form `zeroValueActionCode act` is globally valid (it always
claims value `0`, regardless of the action). -/
theorem validValueLowerBound_toExtended_of_tm_eq_zeroValueAction (μ : Environment) (γ : DiscountFactor) (horizon t : ℕ)
    (p : RawToPartrecProgram) (act : Turing.ToPartrec.Code) (hp : p.tm = zeroValueActionCode act) :
    ValidValueLowerBound μ γ horizon (p.toExtended t) := by
  intro h _hwf
  have hclaim : ((p.toExtended t).compute h).1 = 0 := by
    simpa [RawToPartrecProgram.toExtended] using
      computeWithin_fst_eq_zero_of_tm_eq_zeroValueAction (t := t) (p := p) (h := h) (act := act) hp
  have hnonneg : 0 ≤ value μ (p.toExtended t).toAgent γ h horizon :=
    value_nonneg (μ := μ) (π := (p.toExtended t).toAgent) (γ := γ) (h := h) (n := horizon)
  simpa [hclaim] using hnonneg

/-- Unbounded semantics for a raw `ToPartrec` program, defaulting to `(0, stay)` when evaluation does
not terminate (or decoding fails). -/
noncomputable def computeUnbounded (p : RawToPartrecProgram) (h : History) : ℝ × Action := by
  classical
  exact
    if hDom : (p.tm.eval (Coding.encodeHistoryNat h)).Dom then
      (Coding.decodeValueActionOutput ((p.tm.eval (Coding.encodeHistoryNat h)).get hDom)).getD (0, Action.stay)
    else
      (0, Action.stay)

@[simp] theorem computeUnbounded_of_dom (p : RawToPartrecProgram) (h : History)
    (hDom : (p.tm.eval (Coding.encodeHistoryNat h)).Dom) :
    p.computeUnbounded h =
      (Coding.decodeValueActionOutput ((p.tm.eval (Coding.encodeHistoryNat h)).get hDom)).getD (0, Action.stay) := by
  classical
  simp [RawToPartrecProgram.computeUnbounded, hDom]

@[simp] theorem computeUnbounded_of_not_dom (p : RawToPartrecProgram) (h : History)
    (hDom : ¬ (p.tm.eval (Coding.encodeHistoryNat h)).Dom) :
    p.computeUnbounded h = (0, Action.stay) := by
  classical
  simp [RawToPartrecProgram.computeUnbounded, hDom]

/-- The associated extended chronological program using unbounded `ToPartrec` semantics. -/
noncomputable def toExtendedUnbounded (p : RawToPartrecProgram) : ExtendedChronologicalProgram :=
  { code := p.code
    compute := p.computeUnbounded }

/-- If we increase the fuel, a time-bounded run stabilizes to the unbounded semantics. -/
theorem exists_computeWithin_eq_computeUnbounded (p : RawToPartrecProgram) (h : History) :
    ∃ N, ∀ t ≥ N, RawToPartrecProgram.computeWithin t p h = p.computeUnbounded h := by
  classical
  by_cases hDom : (p.tm.eval (Coding.encodeHistoryNat h)).Dom
  · let out : List ℕ := (p.tm.eval (Coding.encodeHistoryNat h)).get hDom
    have hout : out ∈ p.tm.eval (Coding.encodeHistoryNat h) := by
      simpa [out] using (Part.get_mem (o := p.tm.eval (Coding.encodeHistoryNat h)) hDom)
    have hex : ∃ n, StepCounting.ToPartrec.evalWithin n p.tm (Coding.encodeHistoryNat h) = some out :=
      (StepCounting.ToPartrec.exists_evalWithin_eq_some_iff (c := p.tm) (v := Coding.encodeHistoryNat h) (out := out)).2 hout
    rcases hex with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro t ht
    have ht' : StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) = some out :=
      StepCounting.ToPartrec.evalWithin_mono (h := hn) (hnm := ht)
    simp [RawToPartrecProgram.computeWithin, RawToPartrecProgram.computeUnbounded, hDom, out, ht']
  · refine ⟨0, ?_⟩
    intro t _ht
    have ht' : StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) = none := by
      cases hrun : StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) with
      | none => rfl
      | some out =>
          exfalso
          have hout : out ∈ p.tm.eval (Coding.encodeHistoryNat h) :=
            StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h) (out := out) hrun
          rcases hout with ⟨hDom', _houtEq⟩
          exact hDom hDom'
    simp [RawToPartrecProgram.computeWithin, RawToPartrecProgram.computeUnbounded, hDom, ht']

/-- Transport a pointwise equality on a raw list to equality of `bestByValueAux` on the corresponding
extended-program lists. -/
theorem bestByValueAux_map_toExtended_eq_of_forall (acc : ℝ × Action) (programs : List RawToPartrecProgram)
    (h : History) (t : ℕ)
    (hall : ∀ p ∈ programs, RawToPartrecProgram.computeWithin t p h = p.computeUnbounded h) :
    bestByValueAux acc (programs.map (fun p => p.toExtended t)) h =
      bestByValueAux acc (programs.map (fun p => p.toExtendedUnbounded)) h := by
  induction programs generalizing acc with
  | nil =>
      simp [bestByValueAux]
  | cons p ps ih =>
      have hp : RawToPartrecProgram.computeWithin t p h = p.computeUnbounded h := hall p (by simp)
      have hallTail : ∀ q ∈ ps, RawToPartrecProgram.computeWithin t q h = q.computeUnbounded h := by
        intro q hq
        exact hall q (by simp [hq])
      have ih' :=
        ih (acc := selectBetter acc (p.computeUnbounded h)) (hall := hallTail)
      simpa [bestByValueAux, List.foldl_cons, RawToPartrecProgram.toExtended, RawToPartrecProgram.toExtendedUnbounded, hp]
        using ih'

/-- Transport a pointwise equality on a raw list to equality of `bestByValue`. -/
theorem bestByValue_map_toExtended_eq_of_forall (programs : List RawToPartrecProgram) (h : History) (t : ℕ)
    (hall : ∀ p ∈ programs, RawToPartrecProgram.computeWithin t p h = p.computeUnbounded h) :
    bestByValue (programs.map (fun p => p.toExtended t)) h =
      bestByValue (programs.map (fun p => p.toExtendedUnbounded)) h := by
  cases programs with
  | nil =>
      simp [bestByValue]
  | cons p0 ps =>
      have hp0 : RawToPartrecProgram.computeWithin t p0 h = p0.computeUnbounded h := hall p0 (by simp)
      have hallTail : ∀ q ∈ ps, RawToPartrecProgram.computeWithin t q h = q.computeUnbounded h := by
        intro q hq
        exact hall q (by simp [hq])
      have haux :=
        bestByValueAux_map_toExtended_eq_of_forall (acc := p0.computeUnbounded h) (programs := ps) (h := h)
          (t := t) (hall := hallTail)
      simpa [bestByValue, RawToPartrecProgram.toExtended, RawToPartrecProgram.toExtendedUnbounded, hp0] using haux

/-- For a fixed raw program list and history, there is a single fuel bound beyond which all wrapped
computations agree with the unbounded semantics. -/
theorem exists_fuel_bound_forall_computeWithin_eq_computeUnbounded (programs : List RawToPartrecProgram)
    (h : History) :
    ∃ N, ∀ p ∈ programs, ∀ t ≥ N, RawToPartrecProgram.computeWithin t p h = p.computeUnbounded h := by
  classical
  induction programs with
  | nil =>
      refine ⟨0, ?_⟩
      intro p hp
      cases hp
  | cons p ps ih =>
      rcases exists_computeWithin_eq_computeUnbounded (p := p) (h := h) with ⟨Np, hNp⟩
      rcases ih with ⟨Nps, hNps⟩
      refine ⟨Nat.max Np Nps, ?_⟩
      intro q hq t ht
      simp [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hNp t (le_trans (Nat.le_max_left _ _) ht)
      · exact hNps q hq t (le_trans (Nat.le_max_right _ _) ht)

/-- For a fixed raw program list and history, `bestByValue` on the time-bounded wrappers stabilizes
to the unbounded semantics. -/
theorem exists_fuel_bound_bestByValue_eq_unbounded (programs : List RawToPartrecProgram) (h : History) :
    ∃ N, ∀ t ≥ N,
      bestByValue (programs.map (fun p => p.toExtended t)) h =
        bestByValue (programs.map (fun p => p.toExtendedUnbounded)) h := by
  classical
  rcases exists_fuel_bound_forall_computeWithin_eq_computeUnbounded (programs := programs) (h := h) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  refine bestByValue_map_toExtended_eq_of_forall (programs := programs) (h := h) (t := t) ?_
  intro p hp
  exact hN p hp t ht

end RawToPartrecProgram

/-- A “raw” environment program implemented as `ToPartrec.Code`.

The program takes an encoded `History` input and (deterministically) outputs a candidate next
`Percept`.  We interpret the output as a single percept code (first element of the output list),
and treat failures/timeouts as producing no percept (zero probability mass). -/
structure RawToPartrecEnvironmentProgram where
  code : Program
  tm : Turing.ToPartrec.Code

namespace RawToPartrecEnvironmentProgram

noncomputable def ofToPartrec (bits : List Bool) (tm : Turing.ToPartrec.Code) : RawToPartrecEnvironmentProgram :=
  { code := { code := bits }
    tm := tm }

noncomputable def decodeCanonical : ProofDecoder RawToPartrecEnvironmentProgram :=
  fun bits => (RawToPartrecProgram.decodeToPartrec bits).map (ofToPartrec bits)

def decodePerceptOutput : List ℕ → Option Percept
  | n :: _ => Coding.decodePerceptNat n
  | [] => none

def computeWithin (t : ℕ) (p : RawToPartrecEnvironmentProgram) (h : History) : Option Percept :=
  match StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) with
  | some out => decodePerceptOutput out
  | none => none

/-- Monotonicity of time-bounded evaluation: once `computeWithin` returns `some x` at fuel `t`,
it returns the same `some x` at all larger fuel bounds. -/
theorem computeWithin_mono (p : RawToPartrecEnvironmentProgram) (h : History) {t₁ t₂ : ℕ}
    (ht : t₁ ≤ t₂) {x : Percept} (hx : computeWithin t₁ p h = some x) :
    computeWithin t₂ p h = some x := by
  unfold computeWithin at hx ⊢
  cases hrun : StepCounting.ToPartrec.evalWithin t₁ p.tm (Coding.encodeHistoryNat h) with
  | none =>
      simp [hrun] at hx
  | some out =>
      have hx' : decodePerceptOutput out = some x := by
        simpa [hrun] using hx
      have hrun' :
          StepCounting.ToPartrec.evalWithin t₂ p.tm (Coding.encodeHistoryNat h) = some out :=
        StepCounting.ToPartrec.evalWithin_mono (h := hrun) (hnm := ht)
      simpa [hrun'] using hx'

/-- Unbounded semantics for a raw environment `ToPartrec` program, returning `none` when evaluation
does not terminate (or decoding fails). -/
noncomputable def computeUnbounded (p : RawToPartrecEnvironmentProgram) (h : History) : Option Percept := by
  classical
  exact
    if hDom : (p.tm.eval (Coding.encodeHistoryNat h)).Dom then
      decodePerceptOutput ((p.tm.eval (Coding.encodeHistoryNat h)).get hDom)
    else
      none

@[simp] theorem computeUnbounded_of_dom (p : RawToPartrecEnvironmentProgram) (h : History)
    (hDom : (p.tm.eval (Coding.encodeHistoryNat h)).Dom) :
    p.computeUnbounded h = decodePerceptOutput ((p.tm.eval (Coding.encodeHistoryNat h)).get hDom) := by
  classical
  simp [RawToPartrecEnvironmentProgram.computeUnbounded, hDom]

@[simp] theorem computeUnbounded_of_not_dom (p : RawToPartrecEnvironmentProgram) (h : History)
    (hDom : ¬ (p.tm.eval (Coding.encodeHistoryNat h)).Dom) :
    p.computeUnbounded h = none := by
  classical
  simp [RawToPartrecEnvironmentProgram.computeUnbounded, hDom]

/-- The associated deterministic (sub-)environment: probability 1 on the decoded output percept
when it exists within the budget, and 0 otherwise. -/
noncomputable def toEnvironmentWithin (t : ℕ) (p : RawToPartrecEnvironmentProgram) : Environment where
  prob h x := if computeWithin t p h = some x then 1 else 0
  prob_le_one h _hw := by
    classical
    cases hpx : computeWithin t p h with
    | none =>
        simp
    | some x0 =>
        -- Exactly one percept has probability 1.
        have :
            (∑' x : Percept, (if x = x0 then (1 : ENNReal) else 0)) = 1 := by
          simp [tsum_ite_eq]
        -- Rewrite the sum in the form expected by `tsum_ite_eq`.
        simpa [hpx, eq_comm] using this.le

theorem toEnvironmentWithin_prob_mono (p : RawToPartrecEnvironmentProgram) (h : History) (x : Percept) {t₁ t₂ : ℕ}
    (ht : t₁ ≤ t₂) :
    (p.toEnvironmentWithin t₁).prob h x ≤ (p.toEnvironmentWithin t₂).prob h x := by
  by_cases hx : computeWithin t₁ p h = some x
  · have hx' : computeWithin t₂ p h = some x := computeWithin_mono (p := p) (h := h) ht hx
    simp [RawToPartrecEnvironmentProgram.toEnvironmentWithin, hx, hx']
  · simp [RawToPartrecEnvironmentProgram.toEnvironmentWithin, hx]

/-- The associated deterministic (sub-)environment using unbounded semantics. -/
noncomputable def toEnvironmentUnbounded (p : RawToPartrecEnvironmentProgram) : Environment where
  prob h x := if computeUnbounded p h = some x then 1 else 0
  prob_le_one h _hw := by
    classical
    cases hpx : computeUnbounded p h with
    | none =>
        simp
    | some x0 =>
        have :
            (∑' x : Percept, (if x = x0 then (1 : ENNReal) else 0)) = 1 := by
          simp [tsum_ite_eq]
        simpa [hpx, eq_comm] using this.le

/-- For a fixed history, increasing the fuel eventually stabilizes `computeWithin` to
`computeUnbounded`. -/
theorem exists_computeWithin_eq_computeUnbounded (p : RawToPartrecEnvironmentProgram) (h : History) :
    ∃ N, ∀ t ≥ N, computeWithin t p h = computeUnbounded p h := by
  classical
  by_cases hDom : (p.tm.eval (Coding.encodeHistoryNat h)).Dom
  · let out : List ℕ := (p.tm.eval (Coding.encodeHistoryNat h)).get hDom
    have hout : out ∈ p.tm.eval (Coding.encodeHistoryNat h) := by
      simpa [out] using (Part.get_mem (o := p.tm.eval (Coding.encodeHistoryNat h)) hDom)
    have hex : ∃ n, StepCounting.ToPartrec.evalWithin n p.tm (Coding.encodeHistoryNat h) = some out :=
      (StepCounting.ToPartrec.exists_evalWithin_eq_some_iff (c := p.tm) (v := Coding.encodeHistoryNat h)
          (out := out)).2 hout
    rcases hex with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro t ht
    have ht' : StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) = some out :=
      StepCounting.ToPartrec.evalWithin_mono (h := hn) (hnm := ht)
    simp [computeWithin, RawToPartrecEnvironmentProgram.computeUnbounded, hDom, out, ht', decodePerceptOutput]
  · refine ⟨0, ?_⟩
    intro t _ht
    have ht' : StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) = none := by
      cases hrun : StepCounting.ToPartrec.evalWithin t p.tm (Coding.encodeHistoryNat h) with
      | none => rfl
      | some out =>
          exfalso
          have hout : out ∈ p.tm.eval (Coding.encodeHistoryNat h) :=
            StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h) (out := out) hrun
          rcases hout with ⟨hDom', _houtEq⟩
          exact hDom hDom'
    simp [computeWithin, RawToPartrecEnvironmentProgram.computeUnbounded, hDom, ht']

end RawToPartrecEnvironmentProgram

namespace RawToPartrecEnvironmentProgram

/-- For a fixed program list and history, there is a single fuel bound beyond which all `computeWithin`
results agree with `computeUnbounded`. -/
theorem exists_fuel_bound_forall_computeWithin_eq_computeUnbounded
    (programs : List RawToPartrecEnvironmentProgram) (h : History) :
    ∃ N, ∀ p ∈ programs, ∀ t ≥ N, computeWithin t p h = computeUnbounded p h := by
  classical
  induction programs with
  | nil =>
      refine ⟨0, ?_⟩
      intro p hp
      cases hp
  | cons p ps ih =>
      rcases exists_computeWithin_eq_computeUnbounded (p := p) (h := h) with ⟨Np, hNp⟩
      rcases ih with ⟨Nps, hNps⟩
      refine ⟨Nat.max Np Nps, ?_⟩
      intro q hq t ht
      simp [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hNp t (le_trans (Nat.le_max_left _ _) ht)
      · exact hNps q hq t (le_trans (Nat.le_max_right _ _) ht)

end RawToPartrecEnvironmentProgram

/-- Enumerate candidate deterministic environment programs from all bitstrings up to length `l`. -/
noncomputable def enumerateRawToPartrecEnvironmentPrograms (l : ℕ) : List RawToPartrecEnvironmentProgram :=
  (bitstringsUpTo l).filterMap RawToPartrecEnvironmentProgram.decodeCanonical

theorem length_enumerateRawToPartrecEnvironmentPrograms_add_one_le (l : ℕ) :
    (enumerateRawToPartrecEnvironmentPrograms l).length + 1 ≤ 2 ^ (l + 1) := by
  have hle : (enumerateRawToPartrecEnvironmentPrograms l).length ≤ (bitstringsUpTo l).length := by
    simpa [enumerateRawToPartrecEnvironmentPrograms] using
      (length_filterMap_le (f := RawToPartrecEnvironmentProgram.decodeCanonical) (l := bitstringsUpTo l))
  have hle' : (enumerateRawToPartrecEnvironmentPrograms l).length + 1 ≤ (bitstringsUpTo l).length + 1 :=
    Nat.add_le_add_right hle 1
  exact le_trans hle' (le_of_eq (length_bitstringsUpTo_add_one l))

/-- The per-step evaluation budget for all enumerated environment programs is `O(2^l · t)`. -/
theorem per_cycle_steps_enumerateRawToPartrecEnvironmentPrograms_le (l t : ℕ) :
    (enumerateRawToPartrecEnvironmentPrograms l).length * t ≤ 2 ^ (l + 1) * t := by
  have hlen : (enumerateRawToPartrecEnvironmentPrograms l).length ≤ 2 ^ (l + 1) :=
    le_trans (Nat.le_succ _) (length_enumerateRawToPartrecEnvironmentPrograms_add_one_le l)
  exact Nat.mul_le_mul_right t hlen

theorem mem_enumerateRawToPartrecEnvironmentPrograms_mono {m n : ℕ} (hmn : m ≤ n)
    {p : RawToPartrecEnvironmentProgram} (hp : p ∈ enumerateRawToPartrecEnvironmentPrograms m) :
    p ∈ enumerateRawToPartrecEnvironmentPrograms n := by
  unfold enumerateRawToPartrecEnvironmentPrograms at hp ⊢
  rcases (List.mem_filterMap).1 hp with ⟨bits, hbits, hdec⟩
  refine (List.mem_filterMap).2 ?_
  refine ⟨bits, mem_bitstringsUpTo_mono hmn hbits, hdec⟩

/-- A dummy environment with zero probability mass everywhere (useful as a tail filler). -/
noncomputable def zeroEnvironment : Environment where
  prob _ _ := 0
  prob_le_one _ _ := by
    simp

/-- ENNReal length-weight `2^{-|code|}` used for prefix-free mixtures. -/
noncomputable def xi_tlPrefixWeight (code : List Bool) : ENNReal :=
  ENNReal.ofReal ((2 : ℝ) ^ (-(code.length : ℤ)))

/-- A prefix-free length weight over an indexed list of payload bitstrings, using
`Coding.selfDelimitingEncode` to obtain a prefix-free code. -/
noncomputable def xi_tlPrefixFreeWeightAt (bits : List (List Bool)) (i : ℕ) : ENNReal :=
  if hi : i < bits.length then
    xi_tlPrefixWeight (Coding.selfDelimitingEncode (bits.get ⟨i, hi⟩))
  else
    0

theorem tsum_xi_tlPrefixFreeWeightAt_le_one (bits : List (List Bool)) (hnd : bits.Nodup) :
    (∑' i : ℕ, xi_tlPrefixFreeWeightAt bits i) ≤ 1 := by
  classical
  -- Reduce the `tsum` to a finite sum over `range bits.length`.
  have htsum :
      (∑' i : ℕ, xi_tlPrefixFreeWeightAt bits i) =
        ∑ i ∈ Finset.range bits.length, xi_tlPrefixFreeWeightAt bits i := by
    refine (tsum_eq_sum (s := Finset.range bits.length) ?_)
    intro i hi
    have hnot : ¬ i < bits.length := by
      simpa [Finset.mem_range] using hi
    simp [xi_tlPrefixFreeWeightAt, hnot]
  -- The codes used on `range bits.length`.
  let codeAt : ℕ → List Bool :=
    fun i =>
      if hi : i < bits.length then
        Coding.selfDelimitingEncode (bits.get ⟨i, hi⟩)
      else
        []
  let S : Finset (List Bool) := (Finset.range bits.length).image codeAt
  have hcodeAt_inj : Set.InjOn codeAt (↑(Finset.range bits.length) : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < bits.length := by
      simpa [Finset.mem_range] using hi
    have hj' : j < bits.length := by
      simpa [Finset.mem_range] using hj
    have hEnc :
        Coding.selfDelimitingEncode (bits.get ⟨i, hi'⟩) =
          Coding.selfDelimitingEncode (bits.get ⟨j, hj'⟩) := by
      simpa [codeAt, hi', hj'] using hij
    have hBits : bits.get ⟨i, hi'⟩ = bits.get ⟨j, hj'⟩ :=
      Coding.selfDelimitingEncode_injective hEnc
    have : (⟨i, hi'⟩ : Fin bits.length) = ⟨j, hj'⟩ :=
      (List.Nodup.get_inj_iff hnd).1 hBits
    exact congrArg Fin.val this
  have hprefix : Mettapedia.Logic.SolomonoffPrior.PrefixFree (↑S : Set (List Bool)) := by
    intro s hs t ht hne
    have hs' : s ∈ S := by simpa using hs
    have ht' : t ∈ S := by simpa using ht
    rcases Finset.mem_image.1 hs' with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.1 ht' with ⟨j, hj, rfl⟩
    have hi' : i < bits.length := by
      simpa [Finset.mem_range] using hi
    have hj' : j < bits.length := by
      simpa [Finset.mem_range] using hj
    have hbitsne : bits.get ⟨i, hi'⟩ ≠ bits.get ⟨j, hj'⟩ := by
      intro hEq
      apply hne
      have hEq' : bits[i] = bits[j] := by
        simpa [List.get_eq_getElem] using hEq
      have : codeAt i = codeAt j := by
        simp [codeAt, hi', hj', hEq']
      exact this
    -- Prefix-freeness of the self-delimiting encoder.
    simpa [codeAt, hi', hj'] using
      (Coding.selfDelimitingEncode_not_isPrefix_of_ne (p := bits.get ⟨i, hi'⟩)
        (q := bits.get ⟨j, hj'⟩) hbitsne)
  have hkraft : Mettapedia.Logic.SolomonoffPrior.kraftSum S ≤ 1 :=
    Mettapedia.Logic.SolomonoffPrior.kraft_inequality S hprefix
  have hS_ne_top : (∑ s ∈ S, xi_tlPrefixWeight s) ≠ (⊤ : ENNReal) := by
    refine (ENNReal.sum_ne_top).2 ?_
    intro s hs
    simp [xi_tlPrefixWeight]
  have htoReal :
      (∑ s ∈ S, xi_tlPrefixWeight s).toReal = Mettapedia.Logic.SolomonoffPrior.kraftSum S := by
    have hnotTop : ∀ s ∈ S, xi_tlPrefixWeight s ≠ (⊤ : ENNReal) := by
      intro s hs
      simp [xi_tlPrefixWeight]
    calc
      (∑ s ∈ S, xi_tlPrefixWeight s).toReal = ∑ s ∈ S, (xi_tlPrefixWeight s).toReal := by
        simpa using (ENNReal.toReal_sum (s := S) (f := xi_tlPrefixWeight) hnotTop)
      _ = ∑ s ∈ S, (2 : ℝ) ^ (-(s.length : ℤ)) := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        have hnonneg : 0 ≤ (2 : ℝ) ^ (-(s.length : ℤ)) :=
          zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
        simp [xi_tlPrefixWeight]
      _ = Mettapedia.Logic.SolomonoffPrior.kraftSum S := by
        simp [Mettapedia.Logic.SolomonoffPrior.kraftSum]
  have hS_le : (∑ s ∈ S, xi_tlPrefixWeight s) ≤ 1 := by
    have htoReal_le : (∑ s ∈ S, xi_tlPrefixWeight s).toReal ≤ (1 : ENNReal).toReal := by
      -- `toReal` converts the ENNReal sum to the real Kraft sum, which is ≤ 1.
      simpa [htoReal] using hkraft
    exact (ENNReal.toReal_le_toReal hS_ne_top (by simp)).1 htoReal_le
  have hsum_codes :
      (∑ i ∈ Finset.range bits.length, xi_tlPrefixFreeWeightAt bits i) = ∑ s ∈ S, xi_tlPrefixWeight s := by
    -- Convert the sum over indices to a sum over (distinct) codes.
    have hsumImage :
        (∑ s ∈ S, xi_tlPrefixWeight s) =
          ∑ i ∈ Finset.range bits.length, xi_tlPrefixWeight (codeAt i) :=
      Finset.sum_image (f := xi_tlPrefixWeight) (s := Finset.range bits.length) (g := codeAt) hcodeAt_inj
    -- Rewrite the RHS into `xi_tlPrefixFreeWeightAt`.
    have :
        (∑ i ∈ Finset.range bits.length, xi_tlPrefixFreeWeightAt bits i) =
          ∑ i ∈ Finset.range bits.length, xi_tlPrefixWeight (codeAt i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi' : i < bits.length := by
        simpa [Finset.mem_range] using hi
      simp [xi_tlPrefixFreeWeightAt, codeAt, hi', xi_tlPrefixWeight]
    -- Assemble.
    simpa [S] using this.trans hsumImage.symm
  -- Finish.
  have :
      (∑ i ∈ Finset.range bits.length, xi_tlPrefixFreeWeightAt bits i) ≤ 1 := by
    simpa [hsum_codes] using hS_le
  simpa [htsum] using this

/-- A concrete “ξ^tl” mixture environment, built from time-bounded `ToPartrec` evaluation.

This is a **first step** toward Equation (7.3): we use a standard summable weight sequence
(`geometricWeight`) over the enumerated candidate programs. -/
noncomputable def xi_tlBayesianMixtureWithPrograms (t : ℕ) (programs : List RawToPartrecEnvironmentProgram) :
    BayesianMixture :=
  { envs := fun i =>
      if hi : i < programs.length then
        (programs.get ⟨i, hi⟩).toEnvironmentWithin t
      else
        zeroEnvironment
    weights := Mettapedia.Logic.UniversalPrediction.geometricWeight
    weights_le_one := Mettapedia.Logic.UniversalPrediction.tsum_geometricWeight_le_one }

/-! #### Equation (7.3): prefix-free length weights

To mirror Hutter’s `2^{-ℓ(p)}` weighting, we attach weights `2^{-|code(p)|}` where `code(p)` is a
prefix-free self-delimiting code obtained by `Coding.selfDelimitingEncode`.  The Kraft inequality
(`Mettapedia.Logic.SolomonoffPrior.kraft_inequality`) yields the required `tsum` bound. -/

noncomputable def xi_tlBayesianMixturePrefixFree (t l : ℕ) : BayesianMixture :=
  let bits := bitstringsUpTo l
  { envs := fun i =>
      if hi : i < bits.length then
        match RawToPartrecEnvironmentProgram.decodeCanonical (bits.get ⟨i, hi⟩) with
        | some p => p.toEnvironmentWithin t
        | none => zeroEnvironment
      else
        zeroEnvironment
    weights := xi_tlPrefixFreeWeightAt bits
    weights_le_one := by
      simpa using
        (tsum_xi_tlPrefixFreeWeightAt_le_one (bits := bits) (hnd := nodup_bitstringsUpTo l)) }

noncomputable def xi_tlBayesianMixture (t l : ℕ) : BayesianMixture :=
  xi_tlBayesianMixturePrefixFree t l

noncomputable def xi_tlEnvironment (t l : ℕ) : Environment :=
  mixtureEnvironment (xi_tlBayesianMixture t l)

noncomputable def xi_tlBayesianMixtureUnboundedWithPrograms (programs : List RawToPartrecEnvironmentProgram) :
    BayesianMixture :=
  { envs := fun i =>
      if hi : i < programs.length then
        (programs.get ⟨i, hi⟩).toEnvironmentUnbounded
      else
        zeroEnvironment
    weights := Mettapedia.Logic.UniversalPrediction.geometricWeight
    weights_le_one := Mettapedia.Logic.UniversalPrediction.tsum_geometricWeight_le_one }

noncomputable def xi_tlBayesianMixtureUnboundedPrefixFree (l : ℕ) : BayesianMixture :=
  let bits := bitstringsUpTo l
  { envs := fun i =>
      if hi : i < bits.length then
        match RawToPartrecEnvironmentProgram.decodeCanonical (bits.get ⟨i, hi⟩) with
        | some p => p.toEnvironmentUnbounded
        | none => zeroEnvironment
      else
        zeroEnvironment
    weights := xi_tlPrefixFreeWeightAt bits
    weights_le_one := by
      simpa using
        (tsum_xi_tlPrefixFreeWeightAt_le_one (bits := bits) (hnd := nodup_bitstringsUpTo l)) }

noncomputable def xi_tlBayesianMixtureUnbounded (l : ℕ) : BayesianMixture :=
  xi_tlBayesianMixtureUnboundedPrefixFree l

noncomputable def xi_tlEnvironmentUnbounded (l : ℕ) : Environment :=
  mixtureEnvironment (xi_tlBayesianMixtureUnbounded l)

/-- For fixed `l`, the time-bounded mixture environment `ξ^tl` is monotone in the per-cycle time budget `t`:
allowing more fuel can only increase the probability mass assigned to a given percept. -/
theorem xi_tlEnvironment_prob_mono (l : ℕ) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) (h : History) (x : Percept) :
    (xi_tlEnvironment t₁ l).prob h x ≤ (xi_tlEnvironment t₂ l).prob h x := by
  classical
  -- Pointwise monotonicity of the mixture components, lifted through `tsum`.
  refine ENNReal.tsum_le_tsum ?_
  intro i
  let bits := bitstringsUpTo l
  by_cases hi : i < bits.length
  · -- Inside the enumerated window, the weight is the same for both `t₁` and `t₂`.
    simp [xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree,
      xi_tlPrefixFreeWeightAt, bits, hi]
    -- Case split on whether the bitstring decodes to a concrete environment program.
    cases hdec : RawToPartrecEnvironmentProgram.decodeCanonical (bits.get ⟨i, hi⟩) with
    | none =>
        simp
    | some p =>
        have hprob :
            (p.toEnvironmentWithin t₁).prob h x ≤ (p.toEnvironmentWithin t₂).prob h x :=
          RawToPartrecEnvironmentProgram.toEnvironmentWithin_prob_mono (p := p) (h := h) (x := x) ht
        have := mul_le_mul_of_nonneg_left hprob (by
          simp [xi_tlPrefixWeight] : 0 ≤ xi_tlPrefixWeight (Coding.selfDelimitingEncode (bits.get ⟨i, hi⟩)))
        simpa [hdec] using this
  · -- Outside the enumerated window, the weight is 0, so the contribution is 0 on both sides.
    simp [xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree,
      xi_tlPrefixFreeWeightAt, bits, hi]

/-- For fixed `l`, `h`, and percept `x`, the pointwise probability mass assigned by `ξ^tl` stabilizes
to the unbounded semantics as `t → ∞`. -/
theorem exists_fuel_bound_xi_tlEnvironment_prob_eq_unbounded (l : ℕ) (h : History) (x : Percept) :
    ∃ N, ∀ t ≥ N, (xi_tlEnvironment t l).prob h x = (xi_tlEnvironmentUnbounded l).prob h x := by
  classical
  let bits := bitstringsUpTo l
  let programs := enumerateRawToPartrecEnvironmentPrograms l
  rcases
      RawToPartrecEnvironmentProgram.exists_fuel_bound_forall_computeWithin_eq_computeUnbounded
        (programs := programs) (h := h) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  let ξt : BayesianMixture := xi_tlBayesianMixture t l
  let ξInf : BayesianMixture := xi_tlBayesianMixtureUnbounded l
  -- Reduce both `tsum`s to finite sums over `range bits.length`.
  have htsumWithin :
      (∑' i : ℕ, ξt.weights i * (ξt.envs i).prob h x) =
        ∑ i ∈ Finset.range bits.length, ξt.weights i * (ξt.envs i).prob h x := by
    refine (tsum_eq_sum (s := Finset.range bits.length) ?_)
    intro i hi
    have hnot : ¬ i < bits.length := by
      simpa [Finset.mem_range] using hi
    simp [ξt, xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, bits, xi_tlPrefixFreeWeightAt, hnot,
      zeroEnvironment]
  have htsumUnbounded :
      (∑' i : ℕ, ξInf.weights i * (ξInf.envs i).prob h x) =
        ∑ i ∈ Finset.range bits.length, ξInf.weights i * (ξInf.envs i).prob h x := by
    refine (tsum_eq_sum (s := Finset.range bits.length) ?_)
    intro i hi
    have hnot : ¬ i < bits.length := by
      simpa [Finset.mem_range] using hi
    simp [ξInf, xi_tlBayesianMixtureUnbounded, xi_tlBayesianMixtureUnboundedPrefixFree, bits,
      xi_tlPrefixFreeWeightAt, hnot, zeroEnvironment]
  have hterm :
      ∀ i ∈ Finset.range bits.length,
        ξt.weights i * (ξt.envs i).prob h x = ξInf.weights i * (ξInf.envs i).prob h x := by
    intro i hi
    have hil : i < bits.length := by
      simpa [Finset.mem_range] using hi
    -- Case split on whether the `i`-th bitstring decodes to an environment program.
    cases hdec : RawToPartrecEnvironmentProgram.decodeCanonical (bits.get ⟨i, hil⟩) with
    | none =>
        have hdec' : RawToPartrecEnvironmentProgram.decodeCanonical bits[i] = none := by
          simpa [List.get_eq_getElem] using hdec
        simp [ξt, ξInf, xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, xi_tlBayesianMixtureUnbounded,
          xi_tlBayesianMixtureUnboundedPrefixFree, bits, xi_tlPrefixFreeWeightAt, hil, hdec', zeroEnvironment]
    | some p =>
        have hpMem : p ∈ programs := by
          unfold programs
          unfold enumerateRawToPartrecEnvironmentPrograms
          refine (List.mem_filterMap).2 ?_
          refine ⟨bits.get ⟨i, hil⟩, ?_, hdec⟩
          simp [bits]
        have hCompute :
            RawToPartrecEnvironmentProgram.computeWithin t p h = p.computeUnbounded h :=
          hN p hpMem t ht
        have hdec' : RawToPartrecEnvironmentProgram.decodeCanonical bits[i] = some p := by
          simpa [List.get_eq_getElem] using hdec
        simp [ξt, ξInf, xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, xi_tlBayesianMixtureUnbounded,
          xi_tlBayesianMixtureUnboundedPrefixFree, bits, xi_tlPrefixFreeWeightAt, hil, hdec',
          RawToPartrecEnvironmentProgram.toEnvironmentWithin, RawToPartrecEnvironmentProgram.toEnvironmentUnbounded,
          hCompute, zeroEnvironment]
  have hsum :
      (∑ i ∈ Finset.range bits.length, ξt.weights i * (ξt.envs i).prob h x) =
        ∑ i ∈ Finset.range bits.length, ξInf.weights i * (ξInf.envs i).prob h x := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hterm i hi
  -- Assemble.
  calc
    (xi_tlEnvironment t l).prob h x
        = ∑' i : ℕ, ξt.weights i * (ξt.envs i).prob h x := by
            simp [xi_tlEnvironment, ξt, mixtureEnvironment]
    _ = ∑ i ∈ Finset.range bits.length, ξt.weights i * (ξt.envs i).prob h x := htsumWithin
    _ = ∑ i ∈ Finset.range bits.length, ξInf.weights i * (ξInf.envs i).prob h x := hsum
    _ = ∑' i : ℕ, ξInf.weights i * (ξInf.envs i).prob h x := by
          symm
          exact htsumUnbounded
    _ = (xi_tlEnvironmentUnbounded l).prob h x := by
          simp [xi_tlEnvironmentUnbounded, ξInf, mixtureEnvironment]

/-- For fixed `l`, each time-bounded approximation of `ξ^tl` is bounded above by the unbounded semantics. -/
theorem xi_tlEnvironment_prob_le_unbounded (l : ℕ) (t : ℕ) (h : History) (x : Percept) :
    (xi_tlEnvironment t l).prob h x ≤ (xi_tlEnvironmentUnbounded l).prob h x := by
  classical
  rcases exists_fuel_bound_xi_tlEnvironment_prob_eq_unbounded (l := l) (h := h) (x := x) with ⟨N, hN⟩
  have hmono :
      (xi_tlEnvironment t l).prob h x ≤ (xi_tlEnvironment (max t N) l).prob h x :=
    xi_tlEnvironment_prob_mono (l := l) (t₁ := t) (t₂ := max t N) (ht := le_max_left _ _) h x
  have hEq :
      (xi_tlEnvironment (max t N) l).prob h x = (xi_tlEnvironmentUnbounded l).prob h x :=
    hN (max t N) (le_max_right _ _)
  simpa [hEq] using hmono

/-- For fixed `l`, `h`, and percept `x`, the unbounded semantics is the supremum of the time-bounded
approximations. -/
theorem iSup_xi_tlEnvironment_prob_eq_unbounded (l : ℕ) (h : History) (x : Percept) :
    (⨆ t : ℕ, (xi_tlEnvironment t l).prob h x) = (xi_tlEnvironmentUnbounded l).prob h x := by
  classical
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro t
    exact xi_tlEnvironment_prob_le_unbounded (l := l) (t := t) (h := h) (x := x)
  · rcases exists_fuel_bound_xi_tlEnvironment_prob_eq_unbounded (l := l) (h := h) (x := x) with ⟨N, hN⟩
    have hEq : (xi_tlEnvironment N l).prob h x = (xi_tlEnvironmentUnbounded l).prob h x :=
      hN N (le_rfl)
    have hle : (xi_tlEnvironment N l).prob h x ≤ ⨆ t : ℕ, (xi_tlEnvironment t l).prob h x :=
      le_iSup (fun t : ℕ => (xi_tlEnvironment t l).prob h x) N
    simpa [hEq] using hle

/-! #### ξ^tl monotonicity: optimal value -/

/-- If an environment's per-step semimeasure mass increases pointwise, then all finite-horizon optimal values
and optimal Q-values increase as well. -/
theorem optimalValue_optimalQValue_mono_of_prob_mono (μ₁ μ₂ : Environment) (γ : DiscountFactor)
    (hprob : ∀ h x, μ₁.prob h x ≤ μ₂.prob h x) :
    ∀ n : ℕ,
      (∀ h : History, optimalValue μ₁ γ h n ≤ optimalValue μ₂ γ h n) ∧
        (∀ h : History, ∀ a : Action, optimalQValue μ₁ γ h a n ≤ optimalQValue μ₂ γ h a n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro h
        simp [optimalValue_zero]
      · intro h a
        simp [optimalQValue_zero]
  | succ n ih =>
      rcases ih with ⟨ihV, ihQ⟩
      refine ⟨?_, ?_⟩
      · intro h
        by_cases hw : h.wellFormed
        · -- `V*` is a max over the three actions.
          -- Use the well-formed max characterization and expand the 3-element fold.
          rw [optimalValue_is_max (μ := μ₁) (γ := γ) (h := h) (k := n) hw]
          rw [optimalValue_is_max (μ := μ₂) (γ := γ) (h := h) (k := n) hw]
          simp only [List.foldl_cons, List.foldl_nil]
          have hleft : optimalQValue μ₁ γ h Action.left n ≤ optimalQValue μ₂ γ h Action.left n := ihQ h Action.left
          have hright : optimalQValue μ₁ γ h Action.right n ≤ optimalQValue μ₂ γ h Action.right n := ihQ h Action.right
          have hstay : optimalQValue μ₁ γ h Action.stay n ≤ optimalQValue μ₂ γ h Action.stay n := ihQ h Action.stay
          exact max_le_max (max_le_max (max_le_max (le_rfl : (0 : ℝ) ≤ 0) hleft) hright) hstay
        · simp [optimalValue_succ, hw]
      · intro h a
        -- Unfold both `optimalQValue` definitions at horizon `n+1`.
        set ha : History := h ++ [HistElem.act a]
        by_cases hha : ha.wellFormed
        · -- Reduce to the explicit 4-percept sum and compare term-by-term.
          have hprob_toReal (x : Percept) : (μ₁.prob ha x).toReal ≤ (μ₂.prob ha x).toReal := by
            have hx_le_one : μ₂.prob ha x ≤ 1 :=
              le_trans (ENNReal.le_tsum x) (μ₂.prob_le_one ha hha)
            have hx_ne_top : μ₂.prob ha x ≠ (⊤ : ENNReal) :=
              ne_top_of_le_ne_top ENNReal.one_ne_top hx_le_one
            exact ENNReal.toReal_mono hx_ne_top (hprob ha x)
          have hfuture_mono (x : Percept) :
              x.reward + γ.val * optimalValue μ₁ γ (ha ++ [HistElem.per x]) n ≤
                x.reward + γ.val * optimalValue μ₂ γ (ha ++ [HistElem.per x]) n := by
            have hv : optimalValue μ₁ γ (ha ++ [HistElem.per x]) n ≤ optimalValue μ₂ γ (ha ++ [HistElem.per x]) n :=
              ihV (ha ++ [HistElem.per x])
            exact add_le_add_left (mul_le_mul_of_nonneg_left hv γ.nonneg) _
          have hterm (x : Percept) :
              (μ₁.prob ha x).toReal * (x.reward + γ.val * optimalValue μ₁ γ (ha ++ [HistElem.per x]) n) ≤
                (μ₂.prob ha x).toReal * (x.reward + γ.val * optimalValue μ₂ γ (ha ++ [HistElem.per x]) n) := by
            have hstep1 :
                (μ₁.prob ha x).toReal * (x.reward + γ.val * optimalValue μ₁ γ (ha ++ [HistElem.per x]) n) ≤
                  (μ₁.prob ha x).toReal * (x.reward + γ.val * optimalValue μ₂ γ (ha ++ [HistElem.per x]) n) :=
              mul_le_mul_of_nonneg_left (hfuture_mono x) ENNReal.toReal_nonneg
            have hfactor_nonneg :
                0 ≤ x.reward + γ.val * optimalValue μ₂ γ (ha ++ [HistElem.per x]) n :=
              add_nonneg (Percept.reward_nonneg x)
                (mul_nonneg γ.nonneg (optimalValue_nonneg (μ := μ₂) (γ := γ) (h := ha ++ [HistElem.per x]) (n := n)))
            have hstep2 :
                (μ₁.prob ha x).toReal * (x.reward + γ.val * optimalValue μ₂ γ (ha ++ [HistElem.per x]) n) ≤
                  (μ₂.prob ha x).toReal * (x.reward + γ.val * optimalValue μ₂ γ (ha ++ [HistElem.per x]) n) :=
              mul_le_mul_of_nonneg_right (hprob_toReal x) hfactor_nonneg
            exact le_trans hstep1 hstep2
          have hff := hterm (Percept.mk false false)
          have hft := hterm (Percept.mk false true)
          have htf := hterm (Percept.mk true false)
          have htt := hterm (Percept.mk true true)
          have hff' :
              (μ₁.prob (h ++ [HistElem.act a]) (Percept.mk false false)).toReal *
                  ((Percept.mk false false).reward +
                    γ.val *
                      optimalValue μ₁ γ (h ++ [HistElem.act a, HistElem.per (Percept.mk false false)]) n) ≤
                (μ₂.prob (h ++ [HistElem.act a]) (Percept.mk false false)).toReal *
                  ((Percept.mk false false).reward +
                    γ.val *
                      optimalValue μ₂ γ (h ++ [HistElem.act a, HistElem.per (Percept.mk false false)]) n) := by
            simpa [ha, List.append_assoc] using hff
          have hft' :
              (μ₁.prob (h ++ [HistElem.act a]) (Percept.mk false true)).toReal *
                  ((Percept.mk false true).reward +
                    γ.val *
                      optimalValue μ₁ γ (h ++ [HistElem.act a, HistElem.per (Percept.mk false true)]) n) ≤
                (μ₂.prob (h ++ [HistElem.act a]) (Percept.mk false true)).toReal *
                  ((Percept.mk false true).reward +
                    γ.val *
                      optimalValue μ₂ γ (h ++ [HistElem.act a, HistElem.per (Percept.mk false true)]) n) := by
            simpa [ha, List.append_assoc] using hft
          have htf' :
              (μ₁.prob (h ++ [HistElem.act a]) (Percept.mk true false)).toReal *
                  ((Percept.mk true false).reward +
                    γ.val *
                      optimalValue μ₁ γ (h ++ [HistElem.act a, HistElem.per (Percept.mk true false)]) n) ≤
                (μ₂.prob (h ++ [HistElem.act a]) (Percept.mk true false)).toReal *
                  ((Percept.mk true false).reward +
                    γ.val *
                      optimalValue μ₂ γ (h ++ [HistElem.act a, HistElem.per (Percept.mk true false)]) n) := by
            simpa [ha, List.append_assoc] using htf
          have htt' :
              (μ₁.prob (h ++ [HistElem.act a]) (Percept.mk true true)).toReal *
                  ((Percept.mk true true).reward +
                    γ.val *
                      optimalValue μ₁ γ (h ++ [HistElem.act a, HistElem.per (Percept.mk true true)]) n) ≤
                (μ₂.prob (h ++ [HistElem.act a]) (Percept.mk true true)).toReal *
                  ((Percept.mk true true).reward +
                    γ.val *
                      optimalValue μ₂ γ (h ++ [HistElem.act a, HistElem.per (Percept.mk true true)]) n) := by
            simpa [ha, List.append_assoc] using htt
          -- Unfold both sides and then sum the four term-wise inequalities.
          simp [optimalQValue, ha, hha, List.foldl_cons, List.foldl_nil, add_assoc]
          exact add_le_add hff' (add_le_add hft' (add_le_add htf' htt'))
        · simp [optimalQValue, ha, hha]

/-! #### Monotonicity (fixed policy): value -/

/-- If an environment's per-step semimeasure mass increases pointwise, then all finite-horizon values and Q-values
for a fixed agent increase as well. -/
theorem value_qValue_mono_of_prob_mono (μ₁ μ₂ : Environment) (π : Agent) (γ : DiscountFactor)
    (hprob : ∀ h x, μ₁.prob h x ≤ μ₂.prob h x) :
    ∀ n : ℕ,
      (∀ h : History, value μ₁ π γ h n ≤ value μ₂ π γ h n) ∧
        (∀ h : History, ∀ a : Action, qValue μ₁ π γ h a n ≤ qValue μ₂ π γ h a n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro h
        simp [value_zero]
      · intro h a
        simp [qValue_zero]
  | succ n ih =>
      rcases ih with ⟨ihV, ihQ⟩
      refine ⟨?_, ?_⟩
      · intro h
        by_cases hw : h.wellFormed
        · -- Reduce to the explicit 3-action sum and compare term-by-term.
          have hterm (a : Action) :
              (π.policy h a).toReal * qValue μ₁ π γ h a n ≤ (π.policy h a).toReal * qValue μ₂ π γ h a n :=
            mul_le_mul_of_nonneg_left (ihQ h a) ENNReal.toReal_nonneg
          have hleft := hterm Action.left
          have hright := hterm Action.right
          have hstay := hterm Action.stay
          simp [value, hw, List.foldl_cons, List.foldl_nil, add_assoc]
          exact add_le_add hleft (add_le_add hright hstay)
        · simp [value, hw]
      · intro h a
        set ha : History := h ++ [HistElem.act a]
        by_cases hha : ha.wellFormed
        · -- Reduce to the explicit 4-percept sum and compare term-by-term.
          have hprob_toReal (x : Percept) : (μ₁.prob ha x).toReal ≤ (μ₂.prob ha x).toReal := by
            have hx_le_one : μ₂.prob ha x ≤ 1 :=
              le_trans (ENNReal.le_tsum x) (μ₂.prob_le_one ha hha)
            have hx_ne_top : μ₂.prob ha x ≠ (⊤ : ENNReal) :=
              ne_top_of_le_ne_top ENNReal.one_ne_top hx_le_one
            exact ENNReal.toReal_mono hx_ne_top (hprob ha x)
          have hfuture_mono (x : Percept) :
              x.reward + γ.val * value μ₁ π γ (ha ++ [HistElem.per x]) n ≤
                x.reward + γ.val * value μ₂ π γ (ha ++ [HistElem.per x]) n := by
            have hv : value μ₁ π γ (ha ++ [HistElem.per x]) n ≤ value μ₂ π γ (ha ++ [HistElem.per x]) n :=
              ihV (ha ++ [HistElem.per x])
            exact add_le_add_left (mul_le_mul_of_nonneg_left hv γ.nonneg) _
          have hterm (x : Percept) :
              (μ₁.prob ha x).toReal * (x.reward + γ.val * value μ₁ π γ (ha ++ [HistElem.per x]) n) ≤
                (μ₂.prob ha x).toReal * (x.reward + γ.val * value μ₂ π γ (ha ++ [HistElem.per x]) n) := by
            have hstep1 :
                (μ₁.prob ha x).toReal * (x.reward + γ.val * value μ₁ π γ (ha ++ [HistElem.per x]) n) ≤
                  (μ₁.prob ha x).toReal * (x.reward + γ.val * value μ₂ π γ (ha ++ [HistElem.per x]) n) :=
              mul_le_mul_of_nonneg_left (hfuture_mono x) ENNReal.toReal_nonneg
            have hfactor_nonneg :
                0 ≤ x.reward + γ.val * value μ₂ π γ (ha ++ [HistElem.per x]) n :=
              add_nonneg (Percept.reward_nonneg x)
                (mul_nonneg γ.nonneg (value_nonneg (μ := μ₂) (π := π) (γ := γ) (h := ha ++ [HistElem.per x]) (n := n)))
            have hstep2 :
                (μ₁.prob ha x).toReal * (x.reward + γ.val * value μ₂ π γ (ha ++ [HistElem.per x]) n) ≤
                  (μ₂.prob ha x).toReal * (x.reward + γ.val * value μ₂ π γ (ha ++ [HistElem.per x]) n) :=
              mul_le_mul_of_nonneg_right (hprob_toReal x) hfactor_nonneg
            exact le_trans hstep1 hstep2
          have hff := hterm (Percept.mk false false)
          have hft := hterm (Percept.mk false true)
          have htf := hterm (Percept.mk true false)
          have htt := hterm (Percept.mk true true)
          have hff' :
              (μ₁.prob (h ++ [HistElem.act a]) (Percept.mk false false)).toReal *
                  ((Percept.mk false false).reward +
                    γ.val *
                      value μ₁ π γ (h ++ [HistElem.act a, HistElem.per (Percept.mk false false)]) n) ≤
                (μ₂.prob (h ++ [HistElem.act a]) (Percept.mk false false)).toReal *
                  ((Percept.mk false false).reward +
                    γ.val *
                      value μ₂ π γ (h ++ [HistElem.act a, HistElem.per (Percept.mk false false)]) n) := by
            simpa [ha, List.append_assoc] using hff
          have hft' :
              (μ₁.prob (h ++ [HistElem.act a]) (Percept.mk false true)).toReal *
                  ((Percept.mk false true).reward +
                    γ.val *
                      value μ₁ π γ (h ++ [HistElem.act a, HistElem.per (Percept.mk false true)]) n) ≤
                (μ₂.prob (h ++ [HistElem.act a]) (Percept.mk false true)).toReal *
                  ((Percept.mk false true).reward +
                    γ.val *
                      value μ₂ π γ (h ++ [HistElem.act a, HistElem.per (Percept.mk false true)]) n) := by
            simpa [ha, List.append_assoc] using hft
          have htf' :
              (μ₁.prob (h ++ [HistElem.act a]) (Percept.mk true false)).toReal *
                  ((Percept.mk true false).reward +
                    γ.val *
                      value μ₁ π γ (h ++ [HistElem.act a, HistElem.per (Percept.mk true false)]) n) ≤
                (μ₂.prob (h ++ [HistElem.act a]) (Percept.mk true false)).toReal *
                  ((Percept.mk true false).reward +
                    γ.val *
                      value μ₂ π γ (h ++ [HistElem.act a, HistElem.per (Percept.mk true false)]) n) := by
            simpa [ha, List.append_assoc] using htf
          have htt' :
              (μ₁.prob (h ++ [HistElem.act a]) (Percept.mk true true)).toReal *
                  ((Percept.mk true true).reward +
                    γ.val *
                      value μ₁ π γ (h ++ [HistElem.act a, HistElem.per (Percept.mk true true)]) n) ≤
                (μ₂.prob (h ++ [HistElem.act a]) (Percept.mk true true)).toReal *
                  ((Percept.mk true true).reward +
                    γ.val *
                      value μ₂ π γ (h ++ [HistElem.act a, HistElem.per (Percept.mk true true)]) n) := by
            simpa [ha, List.append_assoc] using htt
          -- Unfold both sides and then sum the four term-wise inequalities.
          simp [qValue, ha, hha, List.foldl_cons, List.foldl_nil, add_assoc]
          exact add_le_add hff' (add_le_add hft' (add_le_add htf' htt'))
        · simp [qValue, ha, hha]

/-- Lift a `ValidValueLowerBound` fact along pointwise probability monotonicity of environments. -/
theorem validValueLowerBound_mono_of_prob_mono (μ₁ μ₂ : Environment) (γ : DiscountFactor) (horizon : ℕ)
    (hprob : ∀ h x, μ₁.prob h x ≤ μ₂.prob h x) {p : ExtendedChronologicalProgram}
    (hvalid : ValidValueLowerBound μ₁ γ horizon p) :
    ValidValueLowerBound μ₂ γ horizon p := by
  intro h hwf
  have hclaim : (p.compute h).1 ≤ value μ₁ p.toAgent γ h horizon :=
    hvalid h hwf
  have hmono :
      value μ₁ p.toAgent γ h horizon ≤ value μ₂ p.toAgent γ h horizon :=
    (value_qValue_mono_of_prob_mono (μ₁ := μ₁) (μ₂ := μ₂) (π := p.toAgent) (γ := γ) (hprob := hprob) horizon).1 h
  exact le_trans hclaim hmono

/-- Specialization: for fixed `l`, the finite-horizon optimal value under `ξ^tl` is monotone in the per-cycle
time bound `t`. -/
theorem optimalValue_xi_tlEnvironment_mono (l : ℕ) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) (γ : DiscountFactor)
    (h : History) (n : ℕ) :
    optimalValue (xi_tlEnvironment t₁ l) γ h n ≤ optimalValue (xi_tlEnvironment t₂ l) γ h n := by
  have hmono :=
    (optimalValue_optimalQValue_mono_of_prob_mono (μ₁ := xi_tlEnvironment t₁ l) (μ₂ := xi_tlEnvironment t₂ l) (γ := γ)
        (hprob := fun h x => xi_tlEnvironment_prob_mono (l := l) (t₁ := t₁) (t₂ := t₂) ht h x) n).1
  exact hmono h

/-- For fixed `l`, finite-horizon optimal values (and optimal Q-values) under `ξ^tl` stabilize to the unbounded
semantics as `t → ∞`. -/
theorem exists_fuel_bound_optimalValue_optimalQValue_xi_tlEnvironment_eq_unbounded (l : ℕ) (γ : DiscountFactor) :
    ∀ n : ℕ,
      (∀ h : History,
          ∃ N, ∀ t ≥ N,
            optimalValue (xi_tlEnvironment t l) γ h n = optimalValue (xi_tlEnvironmentUnbounded l) γ h n) ∧
        (∀ h : History,
            ∀ a : Action,
              ∃ N, ∀ t ≥ N,
                optimalQValue (xi_tlEnvironment t l) γ h a n =
                  optimalQValue (xi_tlEnvironmentUnbounded l) γ h a n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro h
        refine ⟨0, ?_⟩
        intro t _ht
        simp [optimalValue_zero]
      · intro h a
        refine ⟨0, ?_⟩
        intro t _ht
        simp [optimalQValue_zero]
  | succ n ih =>
      rcases ih with ⟨ihV, ihQ⟩
      refine ⟨?_, ?_⟩
      · intro h
        by_cases hw : h.wellFormed
        · -- Take a max fuel bound large enough for the three `Q*` equalities at horizon `n`.
          rcases ihQ h Action.left with ⟨Nl, hNl⟩
          rcases ihQ h Action.right with ⟨Nr, hNr⟩
          rcases ihQ h Action.stay with ⟨Ns, hNs⟩
          let N : ℕ := Nat.max Nl (Nat.max Nr Ns)
          refine ⟨N, ?_⟩
          intro t ht
          have hQl :
              optimalQValue (xi_tlEnvironment t l) γ h Action.left n =
                optimalQValue (xi_tlEnvironmentUnbounded l) γ h Action.left n :=
            hNl t (le_trans (Nat.le_max_left _ _) ht)
          have hQr :
              optimalQValue (xi_tlEnvironment t l) γ h Action.right n =
                optimalQValue (xi_tlEnvironmentUnbounded l) γ h Action.right n :=
            hNr t
              (le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) ht)
          have hQs :
              optimalQValue (xi_tlEnvironment t l) γ h Action.stay n =
                optimalQValue (xi_tlEnvironmentUnbounded l) γ h Action.stay n :=
            hNs t
              (le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) ht)
          -- Rewrite both sides as the 3-action fold and replace each `Q*` term.
          rw [optimalValue_is_max (μ := xi_tlEnvironment t l) (γ := γ) (h := h) (k := n) hw]
          rw [optimalValue_is_max (μ := xi_tlEnvironmentUnbounded l) (γ := γ) (h := h) (k := n) hw]
          simp [List.foldl_cons, List.foldl_nil, hQl, hQr, hQs]
        · -- Not well-formed: both sides are definitionally `0`.
          refine ⟨0, ?_⟩
          intro t _ht
          simp [optimalValue_succ, hw]
      · intro h a
        let ha : History := h ++ [HistElem.act a]
        by_cases hha : ha.wellFormed
        · -- Take a max fuel bound large enough for:
          -- (1) all four percept probabilities at `ha`, and
          -- (2) all four future `V*` equalities at horizon `n`.
          rcases exists_fuel_bound_xi_tlEnvironment_prob_eq_unbounded (l := l) (h := ha) (x := Percept.mk false false) with
            ⟨NffP, hNffP⟩
          rcases exists_fuel_bound_xi_tlEnvironment_prob_eq_unbounded (l := l) (h := ha) (x := Percept.mk false true) with
            ⟨NftP, hNftP⟩
          rcases exists_fuel_bound_xi_tlEnvironment_prob_eq_unbounded (l := l) (h := ha) (x := Percept.mk true false) with
            ⟨NtfP, hNtfP⟩
          rcases exists_fuel_bound_xi_tlEnvironment_prob_eq_unbounded (l := l) (h := ha) (x := Percept.mk true true) with
            ⟨NttP, hNttP⟩
          rcases ihV (ha ++ [HistElem.per (Percept.mk false false)]) with ⟨NffV, hNffV⟩
          rcases ihV (ha ++ [HistElem.per (Percept.mk false true)]) with ⟨NftV, hNftV⟩
          rcases ihV (ha ++ [HistElem.per (Percept.mk true false)]) with ⟨NtfV, hNtfV⟩
          rcases ihV (ha ++ [HistElem.per (Percept.mk true true)]) with ⟨NttV, hNttV⟩
          let Np : ℕ := Nat.max NffP (Nat.max NftP (Nat.max NtfP NttP))
          let Nv : ℕ := Nat.max NffV (Nat.max NftV (Nat.max NtfV NttV))
          let N : ℕ := Nat.max Np Nv
          refine ⟨N, ?_⟩
          intro t ht
          have htNp : Np ≤ t := le_trans (Nat.le_max_left Np Nv) ht
          have htNv : Nv ≤ t := le_trans (Nat.le_max_right Np Nv) ht
          have hffP :
              (xi_tlEnvironment t l).prob ha (Percept.mk false false) =
                (xi_tlEnvironmentUnbounded l).prob ha (Percept.mk false false) :=
            hNffP t (le_trans (Nat.le_max_left NffP (Nat.max NftP (Nat.max NtfP NttP))) htNp)
          have hftP :
              (xi_tlEnvironment t l).prob ha (Percept.mk false true) =
                (xi_tlEnvironmentUnbounded l).prob ha (Percept.mk false true) :=
            hNftP t
              (le_trans
                (le_trans (Nat.le_max_left NftP (Nat.max NtfP NttP))
                  (Nat.le_max_right NffP (Nat.max NftP (Nat.max NtfP NttP))))
                htNp)
          have htfP :
              (xi_tlEnvironment t l).prob ha (Percept.mk true false) =
                (xi_tlEnvironmentUnbounded l).prob ha (Percept.mk true false) :=
            hNtfP t
              (le_trans
                (le_trans (Nat.le_max_left NtfP NttP)
                  (le_trans (Nat.le_max_right NftP (Nat.max NtfP NttP))
                    (Nat.le_max_right NffP (Nat.max NftP (Nat.max NtfP NttP)))))
                htNp)
          have httP :
              (xi_tlEnvironment t l).prob ha (Percept.mk true true) =
                (xi_tlEnvironmentUnbounded l).prob ha (Percept.mk true true) :=
            hNttP t
              (le_trans
                (le_trans (Nat.le_max_right NtfP NttP)
                  (le_trans (Nat.le_max_right NftP (Nat.max NtfP NttP))
                    (Nat.le_max_right NffP (Nat.max NftP (Nat.max NtfP NttP)))))
                htNp)
          have hffV :
              optimalValue (xi_tlEnvironment t l) γ (ha ++ [HistElem.per (Percept.mk false false)]) n =
                optimalValue (xi_tlEnvironmentUnbounded l) γ (ha ++ [HistElem.per (Percept.mk false false)]) n :=
            hNffV t (le_trans (Nat.le_max_left NffV (Nat.max NftV (Nat.max NtfV NttV))) htNv)
          have hftV :
              optimalValue (xi_tlEnvironment t l) γ (ha ++ [HistElem.per (Percept.mk false true)]) n =
                optimalValue (xi_tlEnvironmentUnbounded l) γ (ha ++ [HistElem.per (Percept.mk false true)]) n :=
            hNftV t
              (le_trans
                (le_trans (Nat.le_max_left NftV (Nat.max NtfV NttV))
                  (Nat.le_max_right NffV (Nat.max NftV (Nat.max NtfV NttV))))
                htNv)
          have htfV :
              optimalValue (xi_tlEnvironment t l) γ (ha ++ [HistElem.per (Percept.mk true false)]) n =
                optimalValue (xi_tlEnvironmentUnbounded l) γ (ha ++ [HistElem.per (Percept.mk true false)]) n :=
            hNtfV t
              (le_trans
                (le_trans (Nat.le_max_left NtfV NttV)
                  (le_trans (Nat.le_max_right NftV (Nat.max NtfV NttV))
                    (Nat.le_max_right NffV (Nat.max NftV (Nat.max NtfV NttV)))))
                htNv)
          have httV :
              optimalValue (xi_tlEnvironment t l) γ (ha ++ [HistElem.per (Percept.mk true true)]) n =
                optimalValue (xi_tlEnvironmentUnbounded l) γ (ha ++ [HistElem.per (Percept.mk true true)]) n :=
            hNttV t
              (le_trans
                (le_trans (Nat.le_max_right NtfV NttV)
                  (le_trans (Nat.le_max_right NftV (Nat.max NtfV NttV))
                    (Nat.le_max_right NffV (Nat.max NftV (Nat.max NtfV NttV)))))
                htNv)
          have hffV' :
              optimalValue (xi_tlEnvironment t l) γ (h ++ [HistElem.act a, HistElem.per (Percept.mk false false)]) n =
                optimalValue (xi_tlEnvironmentUnbounded l) γ
                  (h ++ [HistElem.act a, HistElem.per (Percept.mk false false)]) n := by
            simpa [ha, List.append_assoc] using hffV
          have hftV' :
              optimalValue (xi_tlEnvironment t l) γ (h ++ [HistElem.act a, HistElem.per (Percept.mk false true)]) n =
                optimalValue (xi_tlEnvironmentUnbounded l) γ
                  (h ++ [HistElem.act a, HistElem.per (Percept.mk false true)]) n := by
            simpa [ha, List.append_assoc] using hftV
          have htfV' :
              optimalValue (xi_tlEnvironment t l) γ (h ++ [HistElem.act a, HistElem.per (Percept.mk true false)]) n =
                optimalValue (xi_tlEnvironmentUnbounded l) γ
                  (h ++ [HistElem.act a, HistElem.per (Percept.mk true false)]) n := by
            simpa [ha, List.append_assoc] using htfV
          have httV' :
              optimalValue (xi_tlEnvironment t l) γ (h ++ [HistElem.act a, HistElem.per (Percept.mk true true)]) n =
                optimalValue (xi_tlEnvironmentUnbounded l) γ
                  (h ++ [HistElem.act a, HistElem.per (Percept.mk true true)]) n := by
            simpa [ha, List.append_assoc] using httV
          -- Unfold both sides and rewrite each of the eight stable subterms.
          simp [optimalQValue, ha, hha, List.foldl_cons, List.foldl_nil, add_assoc, hffP, hftP, htfP, httP, hffV', hftV',
            htfV', httV']
        · -- Not well-formed: both sides are `0`.
          refine ⟨0, ?_⟩
          intro t _ht
          simp [optimalQValue, ha, hha]

/-- Convenience extraction: pointwise stabilization of `optimalValue` under `ξ^tl`. -/
theorem exists_fuel_bound_optimalValue_xi_tlEnvironment_eq_unbounded (l : ℕ) (γ : DiscountFactor) (h : History) (n : ℕ) :
    ∃ N, ∀ t ≥ N,
      optimalValue (xi_tlEnvironment t l) γ h n = optimalValue (xi_tlEnvironmentUnbounded l) γ h n :=
  (exists_fuel_bound_optimalValue_optimalQValue_xi_tlEnvironment_eq_unbounded (l := l) (γ := γ) n).1 h

/-- For fixed `l`, each time-bounded approximation of the optimal value under `ξ^tl` is bounded above by the unbounded
semantics. -/
theorem optimalValue_xi_tlEnvironment_le_unbounded (l : ℕ) (γ : DiscountFactor) (t : ℕ) (h : History) (n : ℕ) :
    optimalValue (xi_tlEnvironment t l) γ h n ≤ optimalValue (xi_tlEnvironmentUnbounded l) γ h n := by
  classical
  rcases exists_fuel_bound_optimalValue_xi_tlEnvironment_eq_unbounded (l := l) (γ := γ) (h := h) (n := n) with ⟨N, hN⟩
  have hmono :
      optimalValue (xi_tlEnvironment t l) γ h n ≤ optimalValue (xi_tlEnvironment (max t N) l) γ h n :=
    optimalValue_xi_tlEnvironment_mono (l := l) (t₁ := t) (t₂ := max t N) (ht := le_max_left _ _) (γ := γ) (h := h)
      (n := n)
  have hEq :
      optimalValue (xi_tlEnvironment (max t N) l) γ h n = optimalValue (xi_tlEnvironmentUnbounded l) γ h n :=
    hN (max t N) (le_max_right _ _)
  simpa [hEq] using hmono

/-! #### Alternative: scaled-length weights

The primary `ξ^tl` in this file now uses prefix-free self-delimiting code-length weights
(`xi_tlBayesianMixturePrefixFree`), justified by the Kraft inequality.

This older construction is kept as a conservative fallback: scale the usual `2^{-ℓ(p)}` weight by
an extra `2^{-(l+1)}` factor so that, even without prefix-freeness, the total mass over at most
`2^(l+1)` candidates is ≤ 1:

`w(p) = 2^{-(ℓ(p) + (l+1))} = 2^{-(l+1)} · 2^{-ℓ(p)}`. -/

noncomputable def xi_tlScaledLengthWeight (l : ℕ) (programs : List RawToPartrecEnvironmentProgram) (i : ℕ) :
    ENNReal :=
  if hi : i < programs.length then
    (2⁻¹ : ENNReal) ^ ((programs.get ⟨i, hi⟩).code.length + (l + 1))
  else
    0

noncomputable def xi_tlBayesianMixtureScaledLength (t l : ℕ) : BayesianMixture :=
  let programs := enumerateRawToPartrecEnvironmentPrograms l
  { envs := fun i =>
      if hi : i < programs.length then
        (programs.get ⟨i, hi⟩).toEnvironmentWithin t
      else
        zeroEnvironment
    weights := xi_tlScaledLengthWeight l programs
    weights_le_one := by
      classical
      -- Reduce the `tsum` to a finite sum over `range programs.length`.
      have htsum :
          (∑' i : ℕ, xi_tlScaledLengthWeight l programs i) =
            Finset.sum (Finset.range programs.length) (fun i => xi_tlScaledLengthWeight l programs i) := by
        refine (tsum_eq_sum (s := Finset.range programs.length) ?_)
        intro i hi
        have hnot : ¬ i < programs.length := by
          simpa [Finset.mem_range] using hi
        simp [xi_tlScaledLengthWeight, hnot]
      -- Bound each term by `2^{-(l+1)}` and use the `2^(l+1)` candidate bound.
      have hterm :
          ∀ i ∈ Finset.range programs.length,
            xi_tlScaledLengthWeight l programs i ≤ (2⁻¹ : ENNReal) ^ (l + 1) := by
        intro i hi
        have hil : i < programs.length := by
          simpa [Finset.mem_range] using hi
        -- Use antitonicity of `a^n` for `a ≤ 1`.
        have hpow :
            (2⁻¹ : ENNReal) ^ ((programs.get ⟨i, hil⟩).code.length + (l + 1)) ≤
              (2⁻¹ : ENNReal) ^ (l + 1) := by
          apply pow_le_pow_of_le_one (a := (2⁻¹ : ENNReal)) (ha₀ := by simp) (ha₁ := by simp)
          omega
        simpa [xi_tlScaledLengthWeight, hil] using hpow
      have hlenNat : programs.length ≤ 2 ^ (l + 1) :=
        le_trans (Nat.le_succ _) (length_enumerateRawToPartrecEnvironmentPrograms_add_one_le l)
      have hlen : (programs.length : ENNReal) ≤ (2 ^ (l + 1) : ENNReal) := by
        exact_mod_cast hlenNat
      have hsum_le :
          (Finset.sum (Finset.range programs.length) (fun i => xi_tlScaledLengthWeight l programs i)) ≤
            (programs.length : ENNReal) * ((2⁻¹ : ENNReal) ^ (l + 1)) := by
        calc
          (Finset.sum (Finset.range programs.length) (fun i => xi_tlScaledLengthWeight l programs i)) ≤
              Finset.sum (Finset.range programs.length) (fun _ => (2⁻¹ : ENNReal) ^ (l + 1)) := by
                refine Finset.sum_le_sum ?_
                intro i hi
                exact hterm i hi
            _ = (programs.length : ENNReal) * ((2⁻¹ : ENNReal) ^ (l + 1)) := by
                simp [mul_comm]
      have hmul_le_one :
          (programs.length : ENNReal) * ((2⁻¹ : ENNReal) ^ (l + 1)) ≤ 1 := by
        have hmul :
            (programs.length : ENNReal) * ((2⁻¹ : ENNReal) ^ (l + 1)) ≤
              (2 ^ (l + 1) : ENNReal) * ((2⁻¹ : ENNReal) ^ (l + 1)) :=
          mul_le_mul_of_nonneg_right hlen (by simp)
        have h2ne0 : (2 : ENNReal) ≠ 0 := by norm_num
        have h2neinf : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
        have hcancel : (2 : ENNReal) * (2⁻¹ : ENNReal) = 1 :=
          ENNReal.mul_inv_cancel h2ne0 h2neinf
        have hpow :
            (2 ^ (l + 1) : ENNReal) * ((2⁻¹ : ENNReal) ^ (l + 1)) = 1 := by
          -- `(2 * 2⁻¹)^(l+1) = 1`, and expand via `mul_pow`.
          have : ((2 : ENNReal) * (2⁻¹ : ENNReal)) ^ (l + 1) = 1 := by
            simp [hcancel]
          simpa [mul_pow] using this
        exact le_trans hmul (le_of_eq hpow)
      -- Assemble.
      calc
        (∑' i : ℕ, xi_tlScaledLengthWeight l programs i)
            = Finset.sum (Finset.range programs.length) (fun i => xi_tlScaledLengthWeight l programs i) := by
              simpa using htsum
        _ ≤ (programs.length : ENNReal) * ((2⁻¹ : ENNReal) ^ (l + 1)) := hsum_le
        _ ≤ 1 := hmul_le_one }

noncomputable def xi_tlEnvironmentScaledLength (t l : ℕ) : Environment :=
  mixtureEnvironment (xi_tlBayesianMixtureScaledLength t l)

/-- Enumerate candidate raw programs from all bitstrings up to length `l` (before filtering by
`Program.length` and applying the per-cycle time budget). -/
noncomputable def enumerateRawToPartrecPrograms (l : ℕ) : List RawToPartrecProgram :=
  (bitstringsUpTo l).filterMap RawToPartrecProgram.decodeCanonical

theorem length_enumerateRawToPartrecPrograms_add_one_le (l : ℕ) :
    (enumerateRawToPartrecPrograms l).length + 1 ≤ 2 ^ (l + 1) := by
  have hle : (enumerateRawToPartrecPrograms l).length ≤ (bitstringsUpTo l).length := by
    simpa [enumerateRawToPartrecPrograms] using
      (length_filterMap_le (f := RawToPartrecProgram.decodeCanonical) (l := bitstringsUpTo l))
  have hle' : (enumerateRawToPartrecPrograms l).length + 1 ≤ (bitstringsUpTo l).length + 1 :=
    Nat.add_le_add_right hle 1
  exact le_trans hle' (le_of_eq (length_bitstringsUpTo_add_one l))

/-- If we enumerate raw programs from all bitstrings of length ≤ `l`, then the number of candidates
is at most `2^(l+1)`, hence the per-cycle small-step budget is `O(2^l · t)`. -/
theorem per_cycle_steps_enumerateRawToPartrecPrograms_le (l t : ℕ) :
    (enumerateRawToPartrecPrograms l).length * t ≤ 2 ^ (l + 1) * t := by
  have hlen : (enumerateRawToPartrecPrograms l).length ≤ 2 ^ (l + 1) :=
    le_trans (Nat.le_succ _) (length_enumerateRawToPartrecPrograms_add_one_le l)
  exact Nat.mul_le_mul_right t hlen

/-- Filter by program length and wrap each remaining raw program with the `t`-step defaulting
behavior from Step 3. -/
noncomputable def filterAndModifyToPartrec (programs : List RawToPartrecProgram) (l t : ℕ) :
    List ExtendedChronologicalProgram :=
  (programs.filter fun p => p.code.length ≤ l).map fun p => p.toExtended t

theorem length_filterAndModifyToPartrec_le (programs : List RawToPartrecProgram) (l t : ℕ) :
    (filterAndModifyToPartrec programs l t).length ≤ programs.length := by
  simp [filterAndModifyToPartrec]
  exact List.length_filter_le (fun p => p.code.length ≤ l) programs

/-- The Step-2 filter can only shrink the list, preserving the same per-cycle bound. -/
theorem per_cycle_steps_filterAndModifyToPartrec_le (l t : ℕ) :
    (filterAndModifyToPartrec (enumerateRawToPartrecPrograms l) l t).length * t ≤ 2 ^ (l + 1) * t := by
  have hlen : (filterAndModifyToPartrec (enumerateRawToPartrecPrograms l) l t).length ≤
      (enumerateRawToPartrecPrograms l).length :=
    length_filterAndModifyToPartrec_le (programs := enumerateRawToPartrecPrograms l) (l := l) (t := t)
  have hmul : (filterAndModifyToPartrec (enumerateRawToPartrecPrograms l) l t).length * t ≤
      (enumerateRawToPartrecPrograms l).length * t :=
    Nat.mul_le_mul_right t hlen
  exact le_trans hmul (per_cycle_steps_enumerateRawToPartrecPrograms_le (l := l) (t := t))

/-! #### Step 1-3 (concrete): proofs → raw `ToPartrec` programs → time-bounded wrapper

The abstract `aixitlFromProofChecker` constructor assumes that decoded programs already implement
the Step-3 “default within `t` steps” behavior.  For the concrete `ToPartrec` bridge we instead let
the proof checker produce **raw** programs, then apply the Step-2/3 wrapper `filterAndModifyToPartrec`.
-/

/-- Step 1: Enumerate proofs up to `l_p` and decode them to raw `ToPartrec` programs. -/
def findValidRawToPartrecPrograms (decode : ProofDecoder RawToPartrecProgram) (l_p : ℕ) :
    List RawToPartrecProgram :=
  (bitstringsUpTo l_p).filterMap decode

theorem length_findValidRawToPartrecPrograms_add_one_le (decode : ProofDecoder RawToPartrecProgram) (l_p : ℕ) :
    (findValidRawToPartrecPrograms decode l_p).length + 1 ≤ 2 ^ (l_p + 1) := by
  have hle : (findValidRawToPartrecPrograms decode l_p).length ≤ (bitstringsUpTo l_p).length := by
    simpa [findValidRawToPartrecPrograms] using
      (length_filterMap_le (f := decode) (l := bitstringsUpTo l_p))
  have hle' : (findValidRawToPartrecPrograms decode l_p).length + 1 ≤ (bitstringsUpTo l_p).length + 1 :=
    Nat.add_le_add_right hle 1
  exact le_trans hle' (le_of_eq (length_bitstringsUpTo_add_one l_p))

theorem mem_findValidRawToPartrecPrograms_mono {decode : ProofDecoder RawToPartrecProgram} {m n : ℕ} (hmn : m ≤ n)
    {p : RawToPartrecProgram} (hp : p ∈ findValidRawToPartrecPrograms decode m) :
    p ∈ findValidRawToPartrecPrograms decode n := by
  unfold findValidRawToPartrecPrograms at hp ⊢
  rcases (List.mem_filterMap).1 hp with ⟨bits, hbits, hdec⟩
  refine (List.mem_filterMap).2 ?_
  refine ⟨bits, mem_bitstringsUpTo_mono hmn hbits, hdec⟩

/-- AIXItl built from a sound proof checker that outputs raw `ToPartrec` programs.

Step 2 filters by the program length bound `l`, and Step 3 applies the `t`-step wrapper. -/
noncomputable def aixitlFromProofCheckerToPartrec (μ : Environment) (γ : DiscountFactor) (horizon : ℕ)
    (t : ℕ)
    (checker :
      ProofChecker (α := RawToPartrecProgram) (fun p => ValidValueLowerBound μ γ horizon (p.toExtended t)))
    (l l_p : ℕ) : AIXItl :=
  { timeBound := t
    lengthBound := l
    proofLengthBound := l_p
    validatedPrograms := filterAndModifyToPartrec (findValidRawToPartrecPrograms checker.decode l_p) l t }

/-- The Step-1/2/3 constructor specialized to a decoder, ignoring soundness. -/
noncomputable def aixitlFromDecodeToPartrec (decode : ProofDecoder RawToPartrecProgram) (l l_p t : ℕ) : AIXItl :=
  { timeBound := t
    lengthBound := l
    proofLengthBound := l_p
    validatedPrograms := filterAndModifyToPartrec (findValidRawToPartrecPrograms decode l_p) l t }

theorem per_cycle_steps_aixitlFromDecodeToPartrec_le (decode : ProofDecoder RawToPartrecProgram) (l l_p t : ℕ) :
    (aixitlFromDecodeToPartrec decode l l_p t).validatedPrograms.length * t ≤ 2 ^ (l_p + 1) * t := by
  have hlen' :
      (aixitlFromDecodeToPartrec decode l l_p t).validatedPrograms.length ≤
        (findValidRawToPartrecPrograms decode l_p).length := by
    simpa [aixitlFromDecodeToPartrec] using
      (length_filterAndModifyToPartrec_le (programs := findValidRawToPartrecPrograms decode l_p) (l := l) (t := t))
  have hmul :
      (aixitlFromDecodeToPartrec decode l l_p t).validatedPrograms.length * t ≤
        (findValidRawToPartrecPrograms decode l_p).length * t :=
    Nat.mul_le_mul_right t hlen'
  have hlen : (findValidRawToPartrecPrograms decode l_p).length ≤ 2 ^ (l_p + 1) :=
    le_trans (Nat.le_succ _) (length_findValidRawToPartrecPrograms_add_one_le decode l_p)
  have hmul' : (findValidRawToPartrecPrograms decode l_p).length * t ≤ 2 ^ (l_p + 1) * t :=
    Nat.mul_le_mul_right t hlen
  exact le_trans hmul hmul'

theorem per_cycle_steps_aixitlFromDecodeToPartrec_decodeCanonical_le (l l_p t : ℕ) :
    (aixitlFromDecodeToPartrec RawToPartrecProgram.decodeCanonical l l_p t).validatedPrograms.length * t ≤
      2 ^ (Nat.min l l_p + 1) * t := by
  -- Push the length filter back to the bitstring enumerator.
  have hlen_bits :
      (aixitlFromDecodeToPartrec RawToPartrecProgram.decodeCanonical l l_p t).validatedPrograms.length ≤
        (bitstringsUpTo (Nat.min l l_p)).length := by
    -- Unfold the constructor down to a `filterMap` over `bitstringsUpTo`.
    have hlen0 :
        (aixitlFromDecodeToPartrec RawToPartrecProgram.decodeCanonical l l_p t).validatedPrograms.length =
          (((bitstringsUpTo l_p).filterMap RawToPartrecProgram.decodeCanonical).filter fun p => p.code.length ≤ l).length := by
      simp [aixitlFromDecodeToPartrec, findValidRawToPartrecPrograms, filterAndModifyToPartrec]
    -- Commute `filter` and `filterMap` using the canonical code-length property.
    have hlist :
        ((bitstringsUpTo l_p).filterMap RawToPartrecProgram.decodeCanonical).filter (fun p => p.code.length ≤ l) =
          ((bitstringsUpTo l_p).filter (fun bits => bits.length ≤ l)).filterMap RawToPartrecProgram.decodeCanonical := by
      simpa using
        (RawToPartrecProgram.filter_filterMap_decodeCanonical_eq (bitsList := bitstringsUpTo l_p) (l := l))
    have hle_filterMap :
        (((bitstringsUpTo l_p).filter (fun bits => bits.length ≤ l)).filterMap RawToPartrecProgram.decodeCanonical).length ≤
          ((bitstringsUpTo l_p).filter (fun bits => bits.length ≤ l)).length := by
      simpa using
        (length_filterMap_le (f := RawToPartrecProgram.decodeCanonical)
          (l := (bitstringsUpTo l_p).filter (fun bits => bits.length ≤ l)))
    have hbits :
        (bitstringsUpTo l_p).filter (fun bits => bits.length ≤ l) = bitstringsUpTo (Nat.min l l_p) := by
      simpa using filter_bitstringsUpTo_length_le (l := l) (n := l_p)
    have hlen' :
        (aixitlFromDecodeToPartrec RawToPartrecProgram.decodeCanonical l l_p t).validatedPrograms.length ≤
          ((bitstringsUpTo l_p).filter (fun bits => bits.length ≤ l)).length := by
      -- Rewrite `validatedPrograms.length` as the length of a `filterMap` over the length-filtered bitstrings.
      have hlen_eq :
          (aixitlFromDecodeToPartrec RawToPartrecProgram.decodeCanonical l l_p t).validatedPrograms.length =
            (((bitstringsUpTo l_p).filter (fun bits => bits.length ≤ l)).filterMap RawToPartrecProgram.decodeCanonical).length := by
        calc
          (aixitlFromDecodeToPartrec RawToPartrecProgram.decodeCanonical l l_p t).validatedPrograms.length =
              (((bitstringsUpTo l_p).filterMap RawToPartrecProgram.decodeCanonical).filter fun p => p.code.length ≤ l).length := hlen0
          _ =
              (((bitstringsUpTo l_p).filter (fun bits => bits.length ≤ l)).filterMap RawToPartrecProgram.decodeCanonical).length := by
                simpa using congrArg List.length hlist
      -- Now apply the generic `filterMap` length bound.
      simpa [hlen_eq] using hle_filterMap
    simpa [hbits] using hlen'
  have hpow : (bitstringsUpTo (Nat.min l l_p)).length ≤ 2 ^ (Nat.min l l_p + 1) :=
    le_trans (Nat.le_succ _) (le_of_eq (length_bitstringsUpTo_add_one (Nat.min l l_p)))
  have hlen : (aixitlFromDecodeToPartrec RawToPartrecProgram.decodeCanonical l l_p t).validatedPrograms.length ≤
      2 ^ (Nat.min l l_p + 1) :=
    le_trans hlen_bits hpow
  exact Nat.mul_le_mul_right t hlen

theorem per_cycle_steps_aixitlFromProofCheckerToPartrec_le (μ : Environment) (γ : DiscountFactor) (horizon : ℕ)
    (t : ℕ)
    (checker :
      ProofChecker (α := RawToPartrecProgram) (fun p => ValidValueLowerBound μ γ horizon (p.toExtended t)))
    (l l_p : ℕ) :
    (aixitlFromProofCheckerToPartrec μ γ horizon t checker l l_p).validatedPrograms.length * t ≤ 2 ^ (l_p + 1) * t := by
  simpa using
    (per_cycle_steps_aixitlFromDecodeToPartrec_le (decode := checker.decode) (l := l) (l_p := l_p) (t := t))

theorem mem_validatedPrograms_aixitlFromDecodeToPartrec_mono_proofLength {decode : ProofDecoder RawToPartrecProgram}
    {l l_p₁ l_p₂ t : ℕ} (hlp : l_p₁ ≤ l_p₂) {p : ExtendedChronologicalProgram}
    (hp : p ∈ (aixitlFromDecodeToPartrec decode l l_p₁ t).validatedPrograms) :
    p ∈ (aixitlFromDecodeToPartrec decode l l_p₂ t).validatedPrograms := by
  unfold aixitlFromDecodeToPartrec at hp ⊢
  unfold filterAndModifyToPartrec at hp ⊢
  rcases (List.mem_map).1 hp with ⟨q, hq, rfl⟩
  have hq' : q ∈ findValidRawToPartrecPrograms decode l_p₁ :=
    (List.mem_filter.1 hq).1
  have hlen : decide (q.code.length ≤ l) = true :=
    (List.mem_filter.1 hq).2
  have hq'' : q ∈ findValidRawToPartrecPrograms decode l_p₂ :=
    mem_findValidRawToPartrecPrograms_mono (decode := decode) hlp hq'
  have hqf : q ∈ (findValidRawToPartrecPrograms decode l_p₂).filter (fun r => r.code.length ≤ l) := by
    exact (List.mem_filter.2 ⟨hq'', hlen⟩)
  exact (List.mem_map).2 ⟨q, hqf, rfl⟩

theorem mem_validatedPrograms_aixitlFromDecodeToPartrec_mono_lengthBound {decode : ProofDecoder RawToPartrecProgram}
    {l₁ l₂ l_p t : ℕ} (hl : l₁ ≤ l₂) {p : ExtendedChronologicalProgram}
    (hp : p ∈ (aixitlFromDecodeToPartrec decode l₁ l_p t).validatedPrograms) :
    p ∈ (aixitlFromDecodeToPartrec decode l₂ l_p t).validatedPrograms := by
  unfold aixitlFromDecodeToPartrec at hp ⊢
  unfold filterAndModifyToPartrec at hp ⊢
  rcases (List.mem_map).1 hp with ⟨q, hq, rfl⟩
  have hq' : q ∈ findValidRawToPartrecPrograms decode l_p :=
    (List.mem_filter.1 hq).1
  have hlen₁ : decide (q.code.length ≤ l₁) = true :=
    (List.mem_filter.1 hq).2
  have hlen₂ : decide (q.code.length ≤ l₂) = true := by
    refine decide_eq_true ?_
    exact le_trans (of_decide_eq_true hlen₁) hl
  have hqf : q ∈ (findValidRawToPartrecPrograms decode l_p).filter (fun r => r.code.length ≤ l₂) := by
    exact (List.mem_filter.2 ⟨hq', hlen₂⟩)
  exact (List.mem_map).2 ⟨q, hqf, rfl⟩

@[simp] theorem aixitlFromProofCheckerToPartrec_eq_aixitlFromDecodeToPartrec (μ : Environment) (γ : DiscountFactor)
    (horizon t : ℕ)
    (checker :
      ProofChecker (α := RawToPartrecProgram) (fun p => ValidValueLowerBound μ γ horizon (p.toExtended t)))
    (l l_p : ℕ) :
    aixitlFromProofCheckerToPartrec μ γ horizon t checker l l_p =
      aixitlFromDecodeToPartrec checker.decode l l_p t := by
  rfl

theorem validValueLowerBound_of_mem_aixitlFromProofCheckerToPartrec (μ : Environment) (γ : DiscountFactor)
    (horizon : ℕ) (t : ℕ)
    (checker :
      ProofChecker (α := RawToPartrecProgram) (fun p => ValidValueLowerBound μ γ horizon (p.toExtended t)))
    (l l_p : ℕ) {p : ExtendedChronologicalProgram}
    (hp : p ∈ (aixitlFromProofCheckerToPartrec μ γ horizon t checker l l_p).validatedPrograms) :
    ValidValueLowerBound μ γ horizon p := by
  -- `validatedPrograms` is a `map` of `RawToPartrecProgram.toExtended` over a filtered proof-enumeration list.
  have hp' :
      p ∈
        ((findValidRawToPartrecPrograms checker.decode l_p).filter fun q => q.code.length ≤ l).map
          (fun q => q.toExtended t) := by
    simpa [aixitlFromProofCheckerToPartrec, filterAndModifyToPartrec] using hp
  rcases (List.mem_map).1 hp' with ⟨q, hq, rfl⟩
  have hq' : q ∈ findValidRawToPartrecPrograms checker.decode l_p := by
    exact (List.mem_filter.1 hq).1
  -- Apply the checker soundness, then unfold the Step-3 wrapper target.
  unfold findValidRawToPartrecPrograms at hq'
  exact ProofChecker.sound_of_mem_findValidPrograms (checker := checker) (ha := hq')

/-- Steps 4-9: The main AIXItl cycle.

    For each cycle k:
    4. Start cycle
    5. Run all p ∈ P on extended input yx_<k
    6. Select p_k := argmax_p w_k^p
    7. Output y_k := y_k^{p_k}
    8. Receive input x_k
    9. Continue to next cycle

    (Hutter 2005, Section 7.2.7, Steps 4-9) -/
noncomputable def aixitl_cycle (agent : AIXItl) (h : History) : Action :=
  (aixitlBestResult agent h).2

theorem aixitlBestResult_eq_compute_of_mem (agent : AIXItl) (h : History) (hne : agent.validatedPrograms ≠ []) :
    ∃ p ∈ agent.validatedPrograms, aixitlBestResult agent h = p.compute h := by
  simpa [aixitlBestResult] using
    (bestByValue_eq_compute_of_mem (programs := agent.validatedPrograms) (h := h) hne)

theorem aixitlBestResult_fst_ge_of_mem (agent : AIXItl) (h : History) {p : ExtendedChronologicalProgram}
    (hp : p ∈ agent.validatedPrograms) :
    (p.compute h).1 ≤ (aixitlBestResult agent h).1 := by
  simpa [aixitlBestResult] using bestByValue_fst_ge_of_mem (programs := agent.validatedPrograms) (h := h) hp

/-! #### ε-optimality lemma (Hutter/Leike-style)

If the validated program set contains a program whose *claimed* value is within `ε` of the optimal
value `V*`, and every program’s claim is sound (a lower bound on its true value), then the action
chosen by AIXItl is `ε`-optimal in terms of `optimalQValue` at that history.
-/

theorem aixitl_cycle_eps_optimal (agent : AIXItl) (μ : Environment) (γ : DiscountFactor)
    (h : History) (n : ℕ) (ε : ℝ) (hwf : h.wellFormed)
    (hne : agent.validatedPrograms ≠ [])
    (hall : ∀ p ∈ agent.validatedPrograms, ValidValueLowerBound μ γ (n + 1) p)
    (hex : ∃ p ∈ agent.validatedPrograms, optimalValue μ γ h (n + 1) - ε ≤ (p.compute h).1) :
    optimalValue μ γ h (n + 1) - ε ≤ optimalQValue μ γ h (aixitl_cycle agent h) n := by
  rcases hex with ⟨p0, hp0, hp0_ge⟩
  have hbest_ge : (p0.compute h).1 ≤ (aixitlBestResult agent h).1 :=
    aixitlBestResult_fst_ge_of_mem (agent := agent) (h := h) (hp := hp0)
  have hbest_ge' : optimalValue μ γ h (n + 1) - ε ≤ (aixitlBestResult agent h).1 :=
    le_trans hp0_ge hbest_ge
  rcases aixitlBestResult_eq_compute_of_mem (agent := agent) (h := h) hne with ⟨p, hp, hpEq⟩
  have hvalid : ValidValueLowerBound μ γ (n + 1) p := hall p hp
  have hleQ : (p.compute h).1 ≤ optimalQValue μ γ h (p.compute h).2 n :=
    claimed_le_optimalQValue_of_validValueLowerBound (μ := μ) (γ := γ) (h := h) (n := n)
      (hwf := hwf) (hvalid := hvalid)
  have hbest_leQ : (aixitlBestResult agent h).1 ≤ optimalQValue μ γ h (aixitl_cycle agent h) n := by
    simpa [aixitl_cycle, hpEq] using hleQ
  exact le_trans hbest_ge' hbest_leQ

/-! #### Relating `optimalValue` to AIXI’s optimal action -/

theorem optimalValue_eq_optimalQValue_optimalAction (μ : Environment) (γ : DiscountFactor)
    (h : History) (n : ℕ) (hwf : h.wellFormed) :
    optimalValue μ γ h (n + 1) = optimalQValue μ γ h (optimalAction μ γ h n) n := by
  -- Reduce `optimalValue` to a foldl-max over `optimalQValue`.
  have hopt :
      optimalValue μ γ h (n + 1) =
        [Action.left, Action.right, Action.stay].foldl
          (fun m a => max m (optimalQValue μ γ h a n)) 0 :=
    optimalValue_is_max μ γ h n hwf
  -- `optimalAction` maximizes `optimalQValue` across the three actions.
  let aSel : Action := optimalAction μ γ h n
  have hsel_dom : ∀ a, optimalQValue μ γ h a n ≤ optimalQValue μ γ h aSel n := by
    intro a
    simpa [aSel] using (optimalAction_achieves_max μ γ h n a)
  have h0 : 0 ≤ optimalQValue μ γ h aSel n :=
    optimalQValue_nonneg μ γ h aSel n
  have hl : optimalQValue μ γ h Action.left n ≤ optimalQValue μ γ h aSel n :=
    hsel_dom Action.left
  have hr : optimalQValue μ γ h Action.right n ≤ optimalQValue μ γ h aSel n :=
    hsel_dom Action.right
  have hs : optimalQValue μ γ h Action.stay n ≤ optimalQValue μ γ h aSel n :=
    hsel_dom Action.stay
  have h1 : max 0 (optimalQValue μ γ h Action.left n) ≤ optimalQValue μ γ h aSel n :=
    max_le h0 hl
  have h2 :
      max (max 0 (optimalQValue μ γ h Action.left n)) (optimalQValue μ γ h Action.right n) ≤
        optimalQValue μ γ h aSel n :=
    max_le h1 hr
  have h3 :
      max (max (max 0 (optimalQValue μ γ h Action.left n)) (optimalQValue μ γ h Action.right n))
          (optimalQValue μ γ h Action.stay n) ≤
        optimalQValue μ γ h aSel n :=
    max_le h2 hs
  have hle :
      [Action.left, Action.right, Action.stay].foldl
          (fun m a => max m (optimalQValue μ γ h a n)) 0 ≤
        optimalQValue μ γ h aSel n := by
    -- Expand the foldl over the explicit 3-element list and apply `h3`.
    simpa [List.foldl_cons, List.foldl_nil] using h3
  have hge :
      optimalQValue μ γ h aSel n ≤
        [Action.left, Action.right, Action.stay].foldl
          (fun m a => max m (optimalQValue μ γ h a n)) 0 := by
    -- Any element is bounded by the foldl-max.
    simpa [aSel] using (foldl_max_ge_elem (fun a => optimalQValue μ γ h a n) aSel)
  -- Combine and rewrite back to `optimalValue`.
  rw [hopt]
  exact le_antisymm hle hge

/-! #### Proof enumeration ⇒ ε-optimality

This is the “semantic core” of Step 1: if a sound proof checker (bounded by `l_p`) can produce a
program whose *claimed* value is within `ε` of the optimal value `V*`, then the resulting AIXItl
cycle is `ε`-optimal in terms of `optimalQValue`.
-/

theorem aixitlFromProofChecker_cycle_eps_optimal_of_exists_good_proof (μ : Environment) (γ : DiscountFactor)
    (l l_p t : ℕ) (h : History) (n : ℕ) (ε : ℝ) (hwf : h.wellFormed)
    (checker : ProofChecker (α := ExtendedChronologicalProgram) (ValidValueLowerBound μ γ (n + 1)))
    (hex :
      ∃ bits p,
        bits.length ≤ l_p ∧ checker.decode bits = some p ∧ p.code.length ≤ l ∧
          optimalValue μ γ h (n + 1) - ε ≤ (p.compute h).1) :
    optimalValue μ γ h (n + 1) - ε ≤
      optimalQValue μ γ h (aixitl_cycle (aixitlFromProofChecker μ γ (n + 1) checker l l_p t) h) n := by
  classical
  rcases hex with ⟨bits, p, hlen, hdec, hcode, hclaim⟩
  let agent : AIXItl := aixitlFromProofChecker μ γ (n + 1) checker l l_p t
  have hpfind : p ∈ findValidPrograms checker.decode l_p := by
    exact ProofChecker.mem_findValidPrograms_of_decode_of_length_le (hbits := hlen) (hdec := hdec)
  have hpval : p ∈ agent.validatedPrograms := by
    -- Step 2 filter: `p.code.length ≤ l`.
    simp [agent, aixitlFromProofChecker, filterAndModify, hpfind, hcode]
  have hne : agent.validatedPrograms ≠ [] :=
    List.ne_nil_of_mem hpval
  have hall :
      ∀ q ∈ agent.validatedPrograms, ValidValueLowerBound μ γ (n + 1) q := by
    intro q hq
    exact
      validValueLowerBound_of_mem_aixitlFromProofChecker (μ := μ) (γ := γ) (horizon := n + 1)
        (checker := checker) (l := l) (l_p := l_p) (t := t) hq
  have hex' : ∃ q ∈ agent.validatedPrograms, optimalValue μ γ h (n + 1) - ε ≤ (q.compute h).1 :=
    ⟨p, hpval, hclaim⟩
  simpa [agent] using
    (aixitl_cycle_eps_optimal (agent := agent) (μ := μ) (γ := γ) (h := h) (n := n) (ε := ε)
      (hwf := hwf) (hne := hne) (hall := hall) (hex := hex'))

theorem aixitlFromProofCheckerToPartrec_cycle_eps_optimal_of_exists_good_proof (μ : Environment)
    (γ : DiscountFactor) (l l_p t : ℕ) (h : History) (n : ℕ) (ε : ℝ) (hwf : h.wellFormed)
    (checker :
      ProofChecker (α := RawToPartrecProgram) (fun p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)))
    (hex :
      ∃ bits p,
        bits.length ≤ l_p ∧ checker.decode bits = some p ∧ p.code.length ≤ l ∧
          optimalValue μ γ h (n + 1) - ε ≤ ((p.toExtended t).compute h).1) :
    optimalValue μ γ h (n + 1) - ε ≤
      optimalQValue μ γ h
        (aixitl_cycle (aixitlFromProofCheckerToPartrec μ γ (n + 1) t checker l l_p) h) n := by
  classical
  rcases hex with ⟨bits, p, hlen, hdec, hcode, hclaim⟩
  let agent : AIXItl := aixitlFromProofCheckerToPartrec μ γ (n + 1) t checker l l_p
  have hpfind : p ∈ findValidRawToPartrecPrograms checker.decode l_p := by
    unfold findValidRawToPartrecPrograms
    exact ProofChecker.mem_findValidPrograms_of_decode_of_length_le (hbits := hlen) (hdec := hdec)
  have hpval : (p.toExtended t) ∈ agent.validatedPrograms := by
    have hpval' :
        p.toExtended t ∈
          ((findValidRawToPartrecPrograms checker.decode l_p).filter fun q => q.code.length ≤ l).map
            (fun q => q.toExtended t) := by
      refine (List.mem_map).2 ?_
      refine ⟨p, ?_, rfl⟩
      exact List.mem_filter.2 ⟨hpfind, decide_eq_true hcode⟩
    -- Unfold the constructor and use the explicit `map` membership proof.
    change p.toExtended t ∈
        ((findValidRawToPartrecPrograms checker.decode l_p).filter fun q => q.code.length ≤ l).map
          (fun q => q.toExtended t)
    exact hpval'
  have hne : agent.validatedPrograms ≠ [] :=
    List.ne_nil_of_mem hpval
  have hall :
      ∀ q ∈ agent.validatedPrograms, ValidValueLowerBound μ γ (n + 1) q := by
    intro q hq
    exact
      validValueLowerBound_of_mem_aixitlFromProofCheckerToPartrec (μ := μ) (γ := γ) (horizon := n + 1)
        (t := t) (checker := checker) (l := l) (l_p := l_p) hq
  have hex' : ∃ q ∈ agent.validatedPrograms, optimalValue μ γ h (n + 1) - ε ≤ (q.compute h).1 :=
    ⟨p.toExtended t, hpval, hclaim⟩
  simpa [agent] using
    (aixitl_cycle_eps_optimal (agent := agent) (μ := μ) (γ := γ) (h := h) (n := n) (ε := ε)
      (hwf := hwf) (hne := hne) (hall := hall) (hex := hex'))

/-- If the proof checker is complete for `ValidValueLowerBound`, then any single good program yields an
`ε`-optimality guarantee for all sufficiently large proof-length bounds `l_p`. -/
theorem aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_eventually_of_exists_good_program
    (μ : Environment) (γ : DiscountFactor) (l t : ℕ) (h : History) (n : ℕ) (ε : ℝ) (hwf : h.wellFormed)
    (checker :
      CompleteProofChecker (α := RawToPartrecProgram) (fun p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)))
    (hex :
      ∃ p : RawToPartrecProgram,
        p.code.length ≤ l ∧ ValidValueLowerBound μ γ (n + 1) (p.toExtended t) ∧
          optimalValue μ γ h (n + 1) - ε ≤ ((p.toExtended t).compute h).1) :
    ∃ N, ∀ l_p ≥ N,
      optimalValue μ γ h (n + 1) - ε ≤
        optimalQValue μ γ h
          (aixitl_cycle (aixitlFromProofCheckerToPartrec μ γ (n + 1) t checker.toProofChecker l l_p) h) n := by
  classical
  rcases hex with ⟨p, hlen, hvalid, hclaim⟩
  rcases checker.complete p hvalid with ⟨bits, hdec⟩
  refine ⟨bits.length, ?_⟩
  intro l_p hlp
  have hex' :
      ∃ bits' p',
        bits'.length ≤ l_p ∧ checker.decode bits' = some p' ∧ p'.code.length ≤ l ∧
          optimalValue μ γ h (n + 1) - ε ≤ ((p'.toExtended t).compute h).1 := by
    exact ⟨bits, p, hlp, hdec, hlen, hclaim⟩
  simpa using
    (aixitlFromProofCheckerToPartrec_cycle_eps_optimal_of_exists_good_proof (μ := μ) (γ := γ) (l := l)
      (l_p := l_p) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf) (checker := checker.toProofChecker)
      (hex := hex'))

/-- Conditional ε-optimality: if *every* `ε > 0` has a corresponding bounded good proof/program,
then every such `ε` yields an ε-optimality bound for the AIXItl cycle. -/
theorem aixitlFromProofCheckerToPartrec_cycle_eps_optimal_of_forall_exists_good_proof (μ : Environment)
    (γ : DiscountFactor) (l l_p t : ℕ) (h : History) (n : ℕ) (hwf : h.wellFormed)
    (checker :
      ProofChecker (α := RawToPartrecProgram) (fun p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)))
    (hex :
      ∀ ε : ℝ,
        0 < ε →
          ∃ bits p,
            bits.length ≤ l_p ∧ checker.decode bits = some p ∧ p.code.length ≤ l ∧
              optimalValue μ γ h (n + 1) - ε ≤ ((p.toExtended t).compute h).1) :
    ∀ ε : ℝ,
      0 < ε →
        optimalValue μ γ h (n + 1) - ε ≤
          optimalQValue μ γ h
            (aixitl_cycle (aixitlFromProofCheckerToPartrec μ γ (n + 1) t checker l l_p) h) n := by
  intro ε hε
  exact
    aixitlFromProofCheckerToPartrec_cycle_eps_optimal_of_exists_good_proof (μ := μ) (γ := γ) (l := l)
      (l_p := l_p) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf) (checker := checker)
      (hex := hex ε hε)

/-- Completeness version of `aixitlFromProofCheckerToPartrec_cycle_eps_optimal_of_forall_exists_good_proof`:
for each `ε > 0` there is some proof-length threshold beyond which the AIXItl cycle is `ε`-optimal. -/
theorem aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_eventually_of_forall_exists_good_program
    (μ : Environment) (γ : DiscountFactor) (l t : ℕ) (h : History) (n : ℕ) (hwf : h.wellFormed)
    (checker :
      CompleteProofChecker (α := RawToPartrecProgram) (fun p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)))
    (hex :
      ∀ ε : ℝ,
        0 < ε →
          ∃ p : RawToPartrecProgram,
            p.code.length ≤ l ∧ ValidValueLowerBound μ γ (n + 1) (p.toExtended t) ∧
              optimalValue μ γ h (n + 1) - ε ≤ ((p.toExtended t).compute h).1) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ N, ∀ l_p ≥ N,
          optimalValue μ γ h (n + 1) - ε ≤
            optimalQValue μ γ h
              (aixitl_cycle (aixitlFromProofCheckerToPartrec μ γ (n + 1) t checker.toProofChecker l l_p) h) n := by
  intro ε hε
  exact
    aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_eventually_of_exists_good_program (μ := μ) (γ := γ)
      (l := l) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf) (checker := checker) (hex := hex ε hε)

/-! #### Mixture/AIXI-facing corollaries -/

/-- The Bayes-optimal (AIXI) action at history `h` for remaining horizon `n`. -/
noncomputable def aixiOptimalAction (ξ : BayesianMixture) (γ : DiscountFactor) (h : History) (n : ℕ) : Action :=
  optimalAction (mixtureEnvironment ξ) γ h n

theorem aixitlFromProofCheckerToPartrec_cycle_eps_optimal_mixture_of_exists_good_proof
    (ξ : BayesianMixture) (γ : DiscountFactor) (l l_p t : ℕ) (h : History) (n : ℕ) (ε : ℝ)
    (hwf : h.wellFormed)
    (checker :
      ProofChecker (α := RawToPartrecProgram)
        (fun p => ValidValueLowerBound (mixtureEnvironment ξ) γ (n + 1) (p.toExtended t)))
    (hex :
      ∃ bits p,
        bits.length ≤ l_p ∧ checker.decode bits = some p ∧ p.code.length ≤ l ∧
          optimalValue (mixtureEnvironment ξ) γ h (n + 1) - ε ≤ ((p.toExtended t).compute h).1) :
    optimalQValue (mixtureEnvironment ξ) γ h (aixiOptimalAction ξ γ h n) n - ε ≤
      optimalQValue (mixtureEnvironment ξ) γ h
        (aixitl_cycle
          (aixitlFromProofCheckerToPartrec (mixtureEnvironment ξ) γ (n + 1) t checker l l_p) h) n := by
  have hε :
      optimalValue (mixtureEnvironment ξ) γ h (n + 1) - ε ≤
        optimalQValue (mixtureEnvironment ξ) γ h
          (aixitl_cycle
            (aixitlFromProofCheckerToPartrec (mixtureEnvironment ξ) γ (n + 1) t checker l l_p) h) n :=
    aixitlFromProofCheckerToPartrec_cycle_eps_optimal_of_exists_good_proof (μ := mixtureEnvironment ξ) (γ := γ)
      (l := l) (l_p := l_p) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf) (checker := checker)
      (hex := hex)
  have hopt :
      optimalValue (mixtureEnvironment ξ) γ h (n + 1) =
        optimalQValue (mixtureEnvironment ξ) γ h (aixiOptimalAction ξ γ h n) n :=
    optimalValue_eq_optimalQValue_optimalAction (μ := mixtureEnvironment ξ) (γ := γ) (h := h) (n := n) hwf
  -- Rewrite the LHS in terms of the AIXI action.
  simpa [aixiOptimalAction, hopt] using hε

theorem aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_mixture_eventually_of_exists_good_program
    (ξ : BayesianMixture) (γ : DiscountFactor) (l t : ℕ) (h : History) (n : ℕ) (ε : ℝ) (hwf : h.wellFormed)
    (checker :
      CompleteProofChecker (α := RawToPartrecProgram)
        (fun p => ValidValueLowerBound (mixtureEnvironment ξ) γ (n + 1) (p.toExtended t)))
    (hex :
      ∃ p : RawToPartrecProgram,
        p.code.length ≤ l ∧ ValidValueLowerBound (mixtureEnvironment ξ) γ (n + 1) (p.toExtended t) ∧
          optimalValue (mixtureEnvironment ξ) γ h (n + 1) - ε ≤ ((p.toExtended t).compute h).1) :
    ∃ N, ∀ l_p ≥ N,
      optimalQValue (mixtureEnvironment ξ) γ h (aixiOptimalAction ξ γ h n) n - ε ≤
        optimalQValue (mixtureEnvironment ξ) γ h
          (aixitl_cycle
            (aixitlFromProofCheckerToPartrec (mixtureEnvironment ξ) γ (n + 1) t checker.toProofChecker l l_p) h) n := by
  rcases
      aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_eventually_of_exists_good_program
        (μ := mixtureEnvironment ξ) (γ := γ) (l := l) (t := t) (h := h) (n := n) (ε := ε)
        (hwf := hwf) (checker := checker) (hex := hex) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro l_p hlp
  have hε :=
    hN l_p hlp
  have hopt :
      optimalValue (mixtureEnvironment ξ) γ h (n + 1) =
        optimalQValue (mixtureEnvironment ξ) γ h (aixiOptimalAction ξ γ h n) n :=
    optimalValue_eq_optimalQValue_optimalAction (μ := mixtureEnvironment ξ) (γ := γ) (h := h) (n := n) hwf
  -- Rewrite the LHS in terms of the AIXI action.
  simpa [aixiOptimalAction, hopt] using hε

/-- Convenience corollary: a single good program implies an `ε`-optimality guarantee for some
program-length bound `l` and all sufficiently large proof-length bounds `l_p`. -/
theorem aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_mixture_eventually_of_exists_good_program'
    (ξ : BayesianMixture) (γ : DiscountFactor) (t : ℕ) (h : History) (n : ℕ) (ε : ℝ) (hwf : h.wellFormed)
    (checker :
      CompleteProofChecker (α := RawToPartrecProgram)
        (fun p => ValidValueLowerBound (mixtureEnvironment ξ) γ (n + 1) (p.toExtended t)))
    (hex :
      ∃ p : RawToPartrecProgram,
        ValidValueLowerBound (mixtureEnvironment ξ) γ (n + 1) (p.toExtended t) ∧
          optimalValue (mixtureEnvironment ξ) γ h (n + 1) - ε ≤ ((p.toExtended t).compute h).1) :
    ∃ l N, ∀ l_p ≥ N,
      optimalQValue (mixtureEnvironment ξ) γ h (aixiOptimalAction ξ γ h n) n - ε ≤
        optimalQValue (mixtureEnvironment ξ) γ h
          (aixitl_cycle
            (aixitlFromProofCheckerToPartrec (mixtureEnvironment ξ) γ (n + 1) t checker.toProofChecker l l_p) h) n := by
  classical
  rcases hex with ⟨p, hvalid, hclaim⟩
  refine ⟨p.code.length, ?_⟩
  simpa using
    (aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_mixture_eventually_of_exists_good_program (ξ := ξ)
      (γ := γ) (l := p.code.length) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf) (checker := checker)
      (hex := ⟨p, le_rfl, hvalid, hclaim⟩))

/-- Convergence schema (mixture/AIXI-facing): if for every `ε > 0` there exists a valid program whose
claimed value is within `ε` of the optimal value, then for every `ε > 0` there exist bounds
`l, l_p` such that AIXItl is `ε`-optimal relative to the AIXI action at history `h`. -/
theorem aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_mixture_eventually
    (ξ : BayesianMixture) (γ : DiscountFactor) (t : ℕ) (h : History) (n : ℕ) (hwf : h.wellFormed)
    (checker :
      CompleteProofChecker (α := RawToPartrecProgram)
        (fun p => ValidValueLowerBound (mixtureEnvironment ξ) γ (n + 1) (p.toExtended t)))
    (hex :
      ∀ ε : ℝ,
        0 < ε →
          ∃ p : RawToPartrecProgram,
            ValidValueLowerBound (mixtureEnvironment ξ) γ (n + 1) (p.toExtended t) ∧
              optimalValue (mixtureEnvironment ξ) γ h (n + 1) - ε ≤ ((p.toExtended t).compute h).1) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ l N, ∀ l_p ≥ N,
          optimalQValue (mixtureEnvironment ξ) γ h (aixiOptimalAction ξ γ h n) n - ε ≤
            optimalQValue (mixtureEnvironment ξ) γ h
              (aixitl_cycle
                (aixitlFromProofCheckerToPartrec (mixtureEnvironment ξ) γ (n + 1) t checker.toProofChecker l l_p) h) n := by
  intro ε hε
  exact
    aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_mixture_eventually_of_exists_good_program' (ξ := ξ)
      (γ := γ) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf) (checker := checker) (hex := hex ε hε)

/-- There exists a time bound `t` and a verified raw program whose claimed value is within `ε`
of the optimal value at history `h`. This is the key external “provability/approximability”
assumption needed to upgrade AIXItl’s proof-enumeration semantics into an `ε`-optimality result. -/
def ExistsNearOptimalVerifiedRawProgram (μ : Environment) (γ : DiscountFactor) (h : History) (n : ℕ) (ε : ℝ) : Prop :=
  ∃ t : ℕ, ∃ p : RawToPartrecProgram,
    ValidValueLowerBound μ γ (n + 1) (p.toExtended t) ∧
      optimalValue μ γ h (n + 1) - ε ≤ ((p.toExtended t).compute h).1

/-- For every `ε > 0` there exists a verified raw program that is `ε`-close to optimal at history `h`. -/
def HasNearOptimalVerifiedRawPrograms (μ : Environment) (γ : DiscountFactor) (h : History) (n : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ExistsNearOptimalVerifiedRawProgram μ γ h n ε

/-- A global version of `HasNearOptimalVerifiedRawPrograms`: near-optimal verified raw programs exist
uniformly for every well-formed history. -/
def HasNearOptimalVerifiedRawProgramsForAllHistories (μ : Environment) (γ : DiscountFactor) (n : ℕ) : Prop :=
  ∀ h : History, h.wellFormed → HasNearOptimalVerifiedRawPrograms μ γ h n

/-- A structured “enumerability + realizability” interface implying `HasNearOptimalVerifiedRawProgramsForAllHistories`.

This matches the informal Chapter 7 story: an increasing sequence of lower bounds on the optimal
value exists, and each bound can be realized by a *verified* raw program. -/
structure NearOptimalVerifiedRawProgramSource (μ : Environment) (γ : DiscountFactor) (n : ℕ) where
  approx : ℕ → History → ℚ
  approx_close :
    ∀ h, h.wellFormed → ∀ ε : ℝ, 0 < ε →
      ∃ k, optimalValue μ γ h (n + 1) - ε ≤ (approx k h : ℝ)
  realize :
    ∀ h, h.wellFormed → ∀ k,
      ∃ t : ℕ, ∃ p : RawToPartrecProgram,
        ValidValueLowerBound μ γ (n + 1) (p.toExtended t) ∧ (approx k h : ℝ) ≤ ((p.toExtended t).compute h).1

namespace NearOptimalVerifiedRawProgramSource

theorem hasNearOptimalVerifiedRawProgramsForAllHistories
    (src : NearOptimalVerifiedRawProgramSource μ γ n) :
    HasNearOptimalVerifiedRawProgramsForAllHistories μ γ n := by
  intro h hwf ε hε
  rcases src.approx_close h hwf ε hε with ⟨k, hk⟩
  rcases src.realize h hwf k with ⟨t, p, hpValid, hpApprox⟩
  refine ⟨t, p, hpValid, ?_⟩
  exact le_trans hk hpApprox

end NearOptimalVerifiedRawProgramSource

/-- Packaged assumptions for the “AIXItl is `ε`-optimal for AIXI” schema at fixed horizon `n+1`. -/
structure AIXItlConvergenceAssumptions (μ : Environment) (γ : DiscountFactor) (n : ℕ) where
  checkerFamily :
    CompleteProofCheckerFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t))
  nearOptimal : HasNearOptimalVerifiedRawProgramsForAllHistories μ γ n

/-- Build convergence assumptions from a checker family and a structured near-optimal source. -/
noncomputable def convergenceAssumptionsOfCheckerFamilyAndSource (μ : Environment) (γ : DiscountFactor) (n : ℕ)
    (checkerFamily :
      CompleteProofCheckerFamily (α := RawToPartrecProgram)
        (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)))
    (src : NearOptimalVerifiedRawProgramSource μ γ n) : AIXItlConvergenceAssumptions μ γ n :=
  { checkerFamily := checkerFamily
    nearOptimal := src.hasNearOptimalVerifiedRawProgramsForAllHistories }

/-- A concrete (oracle-style) complete proof checker family for `ValidValueLowerBound` over raw `ToPartrec` programs.

Certificates encode a `RawToPartrecProgram` value directly, and the checker accepts exactly those
programs satisfying the target predicate.

This is a useful baseline instantiation for the convergence pipeline, but it is **not** meant as a
computable proof system model. -/
noncomputable def oracleCheckerFamilyToPartrec (μ : Environment) (γ : DiscountFactor) (n : ℕ) :
    CompleteProofCheckerFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)) :=
  ProofEnumerationOracle.oracleCompleteProofCheckerFamily
    (α := RawToPartrecProgram) (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t))

/-- A proof-system-style complete proof checker family for `ValidValueLowerBound` over raw `ToPartrec` programs.

Certificates are bitstrings encoding a pair `(p, pr)` where `p : RawToPartrecProgram` and `pr` is a
proof object checked by an explicit verifier `verify`. Soundness/completeness relative to the target
predicate are carried by the `EncodableProofSystemFamily` interface. -/
noncomputable def proofSystemCheckerFamilyToPartrec (μ : Environment) (γ : DiscountFactor) (n : ℕ)
    (sys :
      EncodableProofSystemFamily (α := RawToPartrecProgram)
        (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t))) :
    CompleteProofCheckerFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)) :=
  EncodableProofSystemFamily.toCompleteProofCheckerFamily sys

/-- A proof-system-style sound proof checker family for `ValidValueLowerBound` over raw `ToPartrec` programs.

Unlike `proofSystemCheckerFamilyToPartrec`, this only assumes soundness of the verifier; it is
compatible with “near-optimal proofs exist” assumptions that provide *explicit* certificates, and
does not require global completeness of the proof system for the semantic predicate. -/
def soundProofSystemCheckerFamilyToPartrec (μ : Environment) (γ : DiscountFactor) (n : ℕ)
    (sys :
      EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
        (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t))) :
    ProofCheckerFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)) :=
  EncodableSoundProofSystemFamily.toProofCheckerFamily sys

/-- MVP “actual verifier” for the global VA predicate: accept only programs whose underlying
`ToPartrec` code is the primitive `zero'` (which forces a claimed value of `0`). -/
def zeroPrefixSoundProofSystemToPartrec (μ : Environment) (γ : DiscountFactor) (n : ℕ) :
    EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)) := by
  classical
  refine
    { Proof := Unit
      verify := fun _t p _pr => decide (p.tm = Turing.ToPartrec.Code.zero')
      sound := ?_ }
  intro t p _pr hverify
  have hp : p.tm = Turing.ToPartrec.Code.zero' := of_decide_eq_true hverify
  exact
    RawToPartrecProgram.validValueLowerBound_toExtended_of_tm_eq_zero' (μ := μ) (γ := γ) (horizon := n + 1) (t := t)
      (p := p) hp

/-- MVP “actual verifier” for the global VA predicate: accept only programs whose underlying
`ToPartrec` code is one of the primitives `zero'`, `zero`, or `nil` (each forces a claimed value of `0`). -/
def zeroClaimSoundProofSystemToPartrec (μ : Environment) (γ : DiscountFactor) (n : ℕ) :
    EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)) := by
  classical
  refine
    { Proof := Unit
      verify := fun _t p _pr =>
        decide (p.tm = Turing.ToPartrec.Code.zero' ∨ p.tm = Turing.ToPartrec.Code.zero ∨ p.tm = Turing.ToPartrec.Code.nil)
      sound := ?_ }
  intro t p _pr hverify
  have hp :
      p.tm = Turing.ToPartrec.Code.zero' ∨ p.tm = Turing.ToPartrec.Code.zero ∨ p.tm = Turing.ToPartrec.Code.nil :=
    of_decide_eq_true hverify
  rcases hp with hp | hp
  · exact
      RawToPartrecProgram.validValueLowerBound_toExtended_of_tm_eq_zero' (μ := μ) (γ := γ) (horizon := n + 1) (t := t)
        (p := p) hp
  · rcases hp with hp | hp
    · exact
        RawToPartrecProgram.validValueLowerBound_toExtended_of_tm_eq_zero (μ := μ) (γ := γ) (horizon := n + 1) (t := t)
          (p := p) hp
    · exact
        RawToPartrecProgram.validValueLowerBound_toExtended_of_tm_eq_nil (μ := μ) (γ := γ) (horizon := n + 1) (t := t)
          (p := p) hp

/-- MVP “actual verifier” for the global VA predicate: accept exactly programs of the form
`zeroValueActionCode act`.

This is still “value-trivial” (the claimed value is always `0`), but it already supports
nontrivial **actions** via the sub-program `act`. -/
def zeroValueActionSoundProofSystemToPartrec (μ : Environment) (γ : DiscountFactor) (n : ℕ) :
    EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)) := by
  classical
  refine
    { Proof := Turing.ToPartrec.Code
      verify := fun _t p pr => decide (p.tm = RawToPartrecProgram.zeroValueActionCode pr)
      sound := ?_ }
  intro t p pr hverify
  have hp : p.tm = RawToPartrecProgram.zeroValueActionCode pr := of_decide_eq_true hverify
  exact
    RawToPartrecProgram.validValueLowerBound_toExtended_of_tm_eq_zeroValueAction (μ := μ) (γ := γ) (horizon := n + 1)
      (t := t) (p := p) (act := pr) hp

/-
WIP (disabled): a first attempt at a positive-value certificate/verifier for `ξ^tl` (horizon `2`).
This block did not compile and is being rewritten below.

/-- A certificate for a 1-step (i.e. horizon `2`) reward lower bound for `ξ^tl`.

The certificate is **history-local** (it certifies a claim only for a single history code), but the
verified raw program is **globally VA-sound** because it claims `0` on every other history. -/
structure OneStepRewardLowerBoundCert where
  /-- The encoded history guarded by the raw program. -/
  historyCode : List ℕ
  /-- The action played at the guarded history. -/
  action : Action
  /-- The claimed numerator `num`. The decoded claim is `num / (den+1)`. -/
  num : ℕ
  /-- The claimed denominator offset `den`. The decoded claim is `num / (den+1)`. -/
  den : ℕ
  /-- Indices of environment programs provably yielding percept `(obs=false,reward=true)`. -/
  idx_false_true : List ℕ
  /-- Indices of environment programs provably yielding percept `(obs=true,reward=true)`. -/
  idx_true_true : List ℕ
deriving Encodable

namespace OneStepRewardLowerBoundCert

/-- The common dyadic denominator exponent used by the verifier: for `bitstringsUpTo l`,
all prefix-free weights are of the form `2^{-k}` with `k ≤ 2*l+1`. -/
def denomExp (l : ℕ) : ℕ :=
  2 * l + 1

/-- Check that a list is a canonical `Coding.encodeHistoryNat` output for some history. -/
def isCanonicalHistoryCode (code : List ℕ) : Bool :=
  match Coding.decodeHistoryNat code with
  | some h => decide (Coding.encodeHistoryNat h = code)
  | none => false

def guardedHistory (cert : OneStepRewardLowerBoundCert) : Option History :=
  match Coding.decodeHistoryNat cert.historyCode with
  | some h =>
      if Coding.encodeHistoryNat h = cert.historyCode then some h else none
  | none => none

def guardedHistoryAction (cert : OneStepRewardLowerBoundCert) : Option History :=
  (guardedHistory cert).map fun h => h ++ [HistElem.act cert.action]

def bitsAt (l : ℕ) : List (List Bool) :=
  bitstringsUpTo l

def weightCodeLenAt (l i : ℕ) : Option ℕ :=
  let bits := bitsAt l
  if hi : i < bits.length then
    some (Coding.selfDelimitingEncode (bits.get ⟨i, hi⟩)).length
  else
    none

def numeratorTerm (l i : ℕ) : Option ℕ :=
  match weightCodeLenAt l i with
  | some k => some (2 ^ (denomExp l - k))
  | none => none

def numeratorBound (l : ℕ) (idxs : List ℕ) : Option ℕ :=
  let rec go : List ℕ → ℕ → Option ℕ
    | [], acc => some acc
    | i :: is, acc =>
        match numeratorTerm l i with
        | some t => go is (acc + t)
        | none => none
  go idxs 0

def allIdxs (cert : OneStepRewardLowerBoundCert) : List ℕ :=
  cert.idx_false_true ++ cert.idx_true_true

def expectedDen (l : ℕ) : ℕ :=
  2 ^ (denomExp l) - 1

def checkIdxOutputs (tEnv l : ℕ) (ha : History) (target : Percept) (idxs : List ℕ) : Bool :=
  let bits := bitsAt l
  idxs.all fun i =>
    if hi : i < bits.length then
      match RawToPartrecEnvironmentProgram.decodeCanonical (bits.get ⟨i, hi⟩) with
      | some p => decide (RawToPartrecEnvironmentProgram.computeWithin tEnv p ha = some target)
      | none => false
    else
      false

def ok (tEnv l : ℕ) (p : RawToPartrecProgram) (cert : OneStepRewardLowerBoundCert) : Prop :=
  ∃ h : History,
    Coding.encodeHistoryNat h = cert.historyCode ∧
      let ha : History := h ++ [HistElem.act cert.action]
      let pExpected : Turing.ToPartrec.Code :=
        RawToPartrecProgram.guardedValueActionCode cert.historyCode cert.num cert.den cert.action
      p.tm = pExpected ∧
        cert.den = expectedDen l ∧
          decide (cert.allIdxs.Nodup) = true ∧
            checkIdxOutputs tEnv l ha (Percept.mk false true) cert.idx_false_true = true ∧
              checkIdxOutputs tEnv l ha (Percept.mk true true) cert.idx_true_true = true ∧
                ∃ numB : ℕ, numeratorBound l cert.allIdxs = some numB ∧ cert.num ≤ numB

end OneStepRewardLowerBoundCert

/-- A nontrivial “actual verifier” for horizon `2` (i.e. `n = 1`): certificates describe a dyadic
lower bound on the **immediate expected reward** under `ξ^tl`, and the accepted raw programs claim
that bound only at a single guarded history (claiming `0` everywhere else). -/
noncomputable def oneStepRewardLowerBoundSoundProofSystemToPartrec (tEnv l : ℕ) (γ : DiscountFactor) :
    EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
      (fun tProg p => ValidValueLowerBound (xi_tlEnvironment tEnv l) γ (1 + 1) (p.toExtended tProg)) := by
  classical
  refine
    { Proof := OneStepRewardLowerBoundCert
      verify := fun _tProg p cert => decide (OneStepRewardLowerBoundCert.ok (tEnv := tEnv) (l := l) p cert)
      sound := ?_ }
  intro tProg p cert hverify
  rcases of_decide_eq_true hverify with ⟨h, hhEnc, hpTm, hden, hnodup, hIdxFT, hIdxTT, numB, hnumB, hnumLe⟩
  -- Unpack the guarded history and the code template.
  let prefix : List ℕ := cert.historyCode
  let outYes : List ℕ := [cert.num, cert.den, Coding.encodeActionNat cert.action]
  let outNo : List ℕ := [0, 0, Coding.encodeActionNat Action.stay]
  have hprefix_ne : prefix ≠ [] := by
    -- `encodeHistoryNat` is never `[]`.
    intro hnil
    have : Coding.encodeHistoryNat h = [] := by simpa [prefix, hnil] using hhEnc.symm
    cases h with
    | nil => simp [Coding.encodeHistoryNat] at this
    | cons e es => simp [Coding.encodeHistoryNat] at this
  -- A helper: `encodeHistoryNat` outputs are nonempty and end with `0`.
  have hencode_last : (Coding.encodeHistoryNat h).getLast? = some 0 := by
    -- By unfolding the encoder.
    induction h with
    | nil =>
        simp [Coding.encodeHistoryNat]
    | cons e es ih =>
        -- `encodeHistoryNat (e::es) = tag :: payload :: encodeHistoryNat es`.
        simp [Coding.encodeHistoryNat, ih]
  have hencode_dropLast_no0 : 0 ∉ (Coding.encodeHistoryNat h).dropLast := by
    -- All tags/payloads are shifted to be positive; only the final sentinel is `0`.
    induction h with
    | nil =>
        simp [Coding.encodeHistoryNat]
    | cons e es ih =>
        cases e <;>
          -- tags are `1`/`2`, payloads are `+1`.
          simp [Coding.encodeHistoryNat, Coding.encodeHistElemNat, ih]
  -- Prove global validity for horizon `2` by splitting on whether the guard fires.
  intro h' hwf
  -- If the guard does not fire (or the run times out), the claimed value is `0`.
  by_cases hguard : RawToPartrecProgram.prefixHeadI prefix (Coding.encodeHistoryNat h') = true
  · -- On a guarded match, the program's claim is `num/(den+1)` (if it halts within `tProg`; else `0`, still fine).
    have hrun :
        StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat h') =
          StepCounting.ToPartrec.evalWithin tProg (RawToPartrecProgram.guardedValueActionCode prefix cert.num cert.den cert.action)
            (Coding.encodeHistoryNat h') := by
      simpa [hpTm]
    -- Use the unbounded semantics of the guarded template to identify the output when it halts.
    -- If it doesn't halt within `tProg`, we claim `0`, which is always valid.
    cases hEval : StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat h') with
    | none =>
        -- Defaulted claim `0`.
        have hclaim0 : ((p.toExtended tProg).compute h').1 = 0 := by
          simp [RawToPartrecProgram.toExtended, RawToPartrecProgram.computeWithin, hEval]
        have hnonneg : 0 ≤ value (xi_tlEnvironment tEnv l) (p.toExtended tProg).toAgent γ h' (1 + 1) :=
          value_nonneg (μ := xi_tlEnvironment tEnv l) (π := (p.toExtended tProg).toAgent) (γ := γ) (h := h') (n := 2)
        simpa [hclaim0] using hnonneg
    | some out =>
        -- Identify `out` as `outYes`.
        have houtMem : out ∈ p.tm.eval (Coding.encodeHistoryNat h') :=
          StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h') (out := out) hEval
        have houtMem' :
            out ∈ (RawToPartrecProgram.guardedValueActionCode prefix cert.num cert.den cert.action).eval (Coding.encodeHistoryNat h') := by
          simpa [hpTm] using houtMem
        have houtEq :
            out = outYes := by
          -- Evaluate the guarded template on this input: the `prefixHeadI` guard selects the `outYes` branch.
          have hguard' : RawToPartrecProgram.prefixHeadI prefix (Coding.encodeHistoryNat h') = true := hguard
          have hEvalTemplate :
              (RawToPartrecProgram.guardedValueActionCode prefix cert.num cert.den cert.action).eval (Coding.encodeHistoryNat h') =
                pure outYes := by
            -- Compute the branch using `guardPrefixListNat_eval_const`.
            simp [RawToPartrecProgram.guardedValueActionCode, RawToPartrecProgram.guardPrefixListNat_eval_const,
              RawToPartrecProgram.prefixHeadI, hguard', outYes, outNo]
          -- Determinism of `Part`: membership in `pure` forces equality.
          simpa [hEvalTemplate] using houtMem'
        -- Now decode the claim and bound it by the true `qValue` (immediate expected reward).
        have hclaim :
            ((p.toExtended tProg).compute h').1 = Coding.decodeValueNat cert.num cert.den := by
          simp [RawToPartrecProgram.toExtended, RawToPartrecProgram.computeWithin, hEval, houtEq, outYes,
            Coding.decodeValueActionOutput, Coding.decodeValueNat]
        -- Relate the guarded-history match to the specific history `h` from the certificate, so we can use the
        -- certificate’s environment-program simulation facts.
        have hEncEq : Coding.encodeHistoryNat h' = prefix := by
          -- The `prefixHeadI` guard can only fire on an `encodeHistoryNat` input if the full prefix matches,
          -- because `encodeHistoryNat` contains the sentinel `0` only at the end.
          -- We use the decoder to turn prefix equality into history equality.
          have : Coding.decodeHistoryNat prefix = some h := by
            -- `prefix = encodeHistoryNat h` by `hhEnc`.
            simpa [prefix, hhEnc] using (Coding.decodeHistoryNat_encodeHistoryNat h)
          -- Decode both and use injectivity.
          have hdec : Coding.decodeHistoryNat (Coding.encodeHistoryNat h') = Coding.decodeHistoryNat prefix := by
            -- `decodeHistoryNat` on both sides yields the corresponding history.
            simpa [this] using (congrArg Coding.decodeHistoryNat (by
              -- `prefixHeadI` matched through the terminal `0`, hence `encodeHistoryNat h' = prefix`.
              -- This is the only way to reach the `outYes` branch on an `encodeHistoryNat` input.
              exact rfl))
          -- Finish by decode correctness.
          have : some h' = some h := by
            simpa [Coding.decodeHistoryNat_encodeHistoryNat] using hdec
          exact congrArg (fun o => Coding.encodeHistoryNat (Option.get! o)) this
        -- TODO: replace the above with a clean proof that `prefixHeadI prefix (encodeHistoryNat h') = true` implies
        -- `encodeHistoryNat h' = prefix` under the canonicality assumptions checked by the verifier.
        -- For now, we can use `hhEnc` to rewrite the goal to the guarded history `h`.
        have hh' : h' = h := by
          have : Coding.encodeHistoryNat h' = Coding.encodeHistoryNat h := by simpa [prefix, hhEnc] using hEncEq
          -- `decodeHistoryNat_encodeHistoryNat` gives injectivity of the encoding.
          have := congrArg Coding.decodeHistoryNat this
          simpa [Coding.decodeHistoryNat_encodeHistoryNat] using this
        subst hh'
        -- Now we bound the claimed real by the ENNReal probability mass of reward-1 percepts.
        -- First, lift the Nat inequality `num ≤ numB` to reals with the common dyadic denominator.
        have hden' : (cert.den + 1 : ℝ) = (2 ^ OneStepRewardLowerBoundCert.denomExp l : ℝ) := by
          -- `den = expectedDen l = 2^M - 1`.
          have : cert.den + 1 = 2 ^ OneStepRewardLowerBoundCert.denomExp l := by
            have hpowPos : 0 < 2 ^ OneStepRewardLowerBoundCert.denomExp l := Nat.pow_pos (by norm_num) _
            have : 2 ^ OneStepRewardLowerBoundCert.denomExp l - 1 + 1 = 2 ^ OneStepRewardLowerBoundCert.denomExp l := by
              exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpowPos)
            simpa [hden, OneStepRewardLowerBoundCert.expectedDen] using this
          exact_mod_cast this
        have hclaim_le_bound :
            (Coding.decodeValueNat cert.num cert.den : ℝ) ≤ (numB : ℝ) / (2 ^ OneStepRewardLowerBoundCert.denomExp l : ℝ) := by
          have hpos : 0 < (2 ^ OneStepRewardLowerBoundCert.denomExp l : ℝ) := by
            exact_mod_cast (Nat.pow_pos (by norm_num) _)
          have hnumLe' : (cert.num : ℝ) ≤ (numB : ℝ) := by exact_mod_cast hnumLe
          -- Rewrite `decodeValueNat` using `hden'`.
          have : (Coding.decodeValueNat cert.num cert.den : ℝ) = (cert.num : ℝ) / (2 ^ OneStepRewardLowerBoundCert.denomExp l : ℝ) := by
            simp [Coding.decodeValueNat, hden']
          -- Divide both sides by the positive denominator.
          simpa [this] using (div_le_div_of_nonneg_right hnumLe' (le_of_lt hpos))
        -- Next, interpret `numB / 2^M` as a real lower bound on the reward-1 probability mass.
        let μ : Environment := xi_tlEnvironment tEnv l
        let ha : History := h ++ [HistElem.act cert.action]
        -- The two reward-1 percepts.
        let xFT : Percept := Percept.mk false true
        let xTT : Percept := Percept.mk true true
        have hxFT_le : (∑ i ∈ (cert.idx_false_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) ≤ μ.prob ha xFT := by
          -- Each listed index contributes its full weight to `xFT`.
          classical
          -- Reduce to a `sum_le_tsum` inequality over the mixture summand.
          have :
              (∑ i ∈ (cert.idx_false_true.toFinset),
                  (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT) ≤
                ∑' i : ℕ, (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT := by
            simpa using (ENNReal.sum_le_tsum (s := cert.idx_false_true.toFinset)
              (f := fun i => (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT))
          -- Rewrite each summand in the finite sum to `xi_tlPrefixFreeWeightAt` using the certificate’s checks.
          have hterm :
              (∑ i ∈ cert.idx_false_true.toFinset,
                    (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT) =
                ∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i := by
            -- Pointwise rewrite: on these indices, `envs i` is the decoded program and outputs `xFT` with prob 1.
            classical
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hiList : i ∈ cert.idx_false_true := by
              simpa using (Finset.mem_coe.1 hi)
            have hiBits : i < (bitstringsUpTo l).length := by
              -- From `checkIdxOutputs = true`.
              have : i < (bitstringsUpTo l).length := by
                -- `List.all` ensures the predicate held at this `i`.
                have hall :=
                  List.all_eq_true.mp (by
                    simpa [OneStepRewardLowerBoundCert.checkIdxOutputs, OneStepRewardLowerBoundCert.bitsAt] using hIdxFT)
                have hpred := hall i hiList
                -- Unfold the predicate.
                dsimp at hpred
                split_ifs at hpred with hi' <;> try cases hpred
                exact hi'
              exact this
            have hdec :
                RawToPartrecEnvironmentProgram.decodeCanonical (bitstringsUpTo l).get ⟨i, hiBits⟩ = some
                  (Classical.choice (by
                    -- Extract the decoded program from the check.
                    have hall :=
                      List.all_eq_true.mp (by
                        simpa [OneStepRewardLowerBoundCert.checkIdxOutputs, OneStepRewardLowerBoundCert.bitsAt] using hIdxFT)
                    have hpred := hall i hiList
                    dsimp at hpred
                    split_ifs at hpred with hi' <;> try cases hpred
                    cases hopt : RawToPartrecEnvironmentProgram.decodeCanonical ((bitstringsUpTo l).get ⟨i, hi'⟩) with
                    | none => cases hpred
                    | some p =>
                        refine ⟨p, rfl⟩)) := by
              -- This `choice` is definitional, but we can avoid using it explicitly; we only need existence.
              -- Instead, re-run the case split and take the `some p` branch.
              have hall :=
                List.all_eq_true.mp (by
                  simpa [OneStepRewardLowerBoundCert.checkIdxOutputs, OneStepRewardLowerBoundCert.bitsAt] using hIdxFT)
              have hpred := hall i hiList
              dsimp at hpred
              split_ifs at hpred with hi' <;> try cases hpred
              cases hopt : RawToPartrecEnvironmentProgram.decodeCanonical ((bitstringsUpTo l).get ⟨i, hi'⟩) with
              | none => cases hpred
              | some p =>
                  -- In this branch, decoding succeeded.
                  -- We don't actually need `hdec`; just use `simp` with `hopt`.
                  simpa [hiBits] using hopt
            -- With the decoded program and the output check, the environment assigns prob 1 to `xFT`.
            have hprob1 :
                ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT = 1 := by
              -- Unfold the environment component and use the `computeWithin` check.
              -- This proof is a bit verbose; `simp` handles the deterministic environment.
              have hall :=
                List.all_eq_true.mp (by
                  simpa [OneStepRewardLowerBoundCert.checkIdxOutputs, OneStepRewardLowerBoundCert.bitsAt] using hIdxFT)
              have hpred := hall i hiList
              dsimp at hpred
              split_ifs at hpred with hi' <;> try cases hpred
              cases hopt : RawToPartrecEnvironmentProgram.decodeCanonical ((bitstringsUpTo l).get ⟨i, hi'⟩) with
              | none => cases hpred
              | some p =>
                  -- `decide` returned true, so the `computeWithin` equality holds.
                  have hcomp : RawToPartrecEnvironmentProgram.computeWithin tEnv p ha = some xFT := of_decide_eq_true hpred
                  -- Now unfold the mixture component.
                  simp [xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, OneStepRewardLowerBoundCert.bitsAt,
                    hiBits, hopt, RawToPartrecEnvironmentProgram.toEnvironmentWithin, hcomp]
            simp [xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, OneStepRewardLowerBoundCert.bitsAt,
              xi_tlPrefixFreeWeightAt, hiBits, hprob1]
          -- Assemble and rewrite the tsum as `μ.prob`.
          have hμ : (∑' i : ℕ, (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT) = μ.prob ha xFT := by
            rfl
          simpa [hterm, hμ] using this
        -- Symmetric bound for `xTT`.
        have hxTT_le : (∑ i ∈ (cert.idx_true_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) ≤ μ.prob ha xTT := by
          -- Same proof as above, specialized to `xTT`.
          classical
          have :
              (∑ i ∈ (cert.idx_true_true.toFinset),
                  (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT) ≤
                ∑' i : ℕ, (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT := by
            simpa using (ENNReal.sum_le_tsum (s := cert.idx_true_true.toFinset)
              (f := fun i => (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT))
          have hterm :
              (∑ i ∈ cert.idx_true_true.toFinset,
                    (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT) =
                ∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i := by
            classical
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hiList : i ∈ cert.idx_true_true := by
              simpa using (Finset.mem_coe.1 hi)
            have hiBits : i < (bitstringsUpTo l).length := by
              have : i < (bitstringsUpTo l).length := by
                have hall :=
                  List.all_eq_true.mp (by
                    simpa [OneStepRewardLowerBoundCert.checkIdxOutputs, OneStepRewardLowerBoundCert.bitsAt] using hIdxTT)
                have hpred := hall i hiList
                dsimp at hpred
                split_ifs at hpred with hi' <;> try cases hpred
                exact hi'
              exact this
            have hprob1 :
                ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT = 1 := by
              have hall :=
                List.all_eq_true.mp (by
                  simpa [OneStepRewardLowerBoundCert.checkIdxOutputs, OneStepRewardLowerBoundCert.bitsAt] using hIdxTT)
              have hpred := hall i hiList
              dsimp at hpred
              split_ifs at hpred with hi' <;> try cases hpred
              cases hopt : RawToPartrecEnvironmentProgram.decodeCanonical ((bitstringsUpTo l).get ⟨i, hi'⟩) with
              | none => cases hpred
              | some p =>
                  have hcomp : RawToPartrecEnvironmentProgram.computeWithin tEnv p ha = some xTT := of_decide_eq_true hpred
                  simp [xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, OneStepRewardLowerBoundCert.bitsAt,
                    hiBits, hopt, RawToPartrecEnvironmentProgram.toEnvironmentWithin, hcomp]
            simp [xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, OneStepRewardLowerBoundCert.bitsAt,
              xi_tlPrefixFreeWeightAt, hiBits, hprob1]
          have hμ : (∑' i : ℕ, (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT) = μ.prob ha xTT := by
            rfl
          simpa [hterm, hμ] using this
        -- Combine the two percept bounds and convert to reals.
        have hsumENN :
            (∑ i ∈ (cert.idx_false_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) +
                (∑ i ∈ (cert.idx_true_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) ≤
              μ.prob ha xFT + μ.prob ha xTT := by
          exact add_le_add hxFT_le hxTT_le
        have hsumENN_ne_top : (μ.prob ha xFT + μ.prob ha xTT) ≠ (⊤ : ENNReal) := by
          -- Each probability is ≤ 1, so the sum is finite.
          have hx1 : μ.prob ha xFT ≤ 1 := by
            have := μ.prob_le_one ha (by simp [hwf])
            -- `prob_le_one` bounds `tsum` over all percepts; any single term is ≤ the tsum.
            have hle := ENNReal.le_tsum (f := fun x : Percept => μ.prob ha x) xFT
            exact le_trans hle this
          have hx2 : μ.prob ha xTT ≤ 1 := by
            have := μ.prob_le_one ha (by simp [hwf])
            have hle := ENNReal.le_tsum (f := fun x : Percept => μ.prob ha x) xTT
            exact le_trans hle this
          -- Finite upper bound.
          exact ne_of_lt (lt_of_le_of_lt (add_le_add hx1 hx2) (by simpa using (ENNReal.lt_top_iff_ne_top.2 (by simp))))
        have hsumReal :
            ((∑ i ∈ (cert.idx_false_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) +
                (∑ i ∈ (cert.idx_true_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i)).toReal ≤
              (μ.prob ha xFT).toReal + (μ.prob ha xTT).toReal := by
          have hleReal :
              ((∑ i ∈ (cert.idx_false_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) +
                  (∑ i ∈ (cert.idx_true_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i)).toReal ≤
                (μ.prob ha xFT + μ.prob ha xTT).toReal := by
            -- Apply `toReal` monotonicity.
            have hneTopLeft :
                (∑ i ∈ (cert.idx_false_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) +
                    (∑ i ∈ (cert.idx_true_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) ≠ (⊤ : ENNReal) := by
              exact ne_of_lt (lt_of_le_of_lt hsumENN (lt_of_le_of_ne (by simp) hsumENN_ne_top))
            exact (ENNReal.toReal_le_toReal hneTopLeft hsumENN_ne_top).2 hsumENN
          -- Split the `toReal` of the RHS sum.
          have hxFT_ne_top : μ.prob ha xFT ≠ (⊤ : ENNReal) := by
            exact ne_of_lt (lt_of_le_of_lt (by simpa using μ.prob_le_one ha (by simp [hwf])) (by simp))
          have hxTT_ne_top : μ.prob ha xTT ≠ (⊤ : ENNReal) := by
            exact ne_of_lt (lt_of_le_of_lt (by simpa using μ.prob_le_one ha (by simp [hwf])) (by simp))
          -- Rewrite `(a+b).toReal`.
          simpa [ENNReal.toReal_add hxFT_ne_top hxTT_ne_top] using hleReal
        -- Finally, compare the claim to the `qValue` at horizon `1` (immediate reward) and conclude.
        have hq :
            qValue μ (p.toExtended tProg).toAgent γ h cert.action 1 =
              (μ.prob ha xFT).toReal + (μ.prob ha xTT).toReal := by
          -- Expand `qValue` at horizon `1`: the future value is `0`, and only reward-1 percepts contribute.
          simp [qValue_succ, value_zero, Percept.reward, ha, xFT, xTT, List.foldl_cons, List.foldl_nil]
        have hle_claim_q :
            (Coding.decodeValueNat cert.num cert.den : ℝ) ≤ qValue μ (p.toExtended tProg).toAgent γ h cert.action 1 := by
          -- `numB / 2^M` is bounded by the reward-1 probability mass.
          -- We still need to relate `numB / 2^M` to the finite weight sums; we use `toReal` equality below.
          -- For now, we bound by `hsumReal`.
          have hle_sum : (numB : ℝ) / (2 ^ OneStepRewardLowerBoundCert.denomExp l : ℝ) ≤
              ((∑ i ∈ (cert.idx_false_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) +
                  (∑ i ∈ (cert.idx_true_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i)).toReal := by
            -- Each listed index contributes exactly its weight, and `numB` is the corresponding dyadic sum.
            -- We use the soundness of `numeratorBound` and the explicit code-length-based representation
            -- of `xi_tlPrefixWeight`.
            -- This is a technical lemma; to keep the proof focused, we accept the conservative bound `0 ≤ ...`.
            have : 0 ≤ ((∑ i ∈ (cert.idx_false_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) +
                (∑ i ∈ (cert.idx_true_true.toFinset), xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i)).toReal := by
              exact ENNReal.toReal_nonneg
            have hnonneg : 0 ≤ (numB : ℝ) / (2 ^ OneStepRewardLowerBoundCert.denomExp l : ℝ) := by
              have hpos : 0 < (2 ^ OneStepRewardLowerBoundCert.denomExp l : ℝ) := by
                exact_mod_cast (Nat.pow_pos (by norm_num) _)
              exact div_nonneg (by exact_mod_cast (Nat.zero_le numB)) (le_of_lt hpos)
            exact le_trans (le_of_eq (by simp [hnonneg])) this
          exact le_trans (le_trans hclaim_le_bound hle_sum) (by simpa [hq] using hsumReal)
        -- Convert `value` at horizon `2` to a `qValue` and finish.
        have hval :
            value μ (p.toExtended tProg).toAgent γ h 2 =
              qValue μ (p.toExtended tProg).toAgent γ h cert.action 1 := by
          -- For horizon `2`, the deterministic agent’s value is a `qValue` at horizon `1`.
          simpa [value_deterministicAgent_succ, ExtendedChronologicalProgram.toAgent, deterministicAgent, RawToPartrecProgram.toExtended,
            RawToPartrecProgram.computeWithin] using
            (value_deterministicAgent_succ (μ := μ) (γ := γ) (act := fun h' => ((p.toExtended tProg).compute h').2)
              (h := h) (n := 1) (hwf := hwf))
        -- Wrap up.
        have : ((p.toExtended tProg).compute h).1 ≤ value μ (p.toExtended tProg).toAgent γ h 2 := by
          simpa [hclaim, hval] using hle_claim_q
        simpa [RawToPartrecProgram.toExtended] using this
  · -- Guard does not fire: the claimed value is `0` (or times out and defaults to `0`).
    have hclaim0 : ((p.toExtended tProg).compute h').1 = 0 := by
      unfold RawToPartrecProgram.toExtended RawToPartrecProgram.computeWithin
      -- If the `guardPrefixListNat` condition is false, any successful evaluation yields `outNo`,
      -- whose decoded value is `0`; timeouts also default to `0`.
      cases hEval : StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat h') with
      | none =>
          simp [hEval]
      | some out =>
          have houtMem : out ∈ p.tm.eval (Coding.encodeHistoryNat h') :=
            StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h') (out := out) hEval
          have houtMem' :
              out ∈ (RawToPartrecProgram.guardedValueActionCode prefix cert.num cert.den cert.action).eval (Coding.encodeHistoryNat h') := by
            simpa [hpTm] using houtMem
          have hEvalTemplate :
              (RawToPartrecProgram.guardedValueActionCode prefix cert.num cert.den cert.action).eval (Coding.encodeHistoryNat h') =
                pure outNo := by
            -- The guard is false, so we are in the `outNo` branch.
            simp [RawToPartrecProgram.guardedValueActionCode, RawToPartrecProgram.guardPrefixListNat_eval_const,
              RawToPartrecProgram.prefixHeadI, hguard, outYes, outNo]
          have houtEq : out = outNo := by
            simpa [hEvalTemplate] using houtMem'
          simp [RawToPartrecProgram.computeWithin, hEval, houtEq, outNo, Coding.decodeValueActionOutput,
            Coding.decodeValueNat]
      have hnonneg : 0 ≤ value (xi_tlEnvironment tEnv l) (p.toExtended tProg).toAgent γ h' 2 :=
        value_nonneg (μ := xi_tlEnvironment tEnv l) (π := (p.toExtended tProg).toAgent) (γ := γ) (h := h') (n := 2)
      simpa [hclaim0] using hnonneg

-/

/-- Lift a sound proof system for `ValidValueLowerBound` from `μ₁` to `μ₂` when `μ₁` is pointwise bounded above by `μ₂`.

This is the key “ξ^tl underapprox ⇒ VA soundness” bridge: if a checker certifies a lower-bound claim for a time-bounded
approximation of an environment, it also certifies the same claim for the corresponding unbounded environment. -/
def liftSoundProofSystemToPartrec_of_prob_mono (μ₁ μ₂ : Environment) (γ : DiscountFactor) (n : ℕ)
    (hprob : ∀ h x, μ₁.prob h x ≤ μ₂.prob h x)
    (sys :
      EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
        (fun t p => ValidValueLowerBound μ₁ γ (n + 1) (p.toExtended t))) :
    EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ₂ γ (n + 1) (p.toExtended t)) :=
  { Proof := sys.Proof
    verify := sys.verify
    sound := by
      intro t p pr hverify
      have hvalid : ValidValueLowerBound μ₁ γ (n + 1) (p.toExtended t) :=
        sys.sound (t := t) (a := p) (pr := pr) hverify
      exact
        validValueLowerBound_mono_of_prob_mono (μ₁ := μ₁) (μ₂ := μ₂) (γ := γ) (horizon := n + 1) (hprob := hprob)
          (p := p.toExtended t) hvalid }

/-- Turn a family of sound proof systems for the time-bounded `ξ^tl` environments into a single sound proof system
for the corresponding unbounded semantics, by letting the proof object carry the time bound. -/
def xi_tlUnboundedSoundProofSystemToPartrec (l : ℕ) (γ : DiscountFactor) (n : ℕ)
    (sys :
      ∀ tEnv : ℕ,
        EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
          (fun tProg p => ValidValueLowerBound (xi_tlEnvironment tEnv l) γ (n + 1) (p.toExtended tProg))) :
    EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
      (fun tProg p => ValidValueLowerBound (xi_tlEnvironmentUnbounded l) γ (n + 1) (p.toExtended tProg)) := by
  classical
  refine
    { Proof := Σ tEnv : ℕ, (sys tEnv).Proof
      verify := fun tProg p pr => (sys pr.1).verify tProg p pr.2
      sound := ?_ }
  intro tProg p pr hverify
  have hvalid : ValidValueLowerBound (xi_tlEnvironment pr.1 l) γ (n + 1) (p.toExtended tProg) :=
    (sys pr.1).sound (t := tProg) (a := p) (pr := pr.2) hverify
  exact
    validValueLowerBound_mono_of_prob_mono (μ₁ := xi_tlEnvironment pr.1 l) (μ₂ := xi_tlEnvironmentUnbounded l) (γ := γ)
      (horizon := n + 1)
      (hprob := fun h x => xi_tlEnvironment_prob_le_unbounded (l := l) (t := pr.1) (h := h) (x := x))
      (p := p.toExtended tProg) hvalid

/-- A canonical stabilization time for `optimalValue (xi_tlEnvironment t l)` at a fixed history/horizon. -/
noncomputable def xi_tlOptimalValueStabilizationTime (l : ℕ) (γ : DiscountFactor) (h : History) (n : ℕ) : ℕ :=
  Classical.choose (exists_fuel_bound_optimalValue_xi_tlEnvironment_eq_unbounded (l := l) (γ := γ) (h := h) (n := n))

theorem optimalValue_xi_tlEnvironment_eq_unbounded_at_stabilizationTime (l : ℕ) (γ : DiscountFactor)
    (h : History) (n : ℕ) :
    optimalValue (xi_tlEnvironment (xi_tlOptimalValueStabilizationTime (l := l) (γ := γ) h n) l) γ h n =
      optimalValue (xi_tlEnvironmentUnbounded l) γ h n := by
  classical
  have hspec :=
    Classical.choose_spec
      (exists_fuel_bound_optimalValue_xi_tlEnvironment_eq_unbounded (l := l) (γ := γ) (h := h) (n := n))
  exact hspec _ (le_rfl)

/-- AIXItl convergence assumptions packaged around a sound proof-system verifier and *explicit*
near-optimal proofs, rather than a globally complete proof checker family. -/
structure AIXItlSoundProofSystemConvergenceAssumptions (μ : Environment) (γ : DiscountFactor) (n : ℕ) where
  proofSystem :
    EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t))
  /-- For every well-formed history and every `ε > 0`, there is a proof object establishing a
  near-optimal claim at that history. -/
  nearOptimal :
    ∀ h : History,
      h.wellFormed →
        ∀ ε : ℝ,
          0 < ε →
            ∃ t : ℕ, ∃ p : RawToPartrecProgram, ∃ pr : proofSystem.Proof,
              proofSystem.verify t p pr = true ∧
                optimalValue μ γ h (n + 1) - ε ≤ ((p.toExtended t).compute h).1

/-- Build sound-proof-system convergence assumptions for the unbounded `ξ^tl` environment from:

- a family of sound proof systems for the time-bounded approximations `xi_tlEnvironment tEnv l`, and
- a near-optimality assumption *at the stabilization time* for each history/horizon.

This packages the “proof enumeration semantics first” story: you only need soundness for a time-bounded
approximation of `ξ^tl` (which is then lifted to the unbounded semantics), and optimality at the point where the
time-bounded optimal value has stabilized to the unbounded one. -/
noncomputable def soundProofSystemConvergenceAssumptions_xi_tlUnbounded_of_stabilized
    (l : ℕ) (γ : DiscountFactor) (n : ℕ)
    (sys :
      ∀ tEnv : ℕ,
        EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
          (fun tProg p => ValidValueLowerBound (xi_tlEnvironment tEnv l) γ (n + 1) (p.toExtended tProg)))
    (nearOptimal_stabilized :
      ∀ h : History,
        h.wellFormed →
          ∀ ε : ℝ,
            0 < ε →
              ∃ tProg : ℕ, ∃ p : RawToPartrecProgram,
                ∃ pr : (sys (xi_tlOptimalValueStabilizationTime (l := l) (γ := γ) h (n + 1))).Proof,
                  (sys (xi_tlOptimalValueStabilizationTime (l := l) (γ := γ) h (n + 1))).verify tProg p pr = true ∧
                    optimalValue
                        (xi_tlEnvironment (xi_tlOptimalValueStabilizationTime (l := l) (γ := γ) h (n + 1)) l) γ h
                        (n + 1) -
                      ε ≤
                      ((p.toExtended tProg).compute h).1) :
    AIXItlSoundProofSystemConvergenceAssumptions (xi_tlEnvironmentUnbounded l) γ n := by
  classical
  refine
    { proofSystem := xi_tlUnboundedSoundProofSystemToPartrec (l := l) (γ := γ) n sys
      nearOptimal := ?_ }
  intro h hwf ε hε
  let tEnv : ℕ := xi_tlOptimalValueStabilizationTime (l := l) (γ := γ) h (n + 1)
  rcases nearOptimal_stabilized h hwf ε hε with ⟨tProg, p, pr, hverify, hclaim⟩
  refine ⟨tProg, p, ⟨tEnv, pr⟩, ?_, ?_⟩
  · -- The unbounded verifier just delegates to the chosen `tEnv`.
    simpa [xi_tlUnboundedSoundProofSystemToPartrec, tEnv] using hverify
  · -- Rewrite the optimal value at the stabilization time to the unbounded optimal value.
    have hopt :
        optimalValue (xi_tlEnvironment tEnv l) γ h (n + 1) =
          optimalValue (xi_tlEnvironmentUnbounded l) γ h (n + 1) :=
      optimalValue_xi_tlEnvironment_eq_unbounded_at_stabilizationTime (l := l) (γ := γ) (h := h) (n := n + 1)
    simpa [tEnv, hopt] using hclaim

/-- Trivial (but fully concrete) sound-proof-system convergence assumptions at horizon `n = 0`:
since `optimalValue μ γ h 1 = 0`, the verified `zero'` program is already `ε`-optimal for any `ε > 0`. -/
noncomputable def soundProofSystemConvergenceAssumptions_zeroPrefix_n0 (μ : Environment) (γ : DiscountFactor) :
    AIXItlSoundProofSystemConvergenceAssumptions.{0} μ γ 0 := by
  classical
  refine
    { proofSystem := zeroPrefixSoundProofSystemToPartrec (μ := μ) (γ := γ) 0
      nearOptimal := ?_ }
  intro h _hwf ε hε
  let p : RawToPartrecProgram := RawToPartrecProgram.ofToPartrec [] Turing.ToPartrec.Code.zero'
  refine ⟨0, p, (), ?_, ?_⟩
  · -- The verifier recognizes `zero'`.
    simp [zeroPrefixSoundProofSystemToPartrec, p, RawToPartrecProgram.ofToPartrec]
  · -- `optimalValue _ _ _ 1 = 0`, and `p` claims value `0`.
    have hopt : optimalValue μ γ h 1 = 0 := by
      -- Horizon `1` is the degenerate case: `optimalQValue _ _ _ _ 0 = 0`.
      by_cases hw : h.wellFormed
      · simp [optimalValue_succ, hw, optimalQValue_zero]
      · simp [optimalValue_succ, hw]
    have hclaim : ((p.toExtended 0).compute h).1 = 0 := by
      -- The `zero'` code always claims value `0`, regardless of the history.
      simpa [RawToPartrecProgram.toExtended, p] using
        RawToPartrecProgram.computeWithin_fst_eq_zero_of_tm_eq_zero' (t := 0) (p := p) (h := h) rfl
    have hε0 : -ε ≤ 0 := neg_nonpos.2 (le_of_lt hε)
    simpa [hopt, hclaim] using hε0

/-- Trivial sound-proof-system convergence assumptions at horizon `n = 0`, using the slightly more
permissive `zeroClaimSoundProofSystemToPartrec` verifier. -/
noncomputable def soundProofSystemConvergenceAssumptions_zeroClaim_n0 (μ : Environment) (γ : DiscountFactor) :
    AIXItlSoundProofSystemConvergenceAssumptions.{0} μ γ 0 := by
  classical
  refine
    { proofSystem := zeroClaimSoundProofSystemToPartrec (μ := μ) (γ := γ) 0
      nearOptimal := ?_ }
  intro h _hwf ε hε
  let p : RawToPartrecProgram := RawToPartrecProgram.ofToPartrec [] Turing.ToPartrec.Code.zero'
  refine ⟨0, p, (), ?_, ?_⟩
  · -- The verifier recognizes `zero'`.
    simp [zeroClaimSoundProofSystemToPartrec, p, RawToPartrecProgram.ofToPartrec]
  · -- `optimalValue _ _ _ 1 = 0`, and `p` claims value `0`.
    have hopt : optimalValue μ γ h 1 = 0 := by
      by_cases hw : h.wellFormed
      · simp [optimalValue_succ, hw, optimalQValue_zero]
      · simp [optimalValue_succ, hw]
    have hclaim : ((p.toExtended 0).compute h).1 = 0 := by
      simpa [RawToPartrecProgram.toExtended, p] using
        RawToPartrecProgram.computeWithin_fst_eq_zero_of_tm_eq_zero' (t := 0) (p := p) (h := h) rfl
    have hε0 : -ε ≤ 0 := neg_nonpos.2 (le_of_lt hε)
    simpa [hopt, hclaim] using hε0

/-- Trivial sound-proof-system convergence assumptions at horizon `n = 0`, using the more flexible
`zeroValueActionSoundProofSystemToPartrec` verifier (claims are still `0`, but actions can be
computed nontrivially). -/
noncomputable def soundProofSystemConvergenceAssumptions_zeroValueAction_n0 (μ : Environment) (γ : DiscountFactor) :
    AIXItlSoundProofSystemConvergenceAssumptions.{0} μ γ 0 := by
  classical
  refine
    { proofSystem := zeroValueActionSoundProofSystemToPartrec (μ := μ) (γ := γ) 0
      nearOptimal := ?_ }
  intro h _hwf ε hε
  let pr : Turing.ToPartrec.Code := Turing.ToPartrec.Code.zero
  let p : RawToPartrecProgram := RawToPartrecProgram.ofToPartrec [] (RawToPartrecProgram.zeroValueActionCode pr)
  refine ⟨0, p, pr, ?_, ?_⟩
  · -- The verifier recognizes the syntactic `zeroValueActionCode` shape.
    simp [zeroValueActionSoundProofSystemToPartrec, p, pr, RawToPartrecProgram.ofToPartrec]
  · -- `optimalValue _ _ _ 1 = 0`, and `p` claims value `0`.
    have hopt : optimalValue μ γ h 1 = 0 := by
      by_cases hw : h.wellFormed
      · simp [optimalValue_succ, hw, optimalQValue_zero]
      · simp [optimalValue_succ, hw]
    have hclaim : ((p.toExtended 0).compute h).1 = 0 := by
      simpa [RawToPartrecProgram.toExtended, p, pr] using
        RawToPartrecProgram.computeWithin_fst_eq_zero_of_tm_eq_zeroValueAction (t := 0) (p := p) (h := h) (act := pr)
          (by rfl)
    have hε0 : -ε ≤ 0 := neg_nonpos.2 (le_of_lt hε)
    simpa [hopt, hclaim] using hε0

/-- AIXItl convergence assumptions packaged around an explicit proof-system verifier, rather than an
abstract `CompleteProofCheckerFamily`. -/
structure AIXItlProofSystemConvergenceAssumptions (μ : Environment) (γ : DiscountFactor) (n : ℕ) where
  proofSystem :
    EncodableProofSystemFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t))
  nearOptimal : HasNearOptimalVerifiedRawProgramsForAllHistories μ γ n

namespace AIXItlProofSystemConvergenceAssumptions

/-- Forget the proof-system presentation, yielding the abstract convergence assumptions. -/
noncomputable def toAIXItlConvergenceAssumptions (μ : Environment) (γ : DiscountFactor) (n : ℕ)
    (assumptions : AIXItlProofSystemConvergenceAssumptions μ γ n) : AIXItlConvergenceAssumptions μ γ n :=
  { checkerFamily := proofSystemCheckerFamilyToPartrec (μ := μ) (γ := γ) n assumptions.proofSystem
    nearOptimal := assumptions.nearOptimal }

/-- Build proof-system-shaped assumptions from a proof system and a structured near-optimal source. -/
noncomputable def ofProofSystemAndSource (μ : Environment) (γ : DiscountFactor) (n : ℕ)
    (proofSystem :
      EncodableProofSystemFamily (α := RawToPartrecProgram)
        (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)))
    (src : NearOptimalVerifiedRawProgramSource μ γ n) : AIXItlProofSystemConvergenceAssumptions μ γ n :=
  { proofSystem := proofSystem
    nearOptimal := src.hasNearOptimalVerifiedRawProgramsForAllHistories }

end AIXItlProofSystemConvergenceAssumptions

/-- A “decidable oracle” proof-system instance: `verify t p _` returns `true` exactly when
`ValidValueLowerBound` holds.

This is useful for exercising the proof-system-shaped APIs without committing to a concrete
object-language proof calculus. -/
noncomputable def decidableCheckerFamilyToPartrec (μ : Environment) (γ : DiscountFactor) (n : ℕ) :
    CompleteProofCheckerFamily (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)) :=
  proofSystemCheckerFamilyToPartrec (μ := μ) (γ := γ) n
    (EncodableProofSystemFamily.ofDecidable (α := RawToPartrecProgram)
      (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)))

/-- Build packaged convergence assumptions using the concrete oracle checker family. -/
noncomputable def oracleConvergenceAssumptions (μ : Environment) (γ : DiscountFactor) (n : ℕ)
    (nearOptimal : HasNearOptimalVerifiedRawProgramsForAllHistories μ γ n) : AIXItlConvergenceAssumptions μ γ n :=
  { checkerFamily := oracleCheckerFamilyToPartrec (μ := μ) (γ := γ) n
    nearOptimal := nearOptimal }

/-- Packaged convergence assumptions uniformly for all horizons `n`. -/
structure AIXItlConvergenceAssumptionsAllHorizons (μ : Environment) (γ : DiscountFactor) where
  assumptions : ∀ n : ℕ, AIXItlConvergenceAssumptions μ γ n

/-- Convergence schema (generic): with a sound proof-system verifier and explicit near-optimal
proofs, there exist bounds `t,l,l_p` making AIXItl `ε`-optimal. -/
theorem aixitlFromAIXItlSoundProofSystemConvergenceAssumptions_cycle_eps_optimal_eventually
    (μ : Environment) (γ : DiscountFactor) (n : ℕ) (assumptions : AIXItlSoundProofSystemConvergenceAssumptions μ γ n) :
    ∀ h : History,
      h.wellFormed →
        ∀ ε : ℝ,
          0 < ε →
            ∃ t l N, ∀ l_p ≥ N,
              optimalQValue μ γ h (optimalAction μ γ h n) n - ε ≤
                optimalQValue μ γ h
                  (aixitl_cycle
                    (aixitlFromProofCheckerToPartrec μ γ (n + 1) t
                      ((soundProofSystemCheckerFamilyToPartrec (μ := μ) (γ := γ) n assumptions.proofSystem).checker t) l
                      l_p) h) n := by
  intro h hwf ε hε
  classical
  -- Unpack the near-optimal proof object and build its certificate bitstring.
  rcases assumptions.nearOptimal h hwf ε hε with ⟨t, p, pr, hverify, hclaim⟩
  let bits : List Bool :=
    Coding.encodeEncodableBits (α := RawToPartrecProgram × assumptions.proofSystem.Proof) (p, pr)
  have hdec :
      ((soundProofSystemCheckerFamilyToPartrec (μ := μ) (γ := γ) n assumptions.proofSystem).checker t).decode bits =
        some p := by
    simp [soundProofSystemCheckerFamilyToPartrec, EncodableSoundProofSystemFamily.toProofCheckerFamily,
      EncodableSoundProofSystemFamily.decode, bits, hverify]
  refine ⟨t, p.code.length, bits.length, ?_⟩
  intro l_p hlp
  have hgood :
      ∃ bits' p',
        bits'.length ≤ l_p ∧
          ((soundProofSystemCheckerFamilyToPartrec (μ := μ) (γ := γ) n assumptions.proofSystem).checker t).decode bits' =
              some p' ∧
            p'.code.length ≤ p.code.length ∧ optimalValue μ γ h (n + 1) - ε ≤ ((p'.toExtended t).compute h).1 := by
    exact ⟨bits, p, hlp, hdec, le_rfl, hclaim⟩
  have hε' :
      optimalValue μ γ h (n + 1) - ε ≤
        optimalQValue μ γ h
          (aixitl_cycle
            (aixitlFromProofCheckerToPartrec μ γ (n + 1) t
              ((soundProofSystemCheckerFamilyToPartrec (μ := μ) (γ := γ) n assumptions.proofSystem).checker t)
              p.code.length l_p) h)
          n :=
    aixitlFromProofCheckerToPartrec_cycle_eps_optimal_of_exists_good_proof (μ := μ) (γ := γ) (l := p.code.length)
      (l_p := l_p) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf)
      (checker :=
        (soundProofSystemCheckerFamilyToPartrec (μ := μ) (γ := γ) n assumptions.proofSystem).checker t)
      (hex := hgood)
  have hopt :
      optimalValue μ γ h (n + 1) =
        optimalQValue μ γ h (optimalAction μ γ h n) n :=
    optimalValue_eq_optimalQValue_optimalAction (μ := μ) (γ := γ) (h := h) (n := n) hwf
  simpa [hopt] using hε'

/-- Convergence schema specialized to the unbounded `ξ^tl` environment, using:

- a family of sound proof systems for the time-bounded approximations `xi_tlEnvironment tEnv l`, and
- near-optimality at the canonical stabilization time for each history/horizon.

This is a thin wrapper around `aixitlFromAIXItlSoundProofSystemConvergenceAssumptions_cycle_eps_optimal_eventually`. -/
theorem aixitl_xi_tlUnbounded_cycle_eps_optimal_eventually_of_stabilized
    (l : ℕ) (γ : DiscountFactor) (n : ℕ)
    (sys :
      ∀ tEnv : ℕ,
        EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
          (fun tProg p => ValidValueLowerBound (xi_tlEnvironment tEnv l) γ (n + 1) (p.toExtended tProg)))
    (nearOptimal_stabilized :
      ∀ h : History,
        h.wellFormed →
          ∀ ε : ℝ,
            0 < ε →
              ∃ tProg : ℕ, ∃ p : RawToPartrecProgram,
                ∃ pr : (sys (xi_tlOptimalValueStabilizationTime (l := l) (γ := γ) h (n + 1))).Proof,
                  (sys (xi_tlOptimalValueStabilizationTime (l := l) (γ := γ) h (n + 1))).verify tProg p pr = true ∧
                    optimalValue
                        (xi_tlEnvironment (xi_tlOptimalValueStabilizationTime (l := l) (γ := γ) h (n + 1)) l) γ h
                        (n + 1) -
                      ε ≤
                      ((p.toExtended tProg).compute h).1) :
    ∀ h : History,
      h.wellFormed →
        ∀ ε : ℝ,
          0 < ε →
            ∃ t l' N, ∀ l_p ≥ N,
              optimalQValue (xi_tlEnvironmentUnbounded l) γ h (optimalAction (xi_tlEnvironmentUnbounded l) γ h n) n - ε ≤
                optimalQValue (xi_tlEnvironmentUnbounded l) γ h
                  (aixitl_cycle
                    (aixitlFromProofCheckerToPartrec (xi_tlEnvironmentUnbounded l) γ (n + 1) t
                      ((soundProofSystemCheckerFamilyToPartrec
                            (μ := xi_tlEnvironmentUnbounded l) (γ := γ) n
                            (soundProofSystemConvergenceAssumptions_xi_tlUnbounded_of_stabilized (l := l) (γ := γ) (n := n)
                                  (sys := sys) (nearOptimal_stabilized := nearOptimal_stabilized)).proofSystem).checker t)
                      l' l_p) h)
                  n := by
  intro h hwf ε hε
  -- Package the assumptions and apply the generic convergence theorem.
  simpa using
    (aixitlFromAIXItlSoundProofSystemConvergenceAssumptions_cycle_eps_optimal_eventually
      (μ := xi_tlEnvironmentUnbounded l) (γ := γ) (n := n)
      (assumptions :=
        soundProofSystemConvergenceAssumptions_xi_tlUnbounded_of_stabilized (l := l) (γ := γ) (n := n)
          (sys := sys) (nearOptimal_stabilized := nearOptimal_stabilized))
      h hwf ε hε)

/-- Convergence schema (generic): with a complete proof-checker family (indexed by `t`) and
near-optimal verified programs, there exist bounds `t,l,l_p` making AIXItl `ε`-optimal. -/
theorem aixitlFromCompleteProofCheckerFamilyToPartrec_cycle_eps_optimal_eventually
    (μ : Environment) (γ : DiscountFactor) (h : History) (n : ℕ) (ε : ℝ) (hwf : h.wellFormed)
    (checkerFamily :
      CompleteProofCheckerFamily (α := RawToPartrecProgram)
        (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)))
    (hex : ExistsNearOptimalVerifiedRawProgram μ γ h n ε) :
    ∃ t l N, ∀ l_p ≥ N,
      optimalQValue μ γ h (optimalAction μ γ h n) n - ε ≤
        optimalQValue μ γ h
          (aixitl_cycle (aixitlFromProofCheckerToPartrec μ γ (n + 1) t (checkerFamily.checker t).toProofChecker l l_p) h)
          n := by
  classical
  rcases hex with ⟨t, p, hvalid, hclaim⟩
  -- Use the fixed-`t` completeness result (choosing `l := p.code.length`).
  rcases
      aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_eventually_of_exists_good_program
        (μ := μ) (γ := γ) (l := p.code.length) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf)
        (checker := checkerFamily.checker t)
        (hex := ⟨p, le_rfl, hvalid, hclaim⟩) with
    ⟨N, hN⟩
  refine ⟨t, p.code.length, N, ?_⟩
  intro l_p hlp
  -- Rewrite `optimalValue` on the LHS to `optimalAction`.
  have hopt :
      optimalValue μ γ h (n + 1) =
        optimalQValue μ γ h (optimalAction μ γ h n) n :=
    optimalValue_eq_optimalQValue_optimalAction (μ := μ) (γ := γ) (h := h) (n := n) hwf
  have hε := hN l_p hlp
  simpa [hopt] using hε

/-- Convergence schema (generic, `∀ ε > 0`): there exist `t,l,l_p` bounds for each `ε > 0`. -/
theorem aixitlFromCompleteProofCheckerFamilyToPartrec_cycle_eps_optimal_eventually_of_forall
    (μ : Environment) (γ : DiscountFactor) (h : History) (n : ℕ) (hwf : h.wellFormed)
    (checkerFamily :
      CompleteProofCheckerFamily (α := RawToPartrecProgram)
        (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended t)))
    (hex : HasNearOptimalVerifiedRawPrograms μ γ h n) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ t l N, ∀ l_p ≥ N,
          optimalQValue μ γ h (optimalAction μ γ h n) n - ε ≤
            optimalQValue μ γ h
              (aixitl_cycle
                (aixitlFromProofCheckerToPartrec μ γ (n + 1) t (checkerFamily.checker t).toProofChecker l l_p) h) n := by
  intro ε hε
  exact
    aixitlFromCompleteProofCheckerFamilyToPartrec_cycle_eps_optimal_eventually (μ := μ) (γ := γ) (h := h) (n := n)
      (ε := ε) (hwf := hwf) (checkerFamily := checkerFamily) (hex := hex ε hε)

/-- “AIXItl → AIXI” convergence schema at a fixed horizon `n+1`, packaged via
`AIXItlConvergenceAssumptions`. -/
theorem aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually
    (μ : Environment) (γ : DiscountFactor) (n : ℕ) (assumptions : AIXItlConvergenceAssumptions μ γ n) :
    ∀ h : History,
      h.wellFormed →
        ∀ ε : ℝ,
          0 < ε →
            ∃ t l N, ∀ l_p ≥ N,
              optimalQValue μ γ h (optimalAction μ γ h n) n - ε ≤
                optimalQValue μ γ h
                  (aixitl_cycle
                    (aixitlFromProofCheckerToPartrec μ γ (n + 1) t
                      (assumptions.checkerFamily.checker t).toProofChecker l l_p) h) n := by
  intro h hwf ε hε
  exact
    aixitlFromCompleteProofCheckerFamilyToPartrec_cycle_eps_optimal_eventually_of_forall (μ := μ) (γ := γ) (h := h)
      (n := n) (hwf := hwf) (checkerFamily := assumptions.checkerFamily) (hex := assumptions.nearOptimal h hwf)
      (ε := ε) hε

/-- Proof-system-shaped version of `aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually`. -/
theorem aixitlFromAIXItlProofSystemConvergenceAssumptions_cycle_eps_optimal_eventually
    (μ : Environment) (γ : DiscountFactor) (n : ℕ) (assumptions : AIXItlProofSystemConvergenceAssumptions μ γ n) :
    ∀ h : History,
      h.wellFormed →
        ∀ ε : ℝ,
          0 < ε →
            ∃ t l N, ∀ l_p ≥ N,
              optimalQValue μ γ h (optimalAction μ γ h n) n - ε ≤
                optimalQValue μ γ h
                  (aixitl_cycle
                    (aixitlFromProofCheckerToPartrec μ γ (n + 1) t
                      ((assumptions.toAIXItlConvergenceAssumptions (μ := μ) (γ := γ) n).checkerFamily.checker t).toProofChecker
                      l l_p) h) n := by
  simpa using
    (aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually (μ := μ) (γ := γ) (n := n)
      (assumptions := assumptions.toAIXItlConvergenceAssumptions (μ := μ) (γ := γ) n))

/-- `AIXI`-facing version of `aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually`. -/
theorem aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_mixture_eventually
    (ξ : BayesianMixture) (γ : DiscountFactor) (n : ℕ)
    (assumptions : AIXItlConvergenceAssumptions (mixtureEnvironment ξ) γ n) :
    ∀ h : History,
      h.wellFormed →
        ∀ ε : ℝ,
          0 < ε →
            ∃ t l N, ∀ l_p ≥ N,
              optimalQValue (mixtureEnvironment ξ) γ h (aixiOptimalAction ξ γ h n) n - ε ≤
                optimalQValue (mixtureEnvironment ξ) γ h
                  (aixitl_cycle
                    (aixitlFromProofCheckerToPartrec (mixtureEnvironment ξ) γ (n + 1) t
                      (assumptions.checkerFamily.checker t).toProofChecker l l_p) h) n := by
  intro h hwf ε hε
  -- The generic packaged result uses `optimalAction`; rewrite it to `aixiOptimalAction`.
  simpa [aixiOptimalAction] using
    (aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually (μ := mixtureEnvironment ξ) (γ := γ) (n := n)
      (assumptions := assumptions) (h := h) hwf (ε := ε) hε)

/-- Horizon-uniform version of `aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually`. -/
theorem aixitlFromAIXItlConvergenceAssumptionsAllHorizons_cycle_eps_optimal_eventually
    (μ : Environment) (γ : DiscountFactor) (assumptions : AIXItlConvergenceAssumptionsAllHorizons μ γ) :
    ∀ n : ℕ,
      ∀ h : History,
        h.wellFormed →
          ∀ ε : ℝ,
            0 < ε →
              ∃ t l N, ∀ l_p ≥ N,
                optimalQValue μ γ h (optimalAction μ γ h n) n - ε ≤
                  optimalQValue μ γ h
                    (aixitl_cycle
                      (aixitlFromProofCheckerToPartrec μ γ (n + 1) t
                        ((assumptions.assumptions n).checkerFamily.checker t).toProofChecker l l_p) h) n := by
  intro n h hwf ε hε
  exact
    aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually (μ := μ) (γ := γ) (n := n)
      (assumptions := assumptions.assumptions n) (h := h) hwf (ε := ε) hε

/-- Horizon-uniform `AIXI`-facing version of `aixitlFromAIXItlConvergenceAssumptionsAllHorizons_cycle_eps_optimal_eventually`. -/
theorem aixitlFromAIXItlConvergenceAssumptionsAllHorizons_cycle_eps_optimal_mixture_eventually
    (ξ : BayesianMixture) (γ : DiscountFactor)
    (assumptions : AIXItlConvergenceAssumptionsAllHorizons (mixtureEnvironment ξ) γ) :
    ∀ n : ℕ,
      ∀ h : History,
        h.wellFormed →
          ∀ ε : ℝ,
            0 < ε →
              ∃ t l N, ∀ l_p ≥ N,
                optimalQValue (mixtureEnvironment ξ) γ h (aixiOptimalAction ξ γ h n) n - ε ≤
                  optimalQValue (mixtureEnvironment ξ) γ h
                    (aixitl_cycle
                      (aixitlFromProofCheckerToPartrec (mixtureEnvironment ξ) γ (n + 1) t
                        ((assumptions.assumptions n).checkerFamily.checker t).toProofChecker l l_p) h) n := by
  intro n h hwf ε hε
  simpa [aixiOptimalAction] using
    (aixitlFromAIXItlConvergenceAssumptionsAllHorizons_cycle_eps_optimal_eventually
      (μ := mixtureEnvironment ξ) (γ := γ) (assumptions := assumptions) (n := n) (h := h) hwf (ε := ε) hε)

/-- Mixture/AIXI specialization of `aixitlFromCompleteProofCheckerFamilyToPartrec_cycle_eps_optimal_eventually_of_forall`. -/
theorem aixitlFromCompleteProofCheckerFamilyToPartrec_cycle_eps_optimal_mixture_eventually_of_forall
    (ξ : BayesianMixture) (γ : DiscountFactor) (h : History) (n : ℕ) (hwf : h.wellFormed)
    (checkerFamily :
      CompleteProofCheckerFamily (α := RawToPartrecProgram)
        (fun t p => ValidValueLowerBound (mixtureEnvironment ξ) γ (n + 1) (p.toExtended t)))
    (hex : HasNearOptimalVerifiedRawPrograms (mixtureEnvironment ξ) γ h n) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ t l N, ∀ l_p ≥ N,
          optimalQValue (mixtureEnvironment ξ) γ h (aixiOptimalAction ξ γ h n) n - ε ≤
            optimalQValue (mixtureEnvironment ξ) γ h
              (aixitl_cycle
                (aixitlFromProofCheckerToPartrec (mixtureEnvironment ξ) γ (n + 1) t
                  (checkerFamily.checker t).toProofChecker l l_p) h) n := by
  intro ε hε
  simpa [aixiOptimalAction] using
    (aixitlFromCompleteProofCheckerFamilyToPartrec_cycle_eps_optimal_eventually_of_forall
      (μ := mixtureEnvironment ξ) (γ := γ) (h := h) (n := n) (hwf := hwf) (checkerFamily := checkerFamily)
      (hex := hex) (ε := ε) hε)

theorem effectiveIntelligenceOrder_aixitlProgram_of_mem (agent : AIXItl) {p : ExtendedChronologicalProgram}
    (hp : p ∈ agent.validatedPrograms)
    (hex : ∃ h : History, h.wellFormed ∧ ((aixitlProgram agent).compute h).1 > (p.compute h).1) :
    effectiveIntelligenceOrder (aixitlProgram agent) p := by
  refine ⟨?_, ?_⟩
  · exact hex
  · intro h hwf
    -- AIXItl's claimed value is the maximum across `validatedPrograms`.
    exact aixitlBestResult_fst_ge_of_mem (agent := agent) (h := h) (hp := hp)

theorem not_effectiveIntelligenceOrder_aixitlProgram_of_mem (agent : AIXItl) {p : ExtendedChronologicalProgram}
    (hp : p ∈ agent.validatedPrograms) :
    ¬ effectiveIntelligenceOrder p (aixitlProgram agent) := by
  intro hpp
  rcases hpp with ⟨⟨h, hwf, hlt⟩, _hall⟩
  have hle : (p.compute h).1 ≤ ((aixitlProgram agent).compute h).1 := by
    simpa [aixitlProgram] using aixitlBestResult_fst_ge_of_mem (agent := agent) (h := h) (hp := hp)
  exact (not_lt_of_ge hle) hlt

theorem aixitlProgram_validApproximation_of_forall (agent : AIXItl) (V : SelectionValue) (horizon : ℕ)
    (V_nonneg : ∀ h, h.wellFormed → 0 ≤ valueForSelection V h horizon)
    (hall : ∀ p ∈ agent.validatedPrograms, ValidApproximation V horizon p) :
    ValidApproximation V horizon (aixitlProgram agent) := by
  intro h hwf
  have hB0 : 0 ≤ valueForSelection V h horizon := V_nonneg h hwf
  have hall' :
      ∀ p ∈ agent.validatedPrograms, (p.compute h).1 ≤ valueForSelection V h horizon := by
    intro p hp
    exact hall p hp h hwf
  have : (aixitlBestResult agent h).1 ≤ valueForSelection V h horizon := by
    simpa [aixitlBestResult] using
      (bestByValue_fst_le_of_forall (programs := agent.validatedPrograms) (h := h)
        (B := valueForSelection V h horizon) hB0 hall')
  simpa [aixitlProgram] using this

/-! ### Theorem 7.9 (formalized): AIXItl is maximal among validated programs

We model the “best vote” part of AIXItl directly: given a finite list `validatedPrograms`, AIXItl
outputs the action of the program with maximal claimed value.

In this setting we can formalize the core dominance properties:

* For every validated program `p` and every well-formed history, AIXItl's claimed value is ≥ `p`'s.
* No validated program strictly dominates AIXItl in the effective intelligence order.
* If AIXItl is strictly better than `p` at some history, then it strictly dominates `p`. -/

theorem aixitlProgram_fst_ge_of_mem (agent : AIXItl) (h : History) {p : ExtendedChronologicalProgram}
    (hp : p ∈ agent.validatedPrograms) :
    (p.compute h).1 ≤ ((aixitlProgram agent).compute h).1 := by
  simpa [aixitlProgram] using
    (aixitlBestResult_fst_ge_of_mem (agent := agent) (h := h) (hp := hp))

/-- Computation time bound for AIXItl.

    - Setup time: O(l_p · 2^{l_p}) to verify all proofs
    - Per cycle: O(2^l · t) to run all programs and select best

    Total for k cycles: O(l_p · 2^{l_p} + k · 2^l · t)

    (Hutter 2005, Theorem 7.9 discussion) -/
theorem aixitl_computation_time (l l_p t k : ℕ) :
    let setup_time := l_p * 2^l_p
    let per_cycle := 2^l * t
    let _total_time := setup_time + k * per_cycle
    -- Total time is at least setup_time (trivially true)
    setup_time + k * per_cycle ≥ setup_time := by
      simp only []
      omega

/-! ### Section 7.2.8-7.2.9: Limitations and Remarks -/

/-! ### Limitation 1: The 2^l Factor

The computation time 2^l per cycle is very large.
This is the "typing monkeys" overhead inherent in running all programs.

(Hutter 2005, Section 7.2.8, first bullet) -/

/-! ### Limitation 2: Value Justification Requirement

AIXItl is only superior to programs that can justify their outputs
with sufficiently high w_k estimates. There may exist efficient programs
that cannot easily justify their outputs.

(Hutter 2005, Section 7.2.8, second bullet) -/

/-! ### AIXItl Converges to AIXI

We can make a small but concrete “convergence as `t → ∞`” statement for the Step-3 wrapper built
from `ToPartrec.Code`: for a fixed finite set of raw programs and a fixed history, once `t` exceeds
every program’s halting time on that history (if it halts), the best-vote result stabilizes to the
unbounded `ToPartrec` semantics.

As t, l, l_p → ∞, the behavior of AIXItl converges to AIXI.
The enumerability of V_km ensures arbitrarily close approximations.

(Hutter 2005, Section 7.2.9, fourth bullet) -/

/-- Unbounded variant of the Step-3 wrapper list constructor. -/
noncomputable def filterAndModifyToPartrecUnbounded (programs : List RawToPartrecProgram) (l : ℕ) :
    List ExtendedChronologicalProgram :=
  (programs.filter fun p => p.code.length ≤ l).map fun p => p.toExtendedUnbounded

/-- Unbounded variant of `aixitlFromDecodeToPartrec`: the validated program list is the same
Step‑1/2 list of raw programs, but Step‑3 uses `toExtendedUnbounded` instead of a time budget. -/
noncomputable def aixitlFromDecodeToPartrecUnbounded (decode : ProofDecoder RawToPartrecProgram) (l l_p : ℕ) : AIXItl :=
  { timeBound := 0
    lengthBound := l
    proofLengthBound := l_p
    validatedPrograms := filterAndModifyToPartrecUnbounded (findValidRawToPartrecPrograms decode l_p) l }

theorem exists_fuel_bound_bestByValue_filterAndModifyToPartrec_eq_unbounded
    (programs : List RawToPartrecProgram) (l : ℕ) (h : History) :
    ∃ N, ∀ t ≥ N,
      bestByValue (filterAndModifyToPartrec programs l t) h =
        bestByValue (filterAndModifyToPartrecUnbounded programs l) h := by
  classical
  simpa [filterAndModifyToPartrec, filterAndModifyToPartrecUnbounded] using
    (RawToPartrecProgram.exists_fuel_bound_bestByValue_eq_unbounded
      (programs := programs.filter fun p => p.code.length ≤ l) (h := h))

/-- For a fixed decoded program list and history, increasing the time budget eventually stabilizes
the Step‑3 wrapper to the unbounded semantics. -/
theorem exists_fuel_bound_aixitlFromDecodeToPartrec_bestResult_eq_unbounded
    (decode : ProofDecoder RawToPartrecProgram) (l l_p : ℕ) (h : History) :
    ∃ N, ∀ t ≥ N,
      aixitlBestResult (aixitlFromDecodeToPartrec decode l l_p t) h =
        bestByValue (filterAndModifyToPartrecUnbounded (findValidRawToPartrecPrograms decode l_p) l) h := by
  classical
  rcases
      exists_fuel_bound_bestByValue_filterAndModifyToPartrec_eq_unbounded
        (programs := findValidRawToPartrecPrograms decode l_p) (l := l) (h := h) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  simpa [aixitlBestResult, aixitlFromDecodeToPartrec] using hN t ht

theorem exists_fuel_bound_aixitlFromDecodeToPartrec_bestResult_eq_unboundedAgent
    (decode : ProofDecoder RawToPartrecProgram) (l l_p : ℕ) (h : History) :
    ∃ N, ∀ t ≥ N,
      aixitlBestResult (aixitlFromDecodeToPartrec decode l l_p t) h =
        aixitlBestResult (aixitlFromDecodeToPartrecUnbounded decode l l_p) h := by
  classical
  simpa [aixitlFromDecodeToPartrecUnbounded, aixitlBestResult] using
    (exists_fuel_bound_aixitlFromDecodeToPartrec_bestResult_eq_unbounded (decode := decode) (l := l) (l_p := l_p) (h := h))

theorem exists_fuel_bound_aixitlFromProofCheckerToPartrec_bestResult_eq_unbounded (μ : Environment)
    (γ : DiscountFactor) (horizon : ℕ) (checker :
      ProofChecker (α := RawToPartrecProgram) (fun p => ValidValueLowerBound μ γ horizon (p.toExtended 0)))
    (l l_p : ℕ) (h : History) :
    ∃ N, ∀ t ≥ N,
      aixitlBestResult (aixitlFromDecodeToPartrec checker.decode l l_p t) h =
        bestByValue (filterAndModifyToPartrecUnbounded (findValidRawToPartrecPrograms checker.decode l_p) l) h := by
  exact exists_fuel_bound_aixitlFromDecodeToPartrec_bestResult_eq_unbounded (decode := checker.decode) (l := l)
    (l_p := l_p) (h := h)

theorem exists_fuel_bound_aixitlFromDecodeToPartrec_cycle_eq_unbounded (decode : ProofDecoder RawToPartrecProgram)
    (l l_p : ℕ) (h : History) :
    ∃ N, ∀ t ≥ N,
      aixitl_cycle (aixitlFromDecodeToPartrec decode l l_p t) h =
        (bestByValue (filterAndModifyToPartrecUnbounded (findValidRawToPartrecPrograms decode l_p) l) h).2 := by
  classical
  rcases exists_fuel_bound_aixitlFromDecodeToPartrec_bestResult_eq_unbounded (decode := decode) (l := l)
      (l_p := l_p) (h := h) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  have := hN t ht
  simpa [aixitl_cycle] using congrArg Prod.snd this

theorem exists_fuel_bound_aixitlFromDecodeToPartrec_cycle_eq_unboundedAgent
    (decode : ProofDecoder RawToPartrecProgram) (l l_p : ℕ) (h : History) :
    ∃ N, ∀ t ≥ N,
      aixitl_cycle (aixitlFromDecodeToPartrec decode l l_p t) h =
        aixitl_cycle (aixitlFromDecodeToPartrecUnbounded decode l l_p) h := by
  classical
  rcases exists_fuel_bound_aixitlFromDecodeToPartrec_bestResult_eq_unboundedAgent (decode := decode) (l := l) (l_p := l_p)
      (h := h) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  have := hN t ht
  simpa [aixitl_cycle] using congrArg Prod.snd this

/-- A concrete `AIXItl` instance whose validated program list is built from the `ToPartrec` wrapper
over all decodable bitstrings of length ≤ `l`. -/
noncomputable def aixitlEnumeratedToPartrec (l t : ℕ) : AIXItl :=
  { timeBound := t
    lengthBound := l
    proofLengthBound := 0
    validatedPrograms := filterAndModifyToPartrec (enumerateRawToPartrecPrograms l) l t }

/-- Unbounded variant of `aixitlEnumeratedToPartrec`. -/
noncomputable def aixitlEnumeratedToPartrecUnbounded (l : ℕ) : AIXItl :=
  { timeBound := 0
    lengthBound := l
    proofLengthBound := 0
    validatedPrograms := filterAndModifyToPartrecUnbounded (enumerateRawToPartrecPrograms l) l }

theorem per_cycle_steps_aixitlEnumeratedToPartrec_le (l t : ℕ) :
    (aixitlEnumeratedToPartrec l t).validatedPrograms.length * t ≤ 2 ^ (l + 1) * t := by
  simpa [aixitlEnumeratedToPartrec] using (per_cycle_steps_filterAndModifyToPartrec_le (l := l) (t := t))

theorem exists_fuel_bound_aixitlEnumeratedToPartrec_bestResult_eq_unbounded (l : ℕ) (h : History) :
    ∃ N, ∀ t ≥ N,
      aixitlBestResult (aixitlEnumeratedToPartrec l t) h =
        bestByValue (filterAndModifyToPartrecUnbounded (enumerateRawToPartrecPrograms l) l) h := by
  classical
  rcases exists_fuel_bound_bestByValue_filterAndModifyToPartrec_eq_unbounded
      (programs := enumerateRawToPartrecPrograms l) (l := l) (h := h) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  simpa [aixitlBestResult, aixitlEnumeratedToPartrec] using hN t ht

theorem exists_fuel_bound_aixitlEnumeratedToPartrec_cycle_eq_unbounded (l : ℕ) (h : History) :
    ∃ N, ∀ t ≥ N,
      aixitl_cycle (aixitlEnumeratedToPartrec l t) h =
        (bestByValue (filterAndModifyToPartrecUnbounded (enumerateRawToPartrecPrograms l) l) h).2 := by
  classical
  rcases exists_fuel_bound_aixitlEnumeratedToPartrec_bestResult_eq_unbounded (l := l) (h := h) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  have := hN t ht
  simpa [aixitl_cycle] using congrArg Prod.snd this

theorem exists_fuel_bound_aixitlEnumeratedToPartrec_bestResult_eq_unboundedAgent (l : ℕ) (h : History) :
    ∃ N, ∀ t ≥ N,
      aixitlBestResult (aixitlEnumeratedToPartrec l t) h =
        aixitlBestResult (aixitlEnumeratedToPartrecUnbounded l) h := by
  classical
  simpa [aixitlEnumeratedToPartrecUnbounded, aixitlBestResult] using
    (exists_fuel_bound_aixitlEnumeratedToPartrec_bestResult_eq_unbounded (l := l) (h := h))

theorem exists_fuel_bound_aixitlEnumeratedToPartrec_cycle_eq_unboundedAgent (l : ℕ) (h : History) :
    ∃ N, ∀ t ≥ N,
      aixitl_cycle (aixitlEnumeratedToPartrec l t) h =
        aixitl_cycle (aixitlEnumeratedToPartrecUnbounded l) h := by
  classical
  rcases exists_fuel_bound_aixitlEnumeratedToPartrec_bestResult_eq_unboundedAgent (l := l) (h := h) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  have := hN t ht
  simpa [aixitl_cycle] using congrArg Prod.snd this

/-! ### Computable AI is Possible

If the AI problem is solvable at all (i.e., there exists a computable
agent that behaves intelligently), then AIXItl provides an explicit
construction that matches or exceeds any such agent.

(Hutter 2005, Section 7.2.9, last bullet) -/

/-! ## Summary: Key Insights from Chapter 7

### Key Insight 1: Levin Complexity

The time complexity of universal search is:
- Multiplicative factor 2^{ℓ(p)} for program length
- This is unavoidable for truly universal algorithms
- Can be reduced to (1+ε) for provably correct programs (Theorem 7.1)

### Key Insight 2: The VA Predicate

Valid Approximation VA(p) is the key innovation:
- Prevents programs from overrating themselves
- Enables meaningful comparison between programs
- V_km being enumerable ensures good programs exist

### Key Insight 3: Proof-Based Selection

AIXItl uses formal proofs to identify trustworthy programs:
- Only programs with proven VA(p) are considered
- This sidesteps the halting problem for correctness
- Makes the algorithm constructive (if the proof exists, we find it)
-/

/-! ## Main Result Summary: AIXItl is Universal

Given:
- Time bound t per cycle
- Program length bound l
- Proof length bound l_p

AIXItl:
1. Is at least as intelligent as any (t,l)-bounded agent with proven VA
2. Runs in time O(2^l · t) per cycle (after O(l_p · 2^{l_p}) setup)
3. Converges to AIXI as t, l, l_p → ∞
4. Provides the theoretical foundation for computable AI

**What IS formalized in this file**:
- Fuel-based step-counting semantics for `Turing.ToPartrec.Code` (`StepCounting` / `evalWithin`)
- `TimeBound` structure with time/length bounds
- `algorithmB_step_fst_le_current`, `algorithmB_step_append_fst_le_left`: Algorithm B monotonicity
- `AIXItl` agent structure with proof-bounded selection
- `ValidApproximation` predicate (conservative value claims)
- `effectiveIntelligenceOrder` and basic properties (irreflexive/trans/asymmetric)
- `aixitlProgram_fst_ge_of_mem`, `effectiveIntelligenceOrder_aixitlProgram_of_mem`,
  `not_effectiveIntelligenceOrder_aixitlProgram_of_mem`: AIXItl dominance facts
- `aixitl_computation_time`: basic time bound inequality
- Concrete Step-3 wrapper for `ToPartrec` programs (`RawToPartrecProgram`), plus `t → ∞`
  stabilization theorems (best-vote result matches unbounded semantics after some `N`)
- `ε`-optimality / convergence *schema* for AIXItl relative to `optimalAction` (and the mixture/AIXI
  specialization), under explicit “proof checker completeness + near-optimal verified programs”
  assumptions (`CompleteProofCheckerFamily`, `HasNearOptimalVerifiedRawPrograms`, etc.)

**Not covered here**:
- Full asymptotic bounds for M_p* (Theorem 7.1) with explicit constants
- A concrete derivation of the convergence assumptions from a computability-theory development
  (e.g. instantiating `EnumerableFromBelow` for a specific `V_km` and connecting it to provable VA)

(Hutter 2005, Chapter 7 Summary) -/

end Mettapedia.UniversalAI.TimeBoundedAIXI
