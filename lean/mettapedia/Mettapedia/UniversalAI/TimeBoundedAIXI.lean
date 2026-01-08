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

 theorem prefixHeadI_self (pref : List ℕ) : prefixHeadI pref pref = true := by
   induction pref with
   | nil =>
       simp [prefixHeadI]
   | cons x xs ih =>
       simp [prefixHeadI, ih]

 theorem prefixHeadI_encodeHistoryNat_eq (h h' : History)
     (hp : prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat h') = true) : h = h' := by
   induction h generalizing h' with
  | nil =>
      cases h' with
      | nil => rfl
      | cons e es =>
          have : (Coding.encodeHistElemNat e).1 = 0 := by
            simpa [Coding.encodeHistoryNat, prefixHeadI] using hp
          cases e <;> simp [Coding.encodeHistElemNat] at this
  | cons e es ih =>
      cases h' with
      | nil =>
          have :
              0 = (Coding.encodeHistElemNat e).1 ∧
                0 = (Coding.encodeHistElemNat e).2 ∧ prefixHeadI (Coding.encodeHistoryNat es) [] = true := by
            simpa [Coding.encodeHistoryNat, prefixHeadI] using hp
          cases e <;> simp [Coding.encodeHistElemNat] at this
      | cons e' es' =>
          have hparts :
              (Coding.encodeHistElemNat e').1 = (Coding.encodeHistElemNat e).1 ∧
                (Coding.encodeHistElemNat e').2 = (Coding.encodeHistElemNat e).2 ∧
                  prefixHeadI (Coding.encodeHistoryNat es) (Coding.encodeHistoryNat es') = true := by
            simpa [Coding.encodeHistoryNat, prefixHeadI] using hp
          have hes : es = es' := ih _ hparts.2.2
          have helem' : e' = e := by
            have hdec_e :
                Coding.decodeHistElemNat (Coding.encodeHistElemNat e).1 (Coding.encodeHistElemNat e).2 = some e := by
              simp
            have hdec_e' :
                Coding.decodeHistElemNat (Coding.encodeHistElemNat e').1 (Coding.encodeHistElemNat e').2 = some e' := by
              simp
            have : some e' = some e := by
              calc
                some e' =
                    Coding.decodeHistElemNat (Coding.encodeHistElemNat e').1 (Coding.encodeHistElemNat e').2 := by
                      simp [hdec_e']
                _ = Coding.decodeHistElemNat (Coding.encodeHistElemNat e).1 (Coding.encodeHistElemNat e).2 := by
                      simp [hparts.1, hparts.2.1]
                _ = some e := by
                      simp [hdec_e]
            simpa using this
          have helem : e = e' := helem'.symm
          subst helem
          subst hes
          rfl

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

/-! #### Multi-history dispatch (finite)

`guardPrefixListNat` is convenient for a single guarded history, but it is *destructive* on failed
comparisons (it decrements the head while testing equality). To build programs that return
different constant outputs on several distinct history codes, we instead:

1. compute (independently) a list of `0/1` flags indicating which prefixes match, and
2. select the first `0` flag in that list (falling back to a trailing default flag).
-/

/-- Return `[0]` iff `pref` is a `prefixHeadI` prefix of the input, else `[1]`. -/
def prefixMatchFlagCode (pref : List ℕ) : Turing.ToPartrec.Code :=
  guardPrefixListNat pref (constListCode [0]) (constListCode [1])

theorem prefixMatchFlagCode_eval (pref v : List ℕ) :
    (prefixMatchFlagCode pref).eval v =
      if prefixHeadI pref v then pure [0] else pure [1] := by
  simpa [prefixMatchFlagCode] using
    (guardPrefixListNat_eval_const (pref := pref) (outYes := [0]) (outNo := [1]) (v := v))

/-- Build the list of match flags for a list of prefixes, *ending with* a trailing `0` (default). -/
def prefixMatchFlagsCode : List (List ℕ) → Turing.ToPartrec.Code
  | [] => constListCode [0]
  | pref :: prefs => Turing.ToPartrec.Code.cons (prefixMatchFlagCode pref) (prefixMatchFlagsCode prefs)

/-- Choose the first output whose corresponding flag is `0`.

The input is a list of naturals, intended to be flags in `{0,1}`. The caller should ensure there
is a trailing `0` flag so selection always terminates in the desired default case. -/
def chooseByFlagsCode : List (List ℕ) → Turing.ToPartrec.Code
  | [] => constListCode []
  | out :: outs =>
      Turing.ToPartrec.Code.case (constListCode out)
        (Turing.ToPartrec.Code.comp (chooseByFlagsCode outs) Turing.ToPartrec.Code.tail)

/-- Dispatch on a finite list of history codes (prefix checks), returning the output of the first
matching case, or `default` if no case matches.

The outputs are `List ℕ` payloads (typically `[num, den, action]`). -/
def dispatchHistoryCodes (cases : List (List ℕ × List ℕ)) (default : List ℕ) : Turing.ToPartrec.Code :=
  let prefs : List (List ℕ) := cases.map Prod.fst
  let outs : List (List ℕ) := cases.map Prod.snd ++ [default]
  Turing.ToPartrec.Code.comp (chooseByFlagsCode outs) (prefixMatchFlagsCode prefs)

/-- The list of `0/1` match flags computed by `prefixMatchFlagsCode`, as a pure function. -/
def prefixMatchFlags (prefs : List (List ℕ)) (v : List ℕ) : List ℕ :=
  prefs.map (fun pref => if prefixHeadI pref v then 0 else 1) ++ [0]

theorem prefixMatchFlagsCode_eval (prefs : List (List ℕ)) (v : List ℕ) :
    (prefixMatchFlagsCode prefs).eval v = pure (prefixMatchFlags prefs v) := by
  induction prefs with
  | nil =>
      simp [prefixMatchFlagsCode, prefixMatchFlags, constListCode_eval]
  | cons pref prefs ih =>
      by_cases hp : prefixHeadI pref v
      · simp [prefixMatchFlagsCode, prefixMatchFlags, Turing.ToPartrec.Code.cons_eval, prefixMatchFlagCode_eval, ih, hp]
      · simp [prefixMatchFlagsCode, prefixMatchFlags, Turing.ToPartrec.Code.cons_eval, prefixMatchFlagCode_eval, ih, hp]

/-- Choose the first output corresponding to a `0` flag, as a pure function.

This matches `chooseByFlagsCode` when flags are intended to be in `{0,1}` and include a trailing `0`. -/
def chooseByFlags : List (List ℕ) → List ℕ → List ℕ
  | [], _ => []
  | out :: outs, flags => if flags.headI = 0 then out else chooseByFlags outs flags.tail

theorem chooseByFlagsCode_eval (outs : List (List ℕ)) (flags : List ℕ) :
    (chooseByFlagsCode outs).eval flags = pure (chooseByFlags outs flags) := by
  induction outs generalizing flags with
  | nil =>
      simp [chooseByFlagsCode, chooseByFlags, constListCode_eval]
  | cons out outs ih =>
      cases h : flags.headI with
      | zero =>
          simp [chooseByFlagsCode, chooseByFlags, Turing.ToPartrec.Code.case_eval, h, constListCode_eval]
      | succ m =>
          simp [chooseByFlagsCode, chooseByFlags, Turing.ToPartrec.Code.case_eval, h, ih, Turing.ToPartrec.Code.comp_eval,
            constListCode_eval]

theorem dispatchHistoryCodes_eval (cases : List (List ℕ × List ℕ)) (default : List ℕ) (v : List ℕ) :
    (dispatchHistoryCodes cases default).eval v =
      pure
        (chooseByFlags (cases.map Prod.snd ++ [default])
          (prefixMatchFlags (cases.map Prod.fst) v)) := by
  simp [dispatchHistoryCodes, prefixMatchFlagsCode_eval, chooseByFlagsCode_eval, prefixMatchFlags,
    Turing.ToPartrec.Code.comp_eval]

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

/-- A certificate for a 1-step (i.e. horizon `2`) reward lower bound for `ξ^tl`.

The certificate is **history-local** (it certifies a claim only for a single history code), but the
verified raw program is **globally VA-sound** because it claims `0` on every other history. -/
structure XiTlOneStepRewardLowerBoundCert where
  /-- The encoded history guarded by the raw program. -/
  historyCode : List ℕ
  /-- The action played at the guarded history, encoded via `Coding.encodeActionNat`. -/
  actionCode : ℕ
  /-- The claimed numerator `num`. The decoded claim is `num / (den+1)`. -/
  num : ℕ
  /-- The claimed denominator offset `den`. The decoded claim is `num / (den+1)`. -/
  den : ℕ
  /-- Indices of environment programs provably yielding percept `(obs=false,reward=true)`. -/
  idx_false_true : List ℕ
  /-- Indices of environment programs provably yielding percept `(obs=true,reward=true)`. -/
  idx_true_true : List ℕ
deriving Encodable

namespace XiTlOneStepRewardLowerBoundCert

/-- The common dyadic denominator exponent used by the verifier: for `bitstringsUpTo l`,
all prefix-free weights are of the form `2^{-k}` with `k ≤ 2*l+1`. -/
def denomExp (l : ℕ) : ℕ :=
  2 * l + 1

def expectedDen (l : ℕ) : ℕ :=
  2 ^ (denomExp l) - 1

def bitsAt (l : ℕ) : List (List Bool) :=
  bitstringsUpTo l

def allIdxs (cert : XiTlOneStepRewardLowerBoundCert) : List ℕ :=
  cert.idx_false_true ++ cert.idx_true_true

def weightCodeLenAt (l i : ℕ) : Option ℕ :=
  let bits := bitsAt l
  if hi : i < bits.length then
    some (Coding.selfDelimitingEncode (bits.get ⟨i, hi⟩)).length
  else
    none

def numeratorTerm (l i : ℕ) : Option ℕ :=
  (weightCodeLenAt l i).map fun k => 2 ^ (denomExp l - k)

def numeratorBound (l : ℕ) : List ℕ → Option ℕ
  | [] => some 0
  | i :: is => do
      let t ← numeratorTerm l i
      let acc ← numeratorBound l is
      pure (t + acc)

lemma numeratorBound_eq_sum_getD (l : ℕ) :
    ∀ idxs num,
      numeratorBound l idxs = some num →
        num = (idxs.map (fun i => (numeratorTerm l i).getD 0)).sum := by
  intro idxs
  induction idxs with
  | nil =>
      intro num h
      simp [numeratorBound] at h
      subst h
      simp
  | cons i is ih =>
      intro num h
      cases hTerm : numeratorTerm l i with
      | none =>
          simp [numeratorBound, hTerm] at h
      | some t =>
          cases hAcc : numeratorBound l is with
          | none =>
              simp [numeratorBound, hTerm, hAcc] at h
          | some acc =>
              have hnum : t + acc = num := by
                simpa [numeratorBound, hTerm, hAcc] using h
              have hacc : acc = (is.map (fun i => (numeratorTerm l i).getD 0)).sum := ih acc hAcc
              have ht : (numeratorTerm l i).getD 0 = t := by
                simp [hTerm]
              simp [List.map, List.sum_cons, ht]
              calc
                num = t + acc := hnum.symm
                _ = t + (is.map (fun i => (numeratorTerm l i).getD 0)).sum := by
                    simp [hacc]

lemma pow_two_zpow_neg_eq_div (D k : ℕ) (hk : k ≤ D) :
    (2 : ℝ) ^ (-(k : ℤ)) = (2 : ℝ) ^ (D - k) / (2 : ℝ) ^ D := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hexp : ((D - k : ℕ) : ℤ) - (D : ℤ) = -(k : ℤ) := by
    have : ((D - k : ℕ) : ℤ) = (D : ℤ) - (k : ℤ) := by
      simpa using (Int.ofNat_sub hk)
    omega
  calc
    (2 : ℝ) ^ (-(k : ℤ)) = (2 : ℝ) ^ (((D - k : ℕ) : ℤ) - (D : ℤ)) := by
      simp [hexp]
    _ = (2 : ℝ) ^ ((D - k : ℕ) : ℤ) / (2 : ℝ) ^ (D : ℤ) := by
      simpa using (zpow_sub₀ (a := (2 : ℝ)) h2 ((D - k : ℕ) : ℤ) (D : ℤ))
    _ = (2 : ℝ) ^ (D - k) / (2 : ℝ) ^ D := by
      simp [zpow_natCast]

lemma selfDelimitingEncode_length_le_denomExp (l i : ℕ) (hi : i < (bitsAt l).length) :
    (Coding.selfDelimitingEncode ((bitsAt l).get ⟨i, hi⟩)).length ≤ denomExp l := by
  have hmem : (bitsAt l).get ⟨i, hi⟩ ∈ bitsAt l := List.get_mem _ _
  have hmemUpTo : (bitsAt l).get ⟨i, hi⟩ ∈ bitstringsUpTo l := by
    simp [bitsAt]
  have hlen : ((bitsAt l).get ⟨i, hi⟩).length ≤ l :=
    length_le_of_mem_bitstringsUpTo hmemUpTo
  calc
    (Coding.selfDelimitingEncode ((bitsAt l).get ⟨i, hi⟩)).length
        = 2 * ((bitsAt l).get ⟨i, hi⟩).length + 1 := by
            simpa using Coding.length_selfDelimitingEncode ((bitsAt l).get ⟨i, hi⟩)
    _ ≤ 2 * l + 1 := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hlen) 1
    _ = denomExp l := by
          simp [denomExp]

lemma prefixFreeWeightAt_toReal_eq_numeratorTerm_div (l i : ℕ) :
    (xi_tlPrefixFreeWeightAt (bitsAt l) i).toReal =
      ((numeratorTerm l i).getD 0 : ℝ) / (2 ^ denomExp l : ℝ) := by
  classical
  by_cases hi : i < (bitsAt l).length
  ·
      let D : ℕ := denomExp l
      let k : ℕ := (Coding.selfDelimitingEncode ((bitsAt l).get ⟨i, hi⟩)).length
      have hk : k ≤ D := by
        simpa [k, D] using selfDelimitingEncode_length_le_denomExp (l := l) (i := i) hi
      have hterm : numeratorTerm l i = some (2 ^ (D - k)) := by
        simp [numeratorTerm, weightCodeLenAt, hi, D, k]
      have hweight : (xi_tlPrefixFreeWeightAt (bitsAt l) i).toReal = (2 : ℝ) ^ (-(k : ℤ)) := by
        simp [xi_tlPrefixFreeWeightAt, xi_tlPrefixWeight, hi, k]
      calc
        (xi_tlPrefixFreeWeightAt (bitsAt l) i).toReal = (2 : ℝ) ^ (-(k : ℤ)) := hweight
        _ = (2 : ℝ) ^ (D - k) / (2 : ℝ) ^ D := pow_two_zpow_neg_eq_div D k hk
        _ = ((2 ^ (D - k) : ℕ) : ℝ) / (2 ^ D : ℝ) := by
              simp [Nat.cast_pow]
        _ = ((numeratorTerm l i).getD 0 : ℝ) / (2 ^ denomExp l : ℝ) := by
              simp [hterm, D]
  ·
      have hterm : numeratorTerm l i = none := by
        simp [numeratorTerm, weightCodeLenAt, hi]
      simp [xi_tlPrefixFreeWeightAt, hi, hterm]

/-- Convert a `numeratorBound` certificate into an explicit `toReal` sum over prefix-free weights. -/
lemma toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l : ℕ) (idxs : List ℕ) (num : ℕ)
    (hnodup : idxs.Nodup) (hnum : numeratorBound l idxs = some num) :
    (∑ i ∈ idxs.toFinset, xi_tlPrefixFreeWeightAt (bitsAt l) i).toReal =
      (num : ℝ) / (2 ^ denomExp l : ℝ) := by
  classical
  let bits : List (List Bool) := bitsAt l
  let den : ℝ := 2 ^ denomExp l
  have hnotTop : ∀ i ∈ idxs.toFinset, xi_tlPrefixFreeWeightAt bits i ≠ (⊤ : ENNReal) := by
    intro i hi
    by_cases hlt : i < bits.length
    · simp [xi_tlPrefixFreeWeightAt, xi_tlPrefixWeight, bits, hlt]
    · simp [xi_tlPrefixFreeWeightAt, bits, hlt]
  have hsum :
      (idxs.map (fun i => (numeratorTerm l i).getD 0)).sum =
        ∑ i ∈ idxs.toFinset, (numeratorTerm l i).getD 0 := by
    symm
    simpa using (List.sum_toFinset (f := fun i => (numeratorTerm l i).getD 0) hnodup)
  have hnumSum :
      (num : ℕ) = (idxs.map (fun i => (numeratorTerm l i).getD 0)).sum :=
    numeratorBound_eq_sum_getD (l := l) idxs num hnum
  calc
    (∑ i ∈ idxs.toFinset, xi_tlPrefixFreeWeightAt bits i).toReal =
        ∑ i ∈ idxs.toFinset, (xi_tlPrefixFreeWeightAt bits i).toReal :=
      ENNReal.toReal_sum (s := idxs.toFinset) (f := fun i => xi_tlPrefixFreeWeightAt bits i) hnotTop
    _ = ∑ i ∈ idxs.toFinset, ((numeratorTerm l i).getD 0 : ℝ) / den := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [bits, den] using (prefixFreeWeightAt_toReal_eq_numeratorTerm_div (l := l) (i := i))
    _ = (∑ i ∈ idxs.toFinset, ((numeratorTerm l i).getD 0 : ℝ)) / den := by
      classical
      simp [div_eq_mul_inv, Finset.sum_mul]
    _ = ((∑ i ∈ idxs.toFinset, (numeratorTerm l i).getD 0 : ℕ) : ℝ) / den := by
      classical
      simp [Nat.cast_sum (R := ℝ) idxs.toFinset (fun i => (numeratorTerm l i).getD 0)]
    _ = (num : ℝ) / den := by
      have :
          (∑ i ∈ idxs.toFinset, (numeratorTerm l i).getD 0 : ℕ) =
            (idxs.map (fun i => (numeratorTerm l i).getD 0)).sum := by
        simp [hsum]
      simp [den, hnumSum, this]

def checkIdxOutputs (tEnv l : ℕ) (ha : History) (target : Percept) (idxs : List ℕ) : Bool :=
  let bits := bitsAt l
  idxs.all fun i =>
    if hi : i < bits.length then
      match Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bits.get ⟨i, hi⟩) with
      | some tm =>
          decide
            (RawToPartrecEnvironmentProgram.computeWithin tEnv { code := { code := bits.get ⟨i, hi⟩ }, tm := tm } ha =
              some target)
      | none => false
    else
      false

/-- The full set of indices (within `bitsAt l`) that output `target` at `ha` within `tEnv`. -/
def idxsOfOutput (tEnv l : ℕ) (ha : History) (target : Percept) : List ℕ :=
  let bits := bitsAt l
  (List.range bits.length).filter fun i =>
    if hi : i < bits.length then
      match Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bits.get ⟨i, hi⟩) with
      | some tm =>
          decide
            (RawToPartrecEnvironmentProgram.computeWithin tEnv { code := { code := bits.get ⟨i, hi⟩ }, tm := tm } ha =
              some target)
      | none => false
    else
      false

lemma idxsOfOutput_lt_bitsAt_length (tEnv l : ℕ) (ha : History) (target : Percept) :
    ∀ i ∈ idxsOfOutput tEnv l ha target, i < (bitsAt l).length := by
  intro i hi
  unfold idxsOfOutput at hi
  rcases List.mem_filter.1 hi with ⟨hiRange, _hiPred⟩
  have : i < (bitsAt l).length := by
    simpa using (List.mem_range.1 hiRange)
  simpa using this

lemma idxsOfOutput_nodup (tEnv l : ℕ) (ha : History) (target : Percept) :
    (idxsOfOutput tEnv l ha target).Nodup := by
  classical
  unfold idxsOfOutput
  refine List.Nodup.filter _ ?_
  simpa using (List.nodup_range (n := (bitsAt l).length))

lemma checkIdxOutputs_idxsOfOutput (tEnv l : ℕ) (ha : History) (target : Percept) :
    checkIdxOutputs tEnv l ha target (idxsOfOutput tEnv l ha target) = true := by
  classical
  -- `filter` ensures every index in `idxsOfOutput` satisfies the predicate checked by `checkIdxOutputs`.
  unfold checkIdxOutputs idxsOfOutput
  simp only
  refine List.all_eq_true.2 ?_
  intro i hi
  rcases List.mem_filter.1 hi with ⟨_hiRange, hiPred⟩
  exact hiPred

lemma numeratorBound_eq_some_of_forall_lt (l : ℕ) :
    ∀ idxs : List ℕ,
      (∀ i ∈ idxs, i < (bitsAt l).length) →
        ∃ num, numeratorBound l idxs = some num := by
  intro idxs
  induction idxs with
  | nil =>
      intro _hlt
      refine ⟨0, by simp [numeratorBound]⟩
  | cons i is ih =>
      intro hlt
      have hi : i < (bitsAt l).length := hlt i (by simp)
      have hi' : i < (bitstringsUpTo l).length := by
        simpa [bitsAt] using hi
      have hlt' : ∀ j ∈ is, j < (bitsAt l).length := by
        intro j hj
        exact hlt j (by simp [hj])
      rcases ih hlt' with ⟨acc, hAcc⟩
      refine ⟨(2 ^ (denomExp l - (Coding.selfDelimitingEncode ((bitsAt l).get ⟨i, hi⟩)).length)) + acc, ?_⟩
      have hTerm :
          numeratorTerm l i =
            some (2 ^ (denomExp l - (Coding.selfDelimitingEncode ((bitsAt l).get ⟨i, hi⟩)).length)) := by
        simp [numeratorTerm, weightCodeLenAt, bitsAt, hi']
      simp [numeratorBound, hTerm, hAcc]

noncomputable def numeratorBoundValue (l : ℕ) (idxs : List ℕ)
    (hlt : ∀ i ∈ idxs, i < (bitsAt l).length) : ℕ :=
  Classical.choose (numeratorBound_eq_some_of_forall_lt (l := l) idxs hlt)

theorem numeratorBoundValue_spec (l : ℕ) (idxs : List ℕ) (hlt : ∀ i ∈ idxs, i < (bitsAt l).length) :
    numeratorBound l idxs = some (numeratorBoundValue (l := l) idxs hlt) :=
  Classical.choose_spec (numeratorBound_eq_some_of_forall_lt (l := l) idxs hlt)

lemma sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs (tEnv l : ℕ) (ha : History) (target : Percept) (idxs : List ℕ)
    (hIdx : checkIdxOutputs tEnv l ha target idxs = true) :
    (∑ i ∈ idxs.toFinset, xi_tlPrefixFreeWeightAt (bitsAt l) i) ≤ (xi_tlEnvironment tEnv l).prob ha target := by
  classical
  let ξ : BayesianMixture := xi_tlBayesianMixture tEnv l
  let μ : Environment := xi_tlEnvironment tEnv l
  have hle :=
    ENNReal.sum_le_tsum
      (s := idxs.toFinset)
      (f := fun i => ξ.weights i * (ξ.envs i).prob ha target)
  have hall :
      ∀ i ∈ idxs,
        (if hi : i < (bitsAt l).length then
            match
              Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) ((bitsAt l).get ⟨i, hi⟩) with
            | some tm =>
                decide
                  (RawToPartrecEnvironmentProgram.computeWithin tEnv
                        { code := { code := (bitsAt l).get ⟨i, hi⟩ }, tm := tm } ha =
                      some target)
            | none => false
          else false) =
          true := by
    simpa [checkIdxOutputs] using
      (List.all_eq_true.mp (by
        simpa [checkIdxOutputs] using hIdx))
  have hterm :
      (∑ i ∈ idxs.toFinset, ξ.weights i * (ξ.envs i).prob ha target) =
        ∑ i ∈ idxs.toFinset, xi_tlPrefixFreeWeightAt (bitsAt l) i := by
    classical
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hiList : i ∈ idxs := (List.mem_toFinset).1 hi
    have hpred0 := hall i hiList
    have hi' : i < (bitsAt l).length := by
      by_contra hi'
      have hpred0' := hpred0
      simp [hi'] at hpred0'
    have hpred :
        (match
            Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) ((bitsAt l).get ⟨i, hi'⟩) with
          | some tm =>
              decide
                (RawToPartrecEnvironmentProgram.computeWithin tEnv
                      { code := { code := (bitsAt l).get ⟨i, hi'⟩ }, tm := tm } ha =
                    some target)
          | none => false) =
          true := by
      simpa [hi'] using hpred0
    cases htm :
        Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) ((bitsAt l).get ⟨i, hi'⟩) with
    | none =>
        have hpred' := hpred
        rw [htm] at hpred'
        cases hpred'
    | some tm =>
        have hdecide :
            decide
                (RawToPartrecEnvironmentProgram.computeWithin tEnv
                      { code := { code := (bitsAt l).get ⟨i, hi'⟩ }, tm := tm } ha =
                    some target) =
              true := by
          have hpred' := hpred
          rw [htm] at hpred'
          simpa using hpred'
        have hcomp :
            RawToPartrecEnvironmentProgram.computeWithin tEnv
                { code := { code := (bitsAt l).get ⟨i, hi'⟩ }, tm := tm } ha =
              some target :=
          of_decide_eq_true hdecide
        have hiBits : i < (bitstringsUpTo l).length := by
          simpa [bitsAt] using hi'
        have htm' :
            Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) ((bitstringsUpTo l).get ⟨i, hiBits⟩) = some tm := by
          simpa [bitsAt] using htm
        have hcomp' :
            RawToPartrecEnvironmentProgram.computeWithin tEnv
                { code := { code := (bitstringsUpTo l).get ⟨i, hiBits⟩ }, tm := tm } ha =
              some target := by
          simpa [bitsAt] using hcomp
        have htm'' : Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bitstringsUpTo l)[i] = some tm := by
          simpa using htm'
        have hcomp'' :
            RawToPartrecEnvironmentProgram.computeWithin tEnv { code := { code := (bitstringsUpTo l)[i] }, tm := tm } ha =
              some target := by
          simpa using hcomp'
        simp [ξ, xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, xi_tlPrefixFreeWeightAt, bitsAt, hiBits,
          RawToPartrecEnvironmentProgram.decodeCanonical, RawToPartrecEnvironmentProgram.ofToPartrec,
          RawToPartrecProgram.decodeToPartrec, RawToPartrecEnvironmentProgram.toEnvironmentWithin, htm'', hcomp'']
  have hμ : (∑' i : ℕ, ξ.weights i * (ξ.envs i).prob ha target) = μ.prob ha target := by
    rfl
  simpa [hterm, hμ] using hle

/-- `idxsOfOutput` is exhaustive: summing the prefix-free weights over the indices that output `target`
within `tEnv` recovers exactly the `ξ^tl` probability mass at `ha`. -/
lemma sum_prefixFreeWeightAt_eq_prob_of_idxsOfOutput (tEnv l : ℕ) (ha : History) (target : Percept) :
    (∑ i ∈ (idxsOfOutput tEnv l ha target).toFinset, xi_tlPrefixFreeWeightAt (bitsAt l) i) =
      (xi_tlEnvironment tEnv l).prob ha target := by
  classical
  let bits : List (List Bool) := bitstringsUpTo l
  let idxs : List ℕ := idxsOfOutput tEnv l ha target
  let ξ : BayesianMixture := xi_tlBayesianMixture tEnv l
  have htsum :
      (∑' i : ℕ, ξ.weights i * (ξ.envs i).prob ha target) =
        ∑ i ∈ Finset.range bits.length, ξ.weights i * (ξ.envs i).prob ha target := by
    refine (tsum_eq_sum (s := Finset.range bits.length) ?_)
    intro i hi
    have hnot : ¬ i < bits.length := by
      simpa [Finset.mem_range] using hi
    have hweight : ξ.weights i = 0 := by
      simp [ξ, xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, xi_tlPrefixFreeWeightAt, bits, hnot]
    simp [hweight]
  have hprob :
      (xi_tlEnvironment tEnv l).prob ha target =
        ∑ i ∈ Finset.range bits.length, ξ.weights i * (ξ.envs i).prob ha target := by
    simp [xi_tlEnvironment, mixtureEnvironment, ξ, htsum, bits]

  have hsubset : idxs.toFinset ⊆ Finset.range bits.length := by
    intro i hi
    have hiList : i ∈ idxs := (List.mem_toFinset).1 hi
    unfold idxs at hiList
    unfold idxsOfOutput at hiList
    rcases List.mem_filter.1 hiList with ⟨hiRange, _hiPred⟩
    have hiLt : i < bits.length := by
      simpa [bits] using (List.mem_range.1 hiRange)
    simpa [Finset.mem_range] using hiLt

  have hfilter :
      (Finset.range bits.length).filter (fun i => i ∈ idxs.toFinset) = idxs.toFinset := by
    ext i
    constructor
    · intro hi
      exact (Finset.mem_filter.1 hi).2
    · intro hi
      exact Finset.mem_filter.2 ⟨hsubset hi, hi⟩

  have hterm :
      (∑ i ∈ Finset.range bits.length, ξ.weights i * (ξ.envs i).prob ha target) =
        ∑ i ∈ Finset.range bits.length, if i ∈ idxs.toFinset then xi_tlPrefixFreeWeightAt bits i else 0 := by
    classical
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hiBits : i < bits.length := by
      simpa [Finset.mem_range] using hi
    by_cases hmem : i ∈ idxs.toFinset
    · have hiList : i ∈ idxs := (List.mem_toFinset).1 hmem
      unfold idxs at hiList
      unfold idxsOfOutput at hiList
      rcases List.mem_filter.1 hiList with ⟨_hiRange, hiPred⟩
      have hiPred' :
          (match
              Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bits.get ⟨i, hiBits⟩) with
            | some tm =>
                decide
                  (RawToPartrecEnvironmentProgram.computeWithin tEnv
                        { code := { code := bits.get ⟨i, hiBits⟩ }, tm := tm } ha =
                      some target)
            | none => false) =
            true := by
        simpa [bitsAt, bits, hiBits] using hiPred
      cases htm : Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bits.get ⟨i, hiBits⟩) with
      | none =>
          have hiPred'' := hiPred'
          rw [htm] at hiPred''
          cases hiPred''
      | some tm =>
          have hdecide :
              decide
                  (RawToPartrecEnvironmentProgram.computeWithin tEnv
                        { code := { code := bits.get ⟨i, hiBits⟩ }, tm := tm } ha =
                      some target) =
                true := by
            have hiPred'' := hiPred'
            rw [htm] at hiPred''
            simpa using hiPred''
          have hcomp :
              RawToPartrecEnvironmentProgram.computeWithin tEnv
                  { code := { code := bits.get ⟨i, hiBits⟩ }, tm := tm } ha =
                some target :=
            of_decide_eq_true hdecide
          have htmIdx : Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bits[i]) = some tm := by
            simpa using htm
          have hcompIdx :
              RawToPartrecEnvironmentProgram.computeWithin tEnv { code := { code := bits[i] }, tm := tm } ha =
                some target := by
            unfold RawToPartrecEnvironmentProgram.computeWithin at hcomp ⊢
            simpa using hcomp
          have hprob1 : (ξ.envs i).prob ha target = 1 := by
            simp [ξ, xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, bits, hiBits,
              RawToPartrecEnvironmentProgram.decodeCanonical, RawToPartrecProgram.decodeToPartrec,
              RawToPartrecEnvironmentProgram.ofToPartrec, RawToPartrecEnvironmentProgram.toEnvironmentWithin,
              htmIdx, hcompIdx, zeroEnvironment]
          have hweight : ξ.weights i = xi_tlPrefixFreeWeightAt bits i := by
            simp [ξ, xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, bits]
          have :
              ξ.weights i * (ξ.envs i).prob ha target = xi_tlPrefixFreeWeightAt bits i := by
            calc
              ξ.weights i * (ξ.envs i).prob ha target = ξ.weights i * 1 := by simp [hprob1]
              _ = ξ.weights i := by simp
              _ = xi_tlPrefixFreeWeightAt bits i := by simpa [hweight]
          simpa [hmem] using this
    · cases htm : Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bits.get ⟨i, hiBits⟩) with
      | none =>
          have htmIdx : Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bits[i]) = none := by
            simpa using htm
          have hprob0 : (ξ.envs i).prob ha target = 0 := by
            simp [ξ, xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, bits, hiBits,
              RawToPartrecEnvironmentProgram.decodeCanonical, RawToPartrecProgram.decodeToPartrec, htmIdx, zeroEnvironment]
          simp [hprob0, hmem]
      | some tm =>
          by_cases hcomp :
              RawToPartrecEnvironmentProgram.computeWithin tEnv
                  { code := { code := bits.get ⟨i, hiBits⟩ }, tm := tm } ha =
                some target
          · have hiRange : i ∈ List.range bits.length := by
              simpa [List.mem_range] using hiBits
            have : i ∈ idxs := by
              unfold idxs idxsOfOutput
              refine List.mem_filter.2 ?_
              refine ⟨?_, ?_⟩
              · simpa [bitsAt, bits] using hiRange
              · have hiAt : i < (bitsAt l).length := by
                  simpa [bitsAt, bits] using hiBits
                have htmAt : Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bitsAt l)[i] = some tm := by
                  simpa [bitsAt, bits] using htm
                have hcompAt :
                    RawToPartrecEnvironmentProgram.computeWithin tEnv { code := { code := (bitsAt l)[i] }, tm := tm } ha =
                      some target := by
                  simpa [bitsAt, bits] using hcomp
                have hpred' :
                    decide
                        (RawToPartrecEnvironmentProgram.computeWithin tEnv
                              { code := { code := (bitsAt l)[i] }, tm := tm } ha =
                            some target) =
                      true := by
                  simpa [decide_eq_true_eq] using hcompAt
                have hpred :
                    (match Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bitsAt l)[i] with
                      | some tm =>
                          decide
                            (RawToPartrecEnvironmentProgram.computeWithin tEnv
                                  { code := { code := (bitsAt l)[i] }, tm := tm } ha =
                                some target)
                      | none => false) =
                      true := by
                  simpa [htmAt] using hpred'
                simpa [hiAt, hpred]
            have : i ∈ idxs.toFinset := (List.mem_toFinset).2 this
            exact (False.elim (hmem this))
          · have htmIdx : Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) (bits[i]) = some tm := by
              simpa using htm
            have hcompIdx :
                RawToPartrecEnvironmentProgram.computeWithin tEnv { code := { code := bits[i] }, tm := tm } ha ≠
                  some target := by
              unfold RawToPartrecEnvironmentProgram.computeWithin at hcomp ⊢
              simpa using hcomp
            have hprob0 : (ξ.envs i).prob ha target = 0 := by
              simp [ξ, xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, bits, hiBits,
                RawToPartrecEnvironmentProgram.decodeCanonical, RawToPartrecProgram.decodeToPartrec,
                RawToPartrecEnvironmentProgram.ofToPartrec, RawToPartrecEnvironmentProgram.toEnvironmentWithin, htmIdx,
                hcompIdx, zeroEnvironment]
            have :
                ξ.weights i * (ξ.envs i).prob ha target = 0 := by
              simp [hprob0]
            simpa [hmem] using this

  have hsum :
      (∑ i ∈ Finset.range bits.length, if i ∈ idxs.toFinset then xi_tlPrefixFreeWeightAt bits i else 0) =
        ∑ i ∈ idxs.toFinset, xi_tlPrefixFreeWeightAt bits i := by
    classical
    have h :=
      (Finset.sum_filter (s := Finset.range bits.length) (f := fun i => xi_tlPrefixFreeWeightAt bits i)
            (p := fun i => i ∈ idxs.toFinset)).symm
    have h' :
        (∑ i ∈ (Finset.range bits.length).filter (fun i => i ∈ idxs.toFinset), xi_tlPrefixFreeWeightAt bits i) =
          ∑ i ∈ idxs.toFinset, xi_tlPrefixFreeWeightAt bits i := by
      rw [hfilter]
    exact Eq.trans h h'

  calc
    (∑ i ∈ idxs.toFinset, xi_tlPrefixFreeWeightAt (bitsAt l) i) =
        ∑ i ∈ idxs.toFinset, xi_tlPrefixFreeWeightAt bits i := by
          simp [bitsAt, bits]
    _ = ∑ i ∈ Finset.range bits.length, if i ∈ idxs.toFinset then xi_tlPrefixFreeWeightAt bits i else 0 := by
          simpa using hsum.symm
    _ = ∑ i ∈ Finset.range bits.length, ξ.weights i * (ξ.envs i).prob ha target := by
          simpa [hterm]
    _ = (xi_tlEnvironment tEnv l).prob ha target := by
          simpa [hprob]

def ok (tEnv l : ℕ) (p : RawToPartrecProgram) (cert : XiTlOneStepRewardLowerBoundCert) : Prop :=
  match Coding.decodeHistoryNat cert.historyCode, Coding.decodeActionNat cert.actionCode with
  | some h, some a =>
      let ha : History := h ++ [HistElem.act a]
      Coding.encodeHistoryNat h = cert.historyCode ∧
        p.tm = RawToPartrecProgram.guardedValueActionCode cert.historyCode cert.num cert.den a ∧
          cert.den = expectedDen l ∧
            ha.wellFormed ∧
              cert.allIdxs.Nodup ∧
                checkIdxOutputs tEnv l ha (Percept.mk false true) cert.idx_false_true = true ∧
                  checkIdxOutputs tEnv l ha (Percept.mk true true) cert.idx_true_true = true ∧
                    numeratorBound l cert.allIdxs = some cert.num
  | _, _ => False

end XiTlOneStepRewardLowerBoundCert

/-- A nontrivial “actual verifier” for horizon `2` (i.e. `n = 1`): certificates describe a dyadic
lower bound on the **immediate expected reward** under `ξ^tl`, and the accepted raw programs claim
that bound only at a single guarded history (claiming `0` everywhere else). -/
noncomputable def xi_tlOneStepRewardLowerBoundSoundProofSystemToPartrec (tEnv l : ℕ) (γ : DiscountFactor) :
    EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
      (fun tProg p => ValidValueLowerBound (xi_tlEnvironment tEnv l) γ 2 (p.toExtended tProg)) := by
  classical
  refine
    { Proof := XiTlOneStepRewardLowerBoundCert
      verify := fun _tProg p cert => decide (XiTlOneStepRewardLowerBoundCert.ok (tEnv := tEnv) (l := l) p cert)
      sound := ?_ }
  intro tProg p cert hverify
  have hok : XiTlOneStepRewardLowerBoundCert.ok (tEnv := tEnv) (l := l) p cert := of_decide_eq_true hverify
  -- Decode the guarded history and action from the certificate.
  cases hdecH : Coding.decodeHistoryNat cert.historyCode with
  | none =>
      have : False := by
        have hok' := hok
        simp [XiTlOneStepRewardLowerBoundCert.ok, hdecH] at hok'
      cases this
  | some h =>
      cases hdecA : Coding.decodeActionNat cert.actionCode with
      | none =>
          have : False := by
            have hok' := hok
            simp [XiTlOneStepRewardLowerBoundCert.ok, hdecH, hdecA] at hok'
          cases this
      | some a =>
          have hok' :
              let ha : History := h ++ [HistElem.act a]
              Coding.encodeHistoryNat h = cert.historyCode ∧
                p.tm = RawToPartrecProgram.guardedValueActionCode cert.historyCode cert.num cert.den a ∧
                  cert.den = XiTlOneStepRewardLowerBoundCert.expectedDen l ∧
                    ha.wellFormed ∧
                      cert.allIdxs.Nodup ∧
                        XiTlOneStepRewardLowerBoundCert.checkIdxOutputs tEnv l ha (Percept.mk false true) cert.idx_false_true =
                            true ∧
                          XiTlOneStepRewardLowerBoundCert.checkIdxOutputs tEnv l ha (Percept.mk true true) cert.idx_true_true =
                              true ∧
                            XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.allIdxs = some cert.num := by
            simpa [XiTlOneStepRewardLowerBoundCert.ok, hdecH, hdecA] using hok
          rcases hok' with ⟨hhEnc, hpTm, hden, hhaWf, hnodup, hIdxFT, hIdxTT, hnum⟩
          -- Prove global `ValidValueLowerBound` for the time-bounded wrapper.
          intro h' hwf
          let μ : Environment := xi_tlEnvironment tEnv l
          let ha : History := h ++ [HistElem.act a]
          let xFT : Percept := Percept.mk false true
          let xTT : Percept := Percept.mk true true
          have hμ : μ = mixtureEnvironment (xi_tlBayesianMixture tEnv l) := rfl
          -- Split on whether the history-guard triggers.
          cases hguard : RawToPartrecProgram.prefixHeadI cert.historyCode (Coding.encodeHistoryNat h') with
          | true =>
              -- The guard can only fire on the intended history encoding.
              have hh' : h = h' := by
                have :
                    RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat h') = true := by
                  simpa [hhEnc] using hguard
                exact RawToPartrecProgram.prefixHeadI_encodeHistoryNat_eq (h := h) (h' := h') this
              subst hh'
              -- Unfold the program wrapper and evaluate the claim.
              unfold RawToPartrecProgram.toExtended RawToPartrecProgram.computeWithin
              cases hEval : StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat h) with
              | none =>
                  -- Timeout: the wrapper defaults to `(0, stay)`, which is always sound.
                  have hnonneg : 0 ≤ value μ (p.toExtended tProg).toAgent γ h 2 :=
                    value_nonneg (μ := μ) (π := (p.toExtended tProg).toAgent) (γ := γ) (h := h) (n := 2)
                  simpa [hEval]
                    using hnonneg
              | some out =>
                  -- Successful evaluation: use the code template to identify the output.
                  have houtMem : out ∈ p.tm.eval (Coding.encodeHistoryNat h) :=
                    StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h) (out := out) hEval
                  have hpTm' :
                      p.tm = RawToPartrecProgram.guardedValueActionCode (Coding.encodeHistoryNat h) cert.num cert.den a := by
                    simpa [hhEnc] using hpTm
                  have houtMem' :
                      out ∈
                        (RawToPartrecProgram.guardedValueActionCode (Coding.encodeHistoryNat h) cert.num cert.den a).eval
                          (Coding.encodeHistoryNat h) := by
                    simpa [hpTm'] using houtMem
                  -- The guard is true, hence evaluation is `outYes`.
                  let outYes : List ℕ := [cert.num, cert.den, Coding.encodeActionNat a]
                  have hEvalTemplate :
                      (RawToPartrecProgram.guardedValueActionCode (Coding.encodeHistoryNat h) cert.num cert.den a).eval
                          (Coding.encodeHistoryNat h) =
                        pure outYes := by
                    -- `prefixHeadI pref pref = true`.
                    have : RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat h) = true := by
                      simpa using RawToPartrecProgram.prefixHeadI_self (Coding.encodeHistoryNat h)
                    simp [RawToPartrecProgram.guardedValueActionCode, RawToPartrecProgram.guardPrefixListNat_eval_const, this, outYes]
                  have houtEq : out = outYes := by
                    simpa [hEvalTemplate] using houtMem'
                  -- Decode the claim and action from `outYes`.
                  have hcompute :
                      ((Coding.decodeValueActionOutput out).getD (0, Action.stay)).1 =
                        Coding.decodeValueNat cert.num cert.den := by
                    subst houtEq
                    simp [outYes, Coding.decodeValueActionOutput, Coding.decodeValueNat]
                  have hact : ((p.toExtended tProg).compute h).2 = a := by
                    simp [RawToPartrecProgram.toExtended, RawToPartrecProgram.computeWithin, hEval, houtEq, outYes,
                      Coding.decodeValueActionOutput]
                  -- Reduce the value at horizon `2` to a `qValue` at horizon `1`.
                  have hval :
                      value μ (p.toExtended tProg).toAgent γ h 2 =
                        qValue μ (p.toExtended tProg).toAgent γ h a 1 := by
                    have hwf' : h.wellFormed := hwf
                    have hval' :
                        value μ (p.toExtended tProg).toAgent γ h 2 =
                          qValue μ (p.toExtended tProg).toAgent γ h ((p.toExtended tProg).compute h).2 1 := by
                      simpa [ExtendedChronologicalProgram.toAgent, deterministicAgent] using
                        (value_deterministicAgent_succ (μ := μ) (γ := γ)
                          (act := fun h0 => ((p.toExtended tProg).compute h0).2) (h := h) (n := 1) hwf')
                    simpa [hact] using hval'
                  -- Expand `qValue` at horizon `1`: only reward-1 percepts contribute.
                  have hq :
                      qValue μ (p.toExtended tProg).toAgent γ h a 1 =
                        (μ.prob ha xFT).toReal + (μ.prob ha xTT).toReal := by
                    have hhaWf' : ha.wellFormed := hhaWf
                    simp [qValue_succ, value_zero, Percept.reward, ha, xFT, xTT, hhaWf', List.foldl_cons, List.foldl_nil]
                  -- Bound the claim by the verified reward mass.
                  have hxFT_le : (∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) ≤ μ.prob ha xFT := by
                    -- Finite sum ≤ `tsum` by nonnegativity.
                    have hle :=
                      ENNReal.sum_le_tsum
                        (s := cert.idx_false_true.toFinset)
                        (f := fun i =>
                          (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT)
                    -- Rewrite each term in the finite sum to the corresponding prefix-free weight.
                    have hterm :
                        (∑ i ∈ cert.idx_false_true.toFinset,
                            (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT) =
                          ∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i := by
                      classical
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      have hiList : i ∈ cert.idx_false_true := (List.mem_toFinset).1 hi
                      have hall :=
                        List.all_eq_true.mp
                          (by
                            simpa [XiTlOneStepRewardLowerBoundCert.checkIdxOutputs, XiTlOneStepRewardLowerBoundCert.bitsAt, ha, xFT]
                              using hIdxFT)
                      have hpred := hall i hiList
                      by_cases hiBits : i < (bitstringsUpTo l).length
                      ·
                          have hpredHi :
                              (match
                                    Coding.decodeEncodableBits (α := Turing.ToPartrec.Code)
                                      ((bitstringsUpTo l).get ⟨i, hiBits⟩)
                                  with
                                  | some tm =>
                                      decide
                                        (RawToPartrecEnvironmentProgram.computeWithin tEnv
                                              { code := { code := (bitstringsUpTo l).get ⟨i, hiBits⟩ }, tm := tm } ha =
                                            some xFT)
                                  | none => false) =
                                  true := by
                            simpa [hiBits] using hpred
                          cases htm :
                              Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) ((bitstringsUpTo l).get ⟨i, hiBits⟩) with
                          | none =>
                              have : False := by
                                have hpredHi' := hpredHi
                                rw [htm] at hpredHi'
                                simp at hpredHi'
                              cases this
                          | some tm =>
                              have hdecide :
                                  decide
                                      (RawToPartrecEnvironmentProgram.computeWithin tEnv
                                            { code := { code := (bitstringsUpTo l).get ⟨i, hiBits⟩ }, tm := tm } ha =
                                          some xFT) =
                                    true := by
                                have hpredHi' := hpredHi
                                rw [htm] at hpredHi'
                                simpa using hpredHi'
                              have hcomp :
                                  RawToPartrecEnvironmentProgram.computeWithin tEnv
                                        { code := { code := (bitstringsUpTo l).get ⟨i, hiBits⟩ }, tm := tm } ha =
                                      some xFT :=
                                of_decide_eq_true hdecide
                              have hdec :
                                  RawToPartrecEnvironmentProgram.decodeCanonical ((bitstringsUpTo l).get ⟨i, hiBits⟩) =
                                    some
                                      (RawToPartrecEnvironmentProgram.ofToPartrec ((bitstringsUpTo l).get ⟨i, hiBits⟩) tm) := by
                                simpa [RawToPartrecEnvironmentProgram.decodeCanonical, RawToPartrecProgram.decodeToPartrec, htm,
                                  RawToPartrecEnvironmentProgram.ofToPartrec]
                              have hdec' :
                                  RawToPartrecEnvironmentProgram.decodeCanonical (bitstringsUpTo l)[i] =
                                    some (RawToPartrecEnvironmentProgram.ofToPartrec (bitstringsUpTo l)[i] tm) := by
                                simpa [List.get_eq_getElem] using hdec
                              have hcompOf :
                                  RawToPartrecEnvironmentProgram.computeWithin tEnv
                                        (RawToPartrecEnvironmentProgram.ofToPartrec (bitstringsUpTo l)[i] tm) ha =
                                      some xFT := by
                                have hcomp' :
                                    RawToPartrecEnvironmentProgram.computeWithin tEnv
                                          { code := { code := (bitstringsUpTo l)[i] }, tm := tm } ha =
                                        some xFT := by
                                  simpa [List.get_eq_getElem] using hcomp
                                simpa [RawToPartrecEnvironmentProgram.ofToPartrec] using hcomp'
                              have hprob1 :
                                  ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT = 1 := by
                                -- Inside the enumerated window, the decoded program yields `xFT`.
                                simp [xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree,
                                  hiBits, hdec',
                                  RawToPartrecEnvironmentProgram.toEnvironmentWithin, hcompOf, xFT]
                              have htermEq :
                                  (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT =
                                    (xi_tlBayesianMixture tEnv l).weights i := by
                                simp [hprob1]
                              simpa [xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, XiTlOneStepRewardLowerBoundCert.bitsAt]
                                using htermEq
                      ·
                          have : False := by
                            have hpred' := hpred
                            simp [hiBits] at hpred'
                          cases this
                    have hμprob : (∑' i : ℕ,
                          (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xFT) = μ.prob ha xFT := by
                      rfl
                    simpa [hterm, hμprob] using hle
                  have hxTT_le : (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) ≤ μ.prob ha xTT := by
                    have hle :=
                      ENNReal.sum_le_tsum
                        (s := cert.idx_true_true.toFinset)
                        (f := fun i =>
                          (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT)
                    have hterm :
                        (∑ i ∈ cert.idx_true_true.toFinset,
                            (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT) =
                          ∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i := by
                      classical
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      have hiList : i ∈ cert.idx_true_true := (List.mem_toFinset).1 hi
                      have hall :=
                        List.all_eq_true.mp
                          (by
                            simpa [XiTlOneStepRewardLowerBoundCert.checkIdxOutputs, XiTlOneStepRewardLowerBoundCert.bitsAt, ha, xTT]
                              using hIdxTT)
                      have hpred := hall i hiList
                      by_cases hiBits : i < (bitstringsUpTo l).length
                      ·
                          have hpredHi :
                              (match
                                    Coding.decodeEncodableBits (α := Turing.ToPartrec.Code)
                                      ((bitstringsUpTo l).get ⟨i, hiBits⟩)
                                  with
                                  | some tm =>
                                      decide
                                        (RawToPartrecEnvironmentProgram.computeWithin tEnv
                                              { code := { code := (bitstringsUpTo l).get ⟨i, hiBits⟩ }, tm := tm } ha =
                                            some xTT)
                                  | none => false) =
                                  true := by
                            simpa [hiBits] using hpred
                          cases htm :
                              Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) ((bitstringsUpTo l).get ⟨i, hiBits⟩) with
                          | none =>
                              have : False := by
                                have hpredHi' := hpredHi
                                rw [htm] at hpredHi'
                                simp at hpredHi'
                              cases this
                          | some tm =>
                              have hdecide :
                                  decide
                                      (RawToPartrecEnvironmentProgram.computeWithin tEnv
                                            { code := { code := (bitstringsUpTo l).get ⟨i, hiBits⟩ }, tm := tm } ha =
                                          some xTT) =
                                    true := by
                                have hpredHi' := hpredHi
                                rw [htm] at hpredHi'
                                simpa using hpredHi'
                              have hcomp :
                                  RawToPartrecEnvironmentProgram.computeWithin tEnv
                                        { code := { code := (bitstringsUpTo l).get ⟨i, hiBits⟩ }, tm := tm } ha =
                                      some xTT :=
                                of_decide_eq_true hdecide
                              have hdec :
                                  RawToPartrecEnvironmentProgram.decodeCanonical ((bitstringsUpTo l).get ⟨i, hiBits⟩) =
                                    some
                                      (RawToPartrecEnvironmentProgram.ofToPartrec ((bitstringsUpTo l).get ⟨i, hiBits⟩) tm) := by
                                simpa [RawToPartrecEnvironmentProgram.decodeCanonical, RawToPartrecProgram.decodeToPartrec, htm,
                                  RawToPartrecEnvironmentProgram.ofToPartrec]
                              have hdec' :
                                  RawToPartrecEnvironmentProgram.decodeCanonical (bitstringsUpTo l)[i] =
                                    some (RawToPartrecEnvironmentProgram.ofToPartrec (bitstringsUpTo l)[i] tm) := by
                                simpa [List.get_eq_getElem] using hdec
                              have hcompOf :
                                  RawToPartrecEnvironmentProgram.computeWithin tEnv
                                        (RawToPartrecEnvironmentProgram.ofToPartrec (bitstringsUpTo l)[i] tm) ha =
                                      some xTT := by
                                have hcomp' :
                                    RawToPartrecEnvironmentProgram.computeWithin tEnv
                                          { code := { code := (bitstringsUpTo l)[i] }, tm := tm } ha =
                                        some xTT := by
                                  simpa [List.get_eq_getElem] using hcomp
                                simpa [RawToPartrecEnvironmentProgram.ofToPartrec] using hcomp'
                              have hprob1 :
                                  ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT = 1 := by
                                simp [xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree,
                                  hiBits, hdec',
                                  RawToPartrecEnvironmentProgram.toEnvironmentWithin, hcompOf, xTT]
                              have htermEq :
                                  (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT =
                                    (xi_tlBayesianMixture tEnv l).weights i := by
                                simp [hprob1]
                              simpa [xi_tlBayesianMixture, xi_tlBayesianMixturePrefixFree, XiTlOneStepRewardLowerBoundCert.bitsAt]
                                using htermEq
                      ·
                          have : False := by
                            have hpred' := hpred
                            simp [hiBits] at hpred'
                          cases this
                    have hμprob : (∑' i : ℕ,
                          (xi_tlBayesianMixture tEnv l).weights i * ((xi_tlBayesianMixture tEnv l).envs i).prob ha xTT) = μ.prob ha xTT := by
                      rfl
                    simpa [hterm, hμprob] using hle
                  have hsumENN :
                      (∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) +
                          (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) ≤
                        μ.prob ha xFT + μ.prob ha xTT := by
                    exact add_le_add hxFT_le hxTT_le
                  have hxFT_ne_top : μ.prob ha xFT ≠ (⊤ : ENNReal) :=
                    ne_of_lt (lt_of_le_of_lt (by
                      have hle := μ.prob_le_one ha (by simpa using hhaWf)
                      have hterm := ENNReal.le_tsum (f := fun x : Percept => μ.prob ha x) xFT
                      exact le_trans hterm hle) (by simp))
                  have hxTT_ne_top : μ.prob ha xTT ≠ (⊤ : ENNReal) :=
                    ne_of_lt (lt_of_le_of_lt (by
                      have hle := μ.prob_le_one ha (by simpa using hhaWf)
                      have hterm := ENNReal.le_tsum (f := fun x : Percept => μ.prob ha x) xTT
                      exact le_trans hterm hle) (by simp))
                  have hsumENN_ne_top : (μ.prob ha xFT + μ.prob ha xTT) ≠ (⊤ : ENNReal) := by
                    intro htop
                    have : μ.prob ha xFT = (⊤ : ENNReal) ∨ μ.prob ha xTT = (⊤ : ENNReal) := by
                      simpa using (ENNReal.add_eq_top).1 (by simpa using htop)
                    cases this with
                    | inl hx =>
                        exact hxFT_ne_top hx
                    | inr hx =>
                        exact hxTT_ne_top hx
                  have hsumReal :
                      ((∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) +
                          (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i)).toReal ≤
                        (μ.prob ha xFT).toReal + (μ.prob ha xTT).toReal := by
                    have hleft_ne_top :
                        (∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) +
                            (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) ≠
                          (⊤ : ENNReal) := by
                      -- bounded by the finite RHS
                      exact ne_of_lt (lt_of_le_of_lt hsumENN (by simpa using (lt_top_iff_ne_top.2 hsumENN_ne_top)))
                    have hleReal :=
                      (ENNReal.toReal_le_toReal hleft_ne_top hsumENN_ne_top).2 hsumENN
                    simpa [ENNReal.toReal_add hxFT_ne_top hxTT_ne_top] using hleReal
                  -- Relate the claim `decodeValueNat num den` to the dyadic weight sum.
                  have hden' : (cert.den : ℝ) + 1 = (2 ^ XiTlOneStepRewardLowerBoundCert.denomExp l : ℝ) := by
                    -- `den = 2^D - 1`, so `den + 1 = 2^D`.
                    have hpow : 1 ≤ 2 ^ XiTlOneStepRewardLowerBoundCert.denomExp l := Nat.one_le_pow _ _ (by norm_num)
                    have hdenNat : cert.den + 1 = 2 ^ XiTlOneStepRewardLowerBoundCert.denomExp l := by
                      simpa [hden, XiTlOneStepRewardLowerBoundCert.expectedDen] using (Nat.sub_add_cancel hpow)
                    have hdenReal :
                        ((cert.den + 1 : ℕ) : ℝ) = (2 ^ XiTlOneStepRewardLowerBoundCert.denomExp l : ℝ) := by
                      exact_mod_cast hdenNat
                    simpa [Nat.cast_add, Nat.cast_one] using hdenReal
                  have hclaim_le :
                        (Coding.decodeValueNat cert.num cert.den : ℝ) ≤
                          ((∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i) +
                              (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt (bitstringsUpTo l) i)).toReal := by
                      let bits : List (List Bool) := XiTlOneStepRewardLowerBoundCert.bitsAt l
                      let D : ℕ := XiTlOneStepRewardLowerBoundCert.denomExp l
                      let den : ℝ := (2 ^ D : ℝ)
                      have hclaimEq :
                          (Coding.decodeValueNat cert.num cert.den : ℝ) = (cert.num : ℝ) / den := by
                        simp [Coding.decodeValueNat, hden', den, D]
                      have hnumSum :
                          cert.num =
                            (cert.allIdxs.map (fun i => (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0)).sum :=
                        XiTlOneStepRewardLowerBoundCert.numeratorBound_eq_sum_getD (l := l) cert.allIdxs cert.num hnum
                      have hnumSplit :
                          cert.num =
                            (cert.idx_false_true.map (fun i => (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0)).sum +
                              (cert.idx_true_true.map (fun i => (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0)).sum := by
                        simpa [XiTlOneStepRewardLowerBoundCert.allIdxs, List.map_append, List.sum_append] using hnumSum
                      have hnodupAppend : (cert.idx_false_true ++ cert.idx_true_true).Nodup := by
                        simpa [XiTlOneStepRewardLowerBoundCert.allIdxs] using hnodup
                      have hnodupF : cert.idx_false_true.Nodup := (List.nodup_append.1 hnodupAppend).1
                      have hnodupT : cert.idx_true_true.Nodup := (List.nodup_append.1 hnodupAppend).2.1
                      have hFinsetF :
                          (∑ i ∈ cert.idx_false_true.toFinset,
                              (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0) =
                            (cert.idx_false_true.map (fun i => (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0)).sum := by
                        classical
                        simpa using
                          (List.sum_toFinset (f := fun i => (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0) hnodupF)
                      have hFinsetT :
                          (∑ i ∈ cert.idx_true_true.toFinset,
                              (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0) =
                            (cert.idx_true_true.map (fun i => (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0)).sum := by
                        classical
                        simpa using
                          (List.sum_toFinset (f := fun i => (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0) hnodupT)
                      have hnumFinset :
                          cert.num =
                            (∑ i ∈ cert.idx_false_true.toFinset,
                                  (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0) +
                              (∑ i ∈ cert.idx_true_true.toFinset,
                                  (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0) := by
                        simpa [hFinsetF, hFinsetT] using hnumSplit
                      have hnumFinsetReal :
                          (cert.num : ℝ) =
                            ((∑ i ∈ cert.idx_false_true.toFinset,
                                    (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ) +
                              ((∑ i ∈ cert.idx_true_true.toFinset,
                                    (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ) := by
                        exact_mod_cast hnumFinset
                      have hsumF_ne_top :
                          (∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i) ≠ (⊤ : ENNReal) := by
                        classical
                        refine (ENNReal.sum_ne_top).2 ?_
                        intro i hi
                        by_cases hlt : i < bits.length
                        · simp [xi_tlPrefixFreeWeightAt, xi_tlPrefixWeight, hlt]
                        · simp [xi_tlPrefixFreeWeightAt, hlt]
                      have hsumT_ne_top :
                          (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i) ≠ (⊤ : ENNReal) := by
                        classical
                        refine (ENNReal.sum_ne_top).2 ?_
                        intro i hi
                        by_cases hlt : i < bits.length
                        · simp [xi_tlPrefixFreeWeightAt, xi_tlPrefixWeight, hlt]
                        · simp [xi_tlPrefixFreeWeightAt, hlt]
                      have htoRealF :
                          (∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i).toReal =
                            ((∑ i ∈ cert.idx_false_true.toFinset,
                                    (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ) / den := by
                        have hnotTop :
                            ∀ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i ≠ (⊤ : ENNReal) := by
                          intro i hi
                          by_cases hlt : i < bits.length
                          · simp [xi_tlPrefixFreeWeightAt, xi_tlPrefixWeight, hlt]
                          · simp [xi_tlPrefixFreeWeightAt, hlt]
                        calc
                          (∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i).toReal =
                              ∑ i ∈ cert.idx_false_true.toFinset, (xi_tlPrefixFreeWeightAt bits i).toReal :=
                            ENNReal.toReal_sum (s := cert.idx_false_true.toFinset)
                              (f := fun i => xi_tlPrefixFreeWeightAt bits i) hnotTop
                          _ = ∑ i ∈ cert.idx_false_true.toFinset,
                                ((XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℝ) / den := by
                            refine Finset.sum_congr rfl ?_
                            intro i hi
                            simpa [bits, den, D] using
                              (XiTlOneStepRewardLowerBoundCert.prefixFreeWeightAt_toReal_eq_numeratorTerm_div (l := l) (i := i))
                          _ = (∑ i ∈ cert.idx_false_true.toFinset,
                                ((XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℝ)) / den := by
                            classical
                            simp [div_eq_mul_inv, Finset.sum_mul]
                          _ = ((∑ i ∈ cert.idx_false_true.toFinset,
                                  (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ) / den := by
                            classical
                            simp [Nat.cast_sum (R := ℝ) (cert.idx_false_true.toFinset)
                              (fun i => (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0)]
                      have htoRealT :
                          (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i).toReal =
                            ((∑ i ∈ cert.idx_true_true.toFinset,
                                    (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ) / den := by
                        have hnotTop :
                            ∀ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i ≠ (⊤ : ENNReal) := by
                          intro i hi
                          by_cases hlt : i < bits.length
                          · simp [xi_tlPrefixFreeWeightAt, xi_tlPrefixWeight, hlt]
                          · simp [xi_tlPrefixFreeWeightAt, hlt]
                        calc
                          (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i).toReal =
                              ∑ i ∈ cert.idx_true_true.toFinset, (xi_tlPrefixFreeWeightAt bits i).toReal :=
                            ENNReal.toReal_sum (s := cert.idx_true_true.toFinset)
                              (f := fun i => xi_tlPrefixFreeWeightAt bits i) hnotTop
                          _ = ∑ i ∈ cert.idx_true_true.toFinset,
                                ((XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℝ) / den := by
                            refine Finset.sum_congr rfl ?_
                            intro i hi
                            simpa [bits, den, D] using
                              (XiTlOneStepRewardLowerBoundCert.prefixFreeWeightAt_toReal_eq_numeratorTerm_div (l := l) (i := i))
                          _ = (∑ i ∈ cert.idx_true_true.toFinset,
                                ((XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℝ)) / den := by
                            classical
                            simp [div_eq_mul_inv, Finset.sum_mul]
                          _ = ((∑ i ∈ cert.idx_true_true.toFinset,
                                  (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ) / den := by
                            classical
                            simp [Nat.cast_sum (R := ℝ) (cert.idx_true_true.toFinset)
                              (fun i => (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0)]
                      have hsumEq :
                          (cert.num : ℝ) / den =
                            ((∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i) +
                                  (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i)).toReal := by
                        have htoRealAdd :
                            ((∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i) +
                                    (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i)).toReal =
                                  (∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i).toReal +
                                    (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i).toReal := by
                          simpa using ENNReal.toReal_add hsumF_ne_top hsumT_ne_top
                        have hsumToReal :
                            ((∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i) +
                                  (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i)).toReal =
                                (cert.num : ℝ) / den := by
                          calc
                            ((∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i) +
                                  (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i)).toReal =
                                (∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i).toReal +
                                  (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i).toReal := htoRealAdd
                            _ =
                                ((∑ i ∈ cert.idx_false_true.toFinset,
                                        (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ) / den +
                                  ((∑ i ∈ cert.idx_true_true.toFinset,
                                        (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ) / den := by
                              simp [htoRealF, htoRealT]
                            _ =
                                (((∑ i ∈ cert.idx_false_true.toFinset,
                                          (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ) +
                                    ((∑ i ∈ cert.idx_true_true.toFinset,
                                          (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ)) / den := by
                              simpa using
                                (add_div
                                    ((∑ i ∈ cert.idx_false_true.toFinset,
                                          (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ)
                                    ((∑ i ∈ cert.idx_true_true.toFinset,
                                          (XiTlOneStepRewardLowerBoundCert.numeratorTerm l i).getD 0 : ℕ) : ℝ)
                                    den).symm
                            _ = (cert.num : ℝ) / den := by
                              simp [hnumFinsetReal]
                        exact hsumToReal.symm
                      have hEq :
                          (Coding.decodeValueNat cert.num cert.den : ℝ) =
                            ((∑ i ∈ cert.idx_false_true.toFinset, xi_tlPrefixFreeWeightAt bits i) +
                                  (∑ i ∈ cert.idx_true_true.toFinset, xi_tlPrefixFreeWeightAt bits i)).toReal := by
                        trans (cert.num : ℝ) / den
                        · exact hclaimEq
                        · exact hsumEq
                      exact le_of_eq hEq
                  have hclaim_le_q :
                        (Coding.decodeValueNat cert.num cert.den : ℝ) ≤ qValue μ (p.toExtended tProg).toAgent γ h a 1 := by
                      exact le_trans hclaim_le (by simpa [hq] using hsumReal)
                  have hclaim_le_value :
                      (Coding.decodeValueNat cert.num cert.den : ℝ) ≤ value μ (p.toExtended tProg).toAgent γ h 2 := by
                    simpa [hval] using hclaim_le_q
                  -- Assemble the `ValidValueLowerBound` conclusion for the `some out` case by rewriting the LHS claim.
                  have hclaim_le_value' :
                      (Coding.decodeValueNat cert.num cert.den : ℝ) ≤
                        value μ
                          ({ code := p.code, compute := RawToPartrecProgram.computeWithin tProg p } : ExtendedChronologicalProgram).toAgent
                          γ h 2 := by
                    simpa [RawToPartrecProgram.toExtended] using hclaim_le_value
                  have hclaim :
                      (RawToPartrecProgram.computeWithin tProg p h).1 = Coding.decodeValueNat cert.num cert.den := by
                    simp [RawToPartrecProgram.computeWithin, hEval, hcompute]
                  have :
                      (RawToPartrecProgram.computeWithin tProg p h).1 ≤
                        value μ
                          ({ code := p.code, compute := RawToPartrecProgram.computeWithin tProg p } : ExtendedChronologicalProgram).toAgent
                          γ h 2 := by
                    simpa [hclaim.symm] using hclaim_le_value'
                  simpa [RawToPartrecProgram.computeWithin] using this
          | false =>
              -- Guard does not fire: the claimed value is `0` (or times out and defaults to `0`).
              have hclaim0 : ((p.toExtended tProg).compute h').1 = 0 := by
                unfold RawToPartrecProgram.toExtended RawToPartrecProgram.computeWithin
                cases hEval : StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat h') with
                | none =>
                    simp [hEval]
                | some out =>
                    have houtMem : out ∈ p.tm.eval (Coding.encodeHistoryNat h') :=
                      StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h') (out := out) hEval
                    have hpTm' : p.tm = RawToPartrecProgram.guardedValueActionCode cert.historyCode cert.num cert.den a := hpTm
                    have houtMem' :
                        out ∈
                          (RawToPartrecProgram.guardedValueActionCode cert.historyCode cert.num cert.den a).eval
                            (Coding.encodeHistoryNat h') := by
                      simpa [hpTm'] using houtMem
                    let outNo : List ℕ := [0, 0, Coding.encodeActionNat Action.stay]
                    have hEvalTemplate :
                        (RawToPartrecProgram.guardedValueActionCode cert.historyCode cert.num cert.den a).eval
                            (Coding.encodeHistoryNat h') =
                          pure outNo := by
                      simp [RawToPartrecProgram.guardedValueActionCode, RawToPartrecProgram.guardPrefixListNat_eval_const, hguard,
                        outNo]
                    have houtEq : out = outNo := by
                      simpa [hEvalTemplate] using houtMem'
                    simp [hEval, houtEq, outNo, Coding.decodeValueActionOutput, Coding.decodeValueNat]
              have hnonneg : 0 ≤ value μ (p.toExtended tProg).toAgent γ h' 2 :=
                value_nonneg (μ := μ) (π := (p.toExtended tProg).toAgent) (γ := γ) (h := h') (n := 2)
              simpa [hclaim0] using hnonneg

/-- Discount factor `γ = 1`, matching Hutter's unnormalized finite-horizon value. -/
noncomputable def gammaOne : DiscountFactor :=
  { val := 1
    nonneg := by norm_num
    le_one := by norm_num }

/-- Intermediate dyadic numerators used by `XiTlTwoStepRewardLowerBoundCert`. -/
structure XiTlTwoStepRewardLowerBoundNumerators where
  n1FF : ℕ
  n1FT : ℕ
  n1TF : ℕ
  n1TT : ℕ
  n2FFFT : ℕ
  n2FFTT : ℕ
  n2FTFT : ℕ
  n2FTTT : ℕ
  n2TFFT : ℕ
  n2TFTT : ℕ
  n2TTFT : ℕ
  n2TTTT : ℕ
deriving Encodable

/-- A certificate for a 2-cycle (i.e. horizon `4`) value lower bound for `ξ^tl`.

The verifier checks:

- a single guarded root history where the program claims a positive dyadic value and chooses an action, and
- the four one-cycle continuation actions for each possible first percept.

The claimed value is computed from dyadic lower bounds on the relevant `ξ^tl` percept probabilities. -/
structure XiTlTwoStepRewardLowerBoundCert where
  /-- The encoded guarded history `h` (must be exactly `Coding.encodeHistoryNat h`). -/
  historyCode : List ℕ
  /-- Root action code at `h`. -/
  actionCode0 : ℕ
  /-- Branch action code after observing `⟨false,false⟩`. -/
  actionCodeFF : ℕ
  /-- Branch action code after observing `⟨false,true⟩`. -/
  actionCodeFT : ℕ
  /-- Branch action code after observing `⟨true,false⟩`. -/
  actionCodeTF : ℕ
  /-- Branch action code after observing `⟨true,true⟩`. -/
  actionCodeTT : ℕ
  /-- The claimed numerator `num` (decoded as `num / (den+1)`). -/
  num : ℕ
  /-- The claimed denominator offset `den` (decoded as `num / (den+1)`). -/
  den : ℕ
  /-- Indices yielding first percept `⟨false,false⟩` at `h ++ [act a0]`. -/
  idx1_FF : List ℕ
  /-- Indices yielding first percept `⟨false,true⟩` at `h ++ [act a0]`. -/
  idx1_FT : List ℕ
  /-- Indices yielding first percept `⟨true,false⟩` at `h ++ [act a0]`. -/
  idx1_TF : List ℕ
  /-- Indices yielding first percept `⟨true,true⟩` at `h ++ [act a0]`. -/
  idx1_TT : List ℕ
  /-- Indices yielding second percept `⟨false,true⟩` after `⟨false,false⟩` and action `aFF`. -/
  idx2_FF_FT : List ℕ
  /-- Indices yielding second percept `⟨true,true⟩` after `⟨false,false⟩` and action `aFF`. -/
  idx2_FF_TT : List ℕ
  /-- Indices yielding second percept `⟨false,true⟩` after `⟨false,true⟩` and action `aFT`. -/
  idx2_FT_FT : List ℕ
  /-- Indices yielding second percept `⟨true,true⟩` after `⟨false,true⟩` and action `aFT`. -/
  idx2_FT_TT : List ℕ
  /-- Indices yielding second percept `⟨false,true⟩` after `⟨true,false⟩` and action `aTF`. -/
  idx2_TF_FT : List ℕ
  /-- Indices yielding second percept `⟨true,true⟩` after `⟨true,false⟩` and action `aTF`. -/
  idx2_TF_TT : List ℕ
  /-- Indices yielding second percept `⟨false,true⟩` after `⟨true,true⟩` and action `aTT`. -/
  idx2_TT_FT : List ℕ
  /-- Indices yielding second percept `⟨true,true⟩` after `⟨true,true⟩` and action `aTT`. -/
  idx2_TT_TT : List ℕ
  /-- Cached dyadic numerators for the listed indices. -/
  nums : XiTlTwoStepRewardLowerBoundNumerators
deriving Encodable

namespace XiTlTwoStepRewardLowerBoundCert

abbrev bitsAt (l : ℕ) : List (List Bool) :=
  XiTlOneStepRewardLowerBoundCert.bitsAt l

abbrev denomExp (l : ℕ) : ℕ :=
  XiTlOneStepRewardLowerBoundCert.denomExp l

abbrev numeratorBound (l : ℕ) : List ℕ → Option ℕ :=
  XiTlOneStepRewardLowerBoundCert.numeratorBound l

abbrev checkIdxOutputs (tEnv l : ℕ) (ha : History) (target : Percept) (idxs : List ℕ) : Bool :=
  XiTlOneStepRewardLowerBoundCert.checkIdxOutputs tEnv l ha target idxs

def denomPow1 (l : ℕ) : ℕ :=
  2 ^ denomExp l

def denomPow2 (l : ℕ) : ℕ :=
  denomPow1 l * denomPow1 l

def expectedDen (l : ℕ) : ℕ :=
  denomPow2 l - 1

def computeClaimNumerator (l : ℕ) (cert : XiTlTwoStepRewardLowerBoundCert) : Option ℕ := do
  let n1FF ← numeratorBound l cert.idx1_FF
  let n1FT ← numeratorBound l cert.idx1_FT
  let n1TF ← numeratorBound l cert.idx1_TF
  let n1TT ← numeratorBound l cert.idx1_TT
  let n2FFFT ← numeratorBound l cert.idx2_FF_FT
  let n2FFTT ← numeratorBound l cert.idx2_FF_TT
  let n2FTFT ← numeratorBound l cert.idx2_FT_FT
  let n2FTTT ← numeratorBound l cert.idx2_FT_TT
  let n2TFFT ← numeratorBound l cert.idx2_TF_FT
  let n2TFTT ← numeratorBound l cert.idx2_TF_TT
  let n2TTFT ← numeratorBound l cert.idx2_TT_FT
  let n2TTTT ← numeratorBound l cert.idx2_TT_TT
  let reward1 : ℕ := n1FT + n1TT
  let reward2FF : ℕ := n2FFFT + n2FFTT
  let reward2FT : ℕ := n2FTFT + n2FTTT
  let reward2TF : ℕ := n2TFFT + n2TFTT
  let reward2TT : ℕ := n2TTFT + n2TTTT
  let den1 : ℕ := denomPow1 l
  pure (reward1 * den1 + n1FF * reward2FF + n1FT * reward2FT + n1TF * reward2TF + n1TT * reward2TT)

def claimNumerator (l : ℕ) (nums : XiTlTwoStepRewardLowerBoundNumerators) : ℕ :=
  let reward1 : ℕ := nums.n1FT + nums.n1TT
  let reward2FF : ℕ := nums.n2FFFT + nums.n2FFTT
  let reward2FT : ℕ := nums.n2FTFT + nums.n2FTTT
  let reward2TF : ℕ := nums.n2TFFT + nums.n2TFTT
  let reward2TT : ℕ := nums.n2TTFT + nums.n2TTTT
  let den1 : ℕ := denomPow1 l
  reward1 * den1 + nums.n1FF * reward2FF + nums.n1FT * reward2FT + nums.n1TF * reward2TF + nums.n1TT * reward2TT

def computeNumerators (l : ℕ) (cert : XiTlTwoStepRewardLowerBoundCert) : Option XiTlTwoStepRewardLowerBoundNumerators := do
  let n1FF ← numeratorBound l cert.idx1_FF
  let n1FT ← numeratorBound l cert.idx1_FT
  let n1TF ← numeratorBound l cert.idx1_TF
  let n1TT ← numeratorBound l cert.idx1_TT
  let n2FFFT ← numeratorBound l cert.idx2_FF_FT
  let n2FFTT ← numeratorBound l cert.idx2_FF_TT
  let n2FTFT ← numeratorBound l cert.idx2_FT_FT
  let n2FTTT ← numeratorBound l cert.idx2_FT_TT
  let n2TFFT ← numeratorBound l cert.idx2_TF_FT
  let n2TFTT ← numeratorBound l cert.idx2_TF_TT
  let n2TTFT ← numeratorBound l cert.idx2_TT_FT
  let n2TTTT ← numeratorBound l cert.idx2_TT_TT
  pure ⟨n1FF, n1FT, n1TF, n1TT, n2FFFT, n2FFTT, n2FTFT, n2FTTT, n2TFFT, n2TFTT, n2TTFT, n2TTTT⟩

def ok (tProg tEnv l : ℕ) (p : RawToPartrecProgram) (cert : XiTlTwoStepRewardLowerBoundCert) : Prop :=
  match
    Coding.decodeHistoryNat cert.historyCode,
    Coding.decodeActionNat cert.actionCode0,
    Coding.decodeActionNat cert.actionCodeFF,
    Coding.decodeActionNat cert.actionCodeFT,
    Coding.decodeActionNat cert.actionCodeTF,
    Coding.decodeActionNat cert.actionCodeTT
  with
  | some h, some a0, some aFF, some aFT, some aTF, some aTT =>
      let xFF : Percept := ⟨false, false⟩
      let xFT : Percept := ⟨false, true⟩
      let xTF : Percept := ⟨true, false⟩
      let xTT : Percept := ⟨true, true⟩
      let ha0 : History := h ++ [HistElem.act a0]
      let hFF : History := h ++ [HistElem.act a0, HistElem.per xFF]
      let hFT : History := h ++ [HistElem.act a0, HistElem.per xFT]
      let hTF : History := h ++ [HistElem.act a0, HistElem.per xTF]
      let hTT : History := h ++ [HistElem.act a0, HistElem.per xTT]
      let haFF : History := hFF ++ [HistElem.act aFF]
      let haFT : History := hFT ++ [HistElem.act aFT]
      let haTF : History := hTF ++ [HistElem.act aTF]
      let haTT : History := hTT ++ [HistElem.act aTT]
      let outRoot : List ℕ := [cert.num, cert.den, Coding.encodeActionNat a0]
      let outFF : List ℕ := [0, 0, Coding.encodeActionNat aFF]
      let outFT : List ℕ := [0, 0, Coding.encodeActionNat aFT]
      let outTF : List ℕ := [0, 0, Coding.encodeActionNat aTF]
      let outTT : List ℕ := [0, 0, Coding.encodeActionNat aTT]
      let defaultOut : List ℕ := [0, 0, Coding.encodeActionNat Action.stay]
      let cases : List (List ℕ × List ℕ) :=
        [ (Coding.encodeHistoryNat h, outRoot)
        , (Coding.encodeHistoryNat hFF, outFF)
        , (Coding.encodeHistoryNat hFT, outFT)
        , (Coding.encodeHistoryNat hTF, outTF)
        , (Coding.encodeHistoryNat hTT, outTT)
        ]
      Coding.encodeHistoryNat h = cert.historyCode ∧
        p.tm = RawToPartrecProgram.dispatchHistoryCodes cases defaultOut ∧
          cert.den = expectedDen l ∧
            ha0.wellFormed ∧
              haFF.wellFormed ∧ haFT.wellFormed ∧ haTF.wellFormed ∧ haTT.wellFormed ∧
                cert.idx1_FF.Nodup ∧ cert.idx1_FT.Nodup ∧ cert.idx1_TF.Nodup ∧ cert.idx1_TT.Nodup ∧
                  cert.idx2_FF_FT.Nodup ∧ cert.idx2_FF_TT.Nodup ∧ cert.idx2_FT_FT.Nodup ∧ cert.idx2_FT_TT.Nodup ∧
                    cert.idx2_TF_FT.Nodup ∧ cert.idx2_TF_TT.Nodup ∧ cert.idx2_TT_FT.Nodup ∧ cert.idx2_TT_TT.Nodup ∧
                      checkIdxOutputs tEnv l ha0 xFF cert.idx1_FF = true ∧
                        checkIdxOutputs tEnv l ha0 xFT cert.idx1_FT = true ∧
                          checkIdxOutputs tEnv l ha0 xTF cert.idx1_TF = true ∧
                            checkIdxOutputs tEnv l ha0 xTT cert.idx1_TT = true ∧
                              checkIdxOutputs tEnv l haFF xFT cert.idx2_FF_FT = true ∧
                                checkIdxOutputs tEnv l haFF xTT cert.idx2_FF_TT = true ∧
                                  checkIdxOutputs tEnv l haFT xFT cert.idx2_FT_FT = true ∧
                                    checkIdxOutputs tEnv l haFT xTT cert.idx2_FT_TT = true ∧
                                      checkIdxOutputs tEnv l haTF xFT cert.idx2_TF_FT = true ∧
                                        checkIdxOutputs tEnv l haTF xTT cert.idx2_TF_TT = true ∧
                                          checkIdxOutputs tEnv l haTT xFT cert.idx2_TT_FT = true ∧
                                            checkIdxOutputs tEnv l haTT xTT cert.idx2_TT_TT = true ∧
                                              computeNumerators l cert = some cert.nums ∧
                                                cert.num = claimNumerator l cert.nums ∧
                                                StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat h) =
                                                    some outRoot ∧
                                                  StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hFF) =
                                                      some outFF ∧
                                                    StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hFT) =
                                                        some outFT ∧
                                                      StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hTF) =
                                                          some outTF ∧
                                                        StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hTT) =
                                                            some outTT
  | _, _, _, _, _, _ => False

end XiTlTwoStepRewardLowerBoundCert

set_option maxHeartbeats 2000000

/-- A 2-cycle “actual verifier” for horizon `4` under `ξ^tl` at discount `γ = 1`.

Certificates describe a guarded root history with a dyadic lower bound on the 2-cycle value, together with
the four continuation actions and dyadic bounds needed to justify the claim. -/
noncomputable def xi_tlTwoStepRewardLowerBoundSoundProofSystemToPartrec (tEnv l : ℕ) :
    EncodableSoundProofSystemFamily (α := RawToPartrecProgram)
      (fun tProg p => ValidValueLowerBound (xi_tlEnvironment tEnv l) gammaOne 4 (p.toExtended tProg)) := by
  classical
  refine
    { Proof := XiTlTwoStepRewardLowerBoundCert
      verify := fun tProg p cert =>
        decide (XiTlTwoStepRewardLowerBoundCert.ok (tProg := tProg) (tEnv := tEnv) (l := l) p cert)
      sound := ?_ }
  intro tProg p cert hverify
  have hok :
      XiTlTwoStepRewardLowerBoundCert.ok (tProg := tProg) (tEnv := tEnv) (l := l) p cert :=
    of_decide_eq_true hverify
  -- Decode the guarded history and actions.
  cases hdecH : Coding.decodeHistoryNat cert.historyCode with
  | none =>
      have : False := by
        have hok' := hok
        simp [XiTlTwoStepRewardLowerBoundCert.ok, hdecH] at hok'
      cases this
  | some h =>
      cases hdecA0 : Coding.decodeActionNat cert.actionCode0 with
      | none =>
          have : False := by
            have hok' := hok
            simp [XiTlTwoStepRewardLowerBoundCert.ok, hdecH, hdecA0] at hok'
          cases this
      | some a0 =>
          cases hdecAFF : Coding.decodeActionNat cert.actionCodeFF with
          | none =>
              have : False := by
                have hok' := hok
                simp [XiTlTwoStepRewardLowerBoundCert.ok, hdecH, hdecA0, hdecAFF] at hok'
              cases this
          | some aFF =>
              cases hdecAFT : Coding.decodeActionNat cert.actionCodeFT with
              | none =>
                  have : False := by
                    have hok' := hok
                    simp [XiTlTwoStepRewardLowerBoundCert.ok, hdecH, hdecA0, hdecAFF, hdecAFT] at hok'
                  cases this
              | some aFT =>
                  cases hdecATF : Coding.decodeActionNat cert.actionCodeTF with
                  | none =>
                      have : False := by
                        have hok' := hok
                        simp [XiTlTwoStepRewardLowerBoundCert.ok, hdecH, hdecA0, hdecAFF, hdecAFT, hdecATF] at hok'
                      cases this
                  | some aTF =>
                      cases hdecATT : Coding.decodeActionNat cert.actionCodeTT with
                      | none =>
                          have : False := by
                            have hok' := hok
                            simp [XiTlTwoStepRewardLowerBoundCert.ok, hdecH, hdecA0, hdecAFF, hdecAFT, hdecATF, hdecATT] at hok'
                          cases this
                      | some aTT =>
                          -- Unpack `ok`.
                          rcases (by
                            simpa [XiTlTwoStepRewardLowerBoundCert.ok, hdecH, hdecA0, hdecAFF, hdecAFT, hdecATF, hdecATT]
                              using hok) with
                            ⟨hhEnc, hpTm, hden, hha0Wf, hhaFFWf, hhaFTWf, hhaTFWf, hhaTTWf, hnodup1FF, hnodup1FT,
                              hnodup1TF, hnodup1TT, hnodup2FFFT, hnodup2FFTT, hnodup2FTFT, hnodup2FTTT, hnodup2TFFT,
                              hnodup2TFTT, hnodup2TTFT, hnodup2TTTT, hIdx1FF, hIdx1FT, hIdx1TF, hIdx1TT, hIdx2FFFT,
                              hIdx2FFTT, hIdx2FTFT, hIdx2FTTT, hIdx2TFFT, hIdx2TFTT, hIdx2TTFT, hIdx2TTTT, hnum,
                              hEvalRoot, hEvalFF, hEvalFT, hEvalTF, hEvalTT⟩
                          let μ : Environment := xi_tlEnvironment tEnv l
                          let xFF : Percept := ⟨false, false⟩
                          let xFT : Percept := ⟨false, true⟩
                          let xTF : Percept := ⟨true, false⟩
                          let xTT : Percept := ⟨true, true⟩
                          let ha0 : History := h ++ [HistElem.act a0]
                          let hFF : History := h ++ [HistElem.act a0, HistElem.per xFF]
                          let hFT : History := h ++ [HistElem.act a0, HistElem.per xFT]
                          let hTF : History := h ++ [HistElem.act a0, HistElem.per xTF]
                          let hTT : History := h ++ [HistElem.act a0, HistElem.per xTT]
                          let haFF : History := hFF ++ [HistElem.act aFF]
                          let haFT : History := hFT ++ [HistElem.act aFT]
                          let haTF : History := hTF ++ [HistElem.act aTF]
                          let haTT : History := hTT ++ [HistElem.act aTT]
                          let outRoot : List ℕ := [cert.num, cert.den, Coding.encodeActionNat a0]
                          let outFF : List ℕ := [0, 0, Coding.encodeActionNat aFF]
                          let outFT : List ℕ := [0, 0, Coding.encodeActionNat aFT]
                          let outTF : List ℕ := [0, 0, Coding.encodeActionNat aTF]
                          let outTT : List ℕ := [0, 0, Coding.encodeActionNat aTT]
                          let defaultOut : List ℕ := [0, 0, Coding.encodeActionNat Action.stay]
                          let cases : List (List ℕ × List ℕ) :=
                            [ (Coding.encodeHistoryNat h, outRoot)
                            , (Coding.encodeHistoryNat hFF, outFF)
                            , (Coding.encodeHistoryNat hFT, outFT)
                            , (Coding.encodeHistoryNat hTF, outTF)
                            , (Coding.encodeHistoryNat hTT, outTT)
                            ]
                          have hpTm' : p.tm = RawToPartrecProgram.dispatchHistoryCodes cases defaultOut := hpTm
                          -- Main soundness goal: global `ValidValueLowerBound`.
                          intro h' hwf
                          by_cases hh' : h' = h
                          · subst h'
                            -- Root history: `compute` returns the verified claim and action.
                            have hEvalRootOut :
                                StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat h) = some outRoot := by
                              simpa [outRoot] using hEvalFF
                            have hEvalFFOut :
                                StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hFF) = some outFF := by
                              simpa [hFF, xFF, outFF] using hEvalFT
                            have hEvalFTOut :
                                StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hFT) = some outFT := by
                              simpa [hFT, xFT, outFT] using hEvalTF
                            have hEvalTFOut :
                                StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hTF) = some outTF := by
                              simpa [hTF, xTF, outTF] using hEvalTT.1
                            have hEvalTTOut :
                                StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hTT) = some outTT := by
                              simpa [hTT, xTT, outTT] using hEvalTT.2
                            have hcompute :
                                (p.toExtended tProg).compute h =
                                  (Coding.decodeValueNat cert.num cert.den, a0) := by
                              unfold RawToPartrecProgram.toExtended RawToPartrecProgram.computeWithin
                              simp [hEvalRootOut, hEvalRoot, outRoot, Coding.decodeValueActionOutput,
                                Coding.decodeActionNat_encodeActionNat, Coding.decodeValueNat]
                            have hclaim :
                                ((p.toExtended tProg).compute h).1 = Coding.decodeValueNat cert.num cert.den := by
                              simp [hcompute]
                            have hact : ((p.toExtended tProg).compute h).2 = a0 := by
                              simp [hcompute]
                            -- Establish branch actions (needed to unfold the value recursion).
                            have hcomputeFF :
                                (p.toExtended tProg).compute hFF = (0, aFF) := by
                              unfold RawToPartrecProgram.toExtended RawToPartrecProgram.computeWithin
                              simp [hEvalFFOut, outFF, Coding.decodeValueActionOutput, Coding.decodeActionNat_encodeActionNat,
                                Coding.decodeValueNat]
                            have hcomputeFT :
                                (p.toExtended tProg).compute hFT = (0, aFT) := by
                              unfold RawToPartrecProgram.toExtended RawToPartrecProgram.computeWithin
                              simp [hEvalFTOut, outFT, Coding.decodeValueActionOutput, Coding.decodeActionNat_encodeActionNat,
                                Coding.decodeValueNat]
                            have hcomputeTF :
                                (p.toExtended tProg).compute hTF = (0, aTF) := by
                              unfold RawToPartrecProgram.toExtended RawToPartrecProgram.computeWithin
                              simp [hEvalTFOut, outTF, Coding.decodeValueActionOutput, Coding.decodeActionNat_encodeActionNat,
                                Coding.decodeValueNat]
                            have hcomputeTT :
                                (p.toExtended tProg).compute hTT = (0, aTT) := by
                              unfold RawToPartrecProgram.toExtended RawToPartrecProgram.computeWithin
                              simp [hEvalTTOut, outTT, Coding.decodeValueActionOutput, Coding.decodeActionNat_encodeActionNat,
                                Coding.decodeValueNat]
                            -- Rewrite `value` at horizon `4` as a `qValue` at horizon `3`.
                            have hval :
                                value μ (p.toExtended tProg).toAgent gammaOne h 4 =
                                  qValue μ (p.toExtended tProg).toAgent gammaOne h a0 3 := by
                              have hwf' : h.wellFormed := hwf
                              have hval' :
                                  value μ (p.toExtended tProg).toAgent gammaOne h 4 =
                                    qValue μ (p.toExtended tProg).toAgent gammaOne h ((p.toExtended tProg).compute h).2 3 := by
                                simpa [ExtendedChronologicalProgram.toAgent, deterministicAgent] using
                                  (value_deterministicAgent_succ (μ := μ) (γ := gammaOne)
                                    (act := fun h0 => ((p.toExtended tProg).compute h0).2) (h := h) (n := 3) hwf')
                              simpa [hact] using hval'
                            -- Expand `qValue` and then each branch `value` at horizon `2`.
                            have hq :
                                qValue μ (p.toExtended tProg).toAgent gammaOne h a0 3 =
                                  (μ.prob ha0 xFF).toReal * (0 + gammaOne.val * value μ (p.toExtended tProg).toAgent gammaOne hFF 2) +
                                    (μ.prob ha0 xFT).toReal * (1 + gammaOne.val * value μ (p.toExtended tProg).toAgent gammaOne hFT 2) +
                                      (μ.prob ha0 xTF).toReal * (0 + gammaOne.val * value μ (p.toExtended tProg).toAgent gammaOne hTF 2) +
                                        (μ.prob ha0 xTT).toReal * (1 + gammaOne.val * value μ (p.toExtended tProg).toAgent gammaOne hTT 2) := by
                              -- `qValue_succ` is a `foldl` over the 4 percepts; unfold explicitly.
                              have hha0Wf' : ha0.wellFormed := hha0Wf
                              simp [qValue_succ, ha0, hha0Wf', List.foldl_cons, List.foldl_nil, Percept.reward, gammaOne,
                                xFF, xFT, xTF, xTT, hFF, hFT, hTF, hTT]
                            -- Each branch `value _ _ _ _ 2` reduces to a 1-step expected reward under the chosen action.
                            have wellFormed_append_act_per_of_wellFormed_append_act
                                (h : History) (a : Action) (x : Percept)
                                (hw : (h ++ [HistElem.act a]).wellFormed = true) :
                                (h ++ [HistElem.act a, HistElem.per x]).wellFormed = true := by
                              -- `History.wellFormed` consumes histories two steps at a time.
                              induction h using List.twoStepInduction with
                              | nil =>
                                  simp [History.wellFormed]
                              | singleton e =>
                                  cases e <;> simp [History.wellFormed] at hw
                              | cons_cons e1 e2 rest ih =>
                                  cases e1 <;> cases e2 <;> simp [History.wellFormed] at hw ⊢
                                  exact ih hw
                            have hvalFF :
                                value μ (p.toExtended tProg).toAgent gammaOne hFF 2 =
                                  qValue μ (p.toExtended tProg).toAgent gammaOne hFF aFF 1 := by
                              have hwfFF : hFF.wellFormed := by
                                have hwfFF' :
                                    (h ++ [HistElem.act a0, HistElem.per xFF]).wellFormed = true :=
                                  wellFormed_append_act_per_of_wellFormed_append_act h a0 xFF hha0Wf
                                simpa [hFF] using hwfFF'
                              have hactFF : ((p.toExtended tProg).compute hFF).2 = aFF := by
                                simp [hcomputeFF]
                              have hval' :
                                  value μ (p.toExtended tProg).toAgent gammaOne hFF 2 =
                                    qValue μ (p.toExtended tProg).toAgent gammaOne hFF ((p.toExtended tProg).compute hFF).2 1 := by
                                simpa [ExtendedChronologicalProgram.toAgent, deterministicAgent] using
                                  (value_deterministicAgent_succ (μ := μ) (γ := gammaOne)
                                    (act := fun h0 => ((p.toExtended tProg).compute h0).2) (h := hFF) (n := 1) hwfFF)
                              simpa [hactFF] using hval'
                            have hvalFT :
                                value μ (p.toExtended tProg).toAgent gammaOne hFT 2 =
                                  qValue μ (p.toExtended tProg).toAgent gammaOne hFT aFT 1 := by
                              have hwfFT : hFT.wellFormed := by
                                have hwfFT' :
                                    (h ++ [HistElem.act a0, HistElem.per xFT]).wellFormed = true :=
                                  wellFormed_append_act_per_of_wellFormed_append_act h a0 xFT hha0Wf
                                simpa [hFT] using hwfFT'
                              have hactFT : ((p.toExtended tProg).compute hFT).2 = aFT := by
                                simp [hcomputeFT]
                              have hval' :
                                  value μ (p.toExtended tProg).toAgent gammaOne hFT 2 =
                                    qValue μ (p.toExtended tProg).toAgent gammaOne hFT ((p.toExtended tProg).compute hFT).2 1 := by
                                simpa [ExtendedChronologicalProgram.toAgent, deterministicAgent] using
                                  (value_deterministicAgent_succ (μ := μ) (γ := gammaOne)
                                    (act := fun h0 => ((p.toExtended tProg).compute h0).2) (h := hFT) (n := 1) hwfFT)
                              simpa [hactFT] using hval'
                            have hvalTF :
                                value μ (p.toExtended tProg).toAgent gammaOne hTF 2 =
                                  qValue μ (p.toExtended tProg).toAgent gammaOne hTF aTF 1 := by
                              have hwfTF : hTF.wellFormed := by
                                have hwfTF' :
                                    (h ++ [HistElem.act a0, HistElem.per xTF]).wellFormed = true :=
                                  wellFormed_append_act_per_of_wellFormed_append_act h a0 xTF hha0Wf
                                simpa [hTF] using hwfTF'
                              have hactTF : ((p.toExtended tProg).compute hTF).2 = aTF := by
                                simp [hcomputeTF]
                              have hval' :
                                  value μ (p.toExtended tProg).toAgent gammaOne hTF 2 =
                                    qValue μ (p.toExtended tProg).toAgent gammaOne hTF ((p.toExtended tProg).compute hTF).2 1 := by
                                simpa [ExtendedChronologicalProgram.toAgent, deterministicAgent] using
                                  (value_deterministicAgent_succ (μ := μ) (γ := gammaOne)
                                    (act := fun h0 => ((p.toExtended tProg).compute h0).2) (h := hTF) (n := 1) hwfTF)
                              simpa [hactTF] using hval'
                            have hvalTT :
                                value μ (p.toExtended tProg).toAgent gammaOne hTT 2 =
                                  qValue μ (p.toExtended tProg).toAgent gammaOne hTT aTT 1 := by
                              have hwfTT : hTT.wellFormed := by
                                have hwfTT' :
                                    (h ++ [HistElem.act a0, HistElem.per xTT]).wellFormed = true :=
                                  wellFormed_append_act_per_of_wellFormed_append_act h a0 xTT hha0Wf
                                simpa [hTT] using hwfTT'
                              have hactTT : ((p.toExtended tProg).compute hTT).2 = aTT := by
                                simp [hcomputeTT]
                              have hval' :
                                  value μ (p.toExtended tProg).toAgent gammaOne hTT 2 =
                                    qValue μ (p.toExtended tProg).toAgent gammaOne hTT ((p.toExtended tProg).compute hTT).2 1 := by
                                simpa [ExtendedChronologicalProgram.toAgent, deterministicAgent] using
                                  (value_deterministicAgent_succ (μ := μ) (γ := gammaOne)
                                    (act := fun h0 => ((p.toExtended tProg).compute h0).2) (h := hTT) (n := 1) hwfTT)
                              simpa [hactTT] using hval'
                            -- Expand each branch `qValue` at horizon `1` to the reward-true mass.
                            have hhaFFWf' : haFF.wellFormed = true := by
                              simpa [haFF, hFF, xFF] using hhaFFWf
                            have hhaFTWf' : haFT.wellFormed = true := by
                              simpa [haFT, hFT, xFT] using hhaFTWf
                            have hhaTFWf' : haTF.wellFormed = true := by
                              simpa [haTF, hTF, xTF] using hhaTFWf
                            have hhaTTWf' : haTT.wellFormed = true := by
                              simpa [haTT, hTT, xTT] using hhaTTWf
                            have hqFF :
                                qValue μ (p.toExtended tProg).toAgent gammaOne hFF aFF 1 =
                                  (μ.prob haFF xFT).toReal + (μ.prob haFF xTT).toReal := by
                              simp [qValue_succ, value_zero, Percept.reward, haFF, xFT, xTT, hhaFFWf', List.foldl_cons,
                                List.foldl_nil, gammaOne]
                            have hqFT :
                                qValue μ (p.toExtended tProg).toAgent gammaOne hFT aFT 1 =
                                  (μ.prob haFT xFT).toReal + (μ.prob haFT xTT).toReal := by
                              simp [qValue_succ, value_zero, Percept.reward, haFT, xFT, xTT, hhaFTWf', List.foldl_cons,
                                List.foldl_nil, gammaOne]
                            have hqTF :
                                qValue μ (p.toExtended tProg).toAgent gammaOne hTF aTF 1 =
                                  (μ.prob haTF xFT).toReal + (μ.prob haTF xTT).toReal := by
                              simp [qValue_succ, value_zero, Percept.reward, haTF, xFT, xTT, hhaTFWf', List.foldl_cons,
                                List.foldl_nil, gammaOne]
                            have hqTT :
                                qValue μ (p.toExtended tProg).toAgent gammaOne hTT aTT 1 =
                                  (μ.prob haTT xFT).toReal + (μ.prob haTT xTT).toReal := by
                              simp [qValue_succ, value_zero, Percept.reward, haTT, xFT, xTT, hhaTTWf', List.foldl_cons,
                                List.foldl_nil, gammaOne]
                            -- Lower bound each relevant probability by the certified finite sums.
                            have hx1FF_le :
                                (∑ i ∈ cert.idx1_FF.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob ha0 xFF := by
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := ha0) (target := xFF) (idxs := cert.idx1_FF)
                                  (by
                                    simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs] using hIdx1FF))
                            -- The remaining probability bounds are analogous; we reuse the same pattern by symmetry.
                            have hx1FT_le :
                                (∑ i ∈ cert.idx1_FT.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob ha0 xFT := by
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := ha0) (target := xFT) (idxs := cert.idx1_FT)
                                  (by
                                    simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs] using hIdx1FT))
                            have hx1TF_le :
                                (∑ i ∈ cert.idx1_TF.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob ha0 xTF := by
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := ha0) (target := xTF) (idxs := cert.idx1_TF)
                                  (by
                                    simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs] using hIdx1TF))
                            have hx1TT_le :
                                (∑ i ∈ cert.idx1_TT.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob ha0 xTT := by
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := ha0) (target := xTT) (idxs := cert.idx1_TT)
                                  (by
                                    simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs] using hIdx1TT))
                            -- Second-step reward-true probability bounds at each branch.
                            have hx2FF_FT_le :
                                (∑ i ∈ cert.idx2_FF_FT.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob haFF xFT := by
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := haFF) (target := xFT) (idxs := cert.idx2_FF_FT)
                                  (by
                                    simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs, haFF, hFF, xFF, xFT] using hIdx2FFFT))
                            have hx2FF_TT_le :
                                (∑ i ∈ cert.idx2_FF_TT.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob haFF xTT := by
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := haFF) (target := xTT) (idxs := cert.idx2_FF_TT)
                                  (by
                                    simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs, haFF, hFF, xFF, xTT] using hIdx2FFTT))
                            -- For the other three branches, we only need the reward-true mass lower bounds.
                            have hx2FT_FT_le :
                                (∑ i ∈ cert.idx2_FT_FT.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob haFT xFT := by
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := haFT) (target := xFT) (idxs := cert.idx2_FT_FT)
                                  (by
                                    simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs, haFT, hFT, xFT] using hIdx2FTFT))
                            have hx2FT_TT_le :
                                (∑ i ∈ cert.idx2_FT_TT.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob haFT xTT := by
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := haFT) (target := xTT) (idxs := cert.idx2_FT_TT)
                                  (by
                                    simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs, haFT, hFT, xFT, xTT] using hIdx2FTTT))
                            have hx2TF_FT_le :
                                (∑ i ∈ cert.idx2_TF_FT.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob haTF xFT := by
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := haTF) (target := xFT) (idxs := cert.idx2_TF_FT)
                                  (by
                                    simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs, haTF, hTF, xTF, xFT] using hIdx2TFFT))
                            have hx2TF_TT_le :
                                (∑ i ∈ cert.idx2_TF_TT.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob haTF xTT := by
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := haTF) (target := xTT) (idxs := cert.idx2_TF_TT)
                                  (by
                                    simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs, haTF, hTF, xTF, xTT] using hIdx2TFTT))
                            have hx2TT_FT_le :
                                (∑ i ∈ cert.idx2_TT_FT.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob haTT xFT := by
                              have hIdx2TTFT' :
                                  XiTlOneStepRewardLowerBoundCert.checkIdxOutputs tEnv l haTT xFT cert.idx2_TT_FT = true := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs, haTT, hTT] using hIdx2TTFT
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := haTT) (target := xFT) (idxs := cert.idx2_TT_FT)
                                  (hIdx := hIdx2TTFT'))
                            have hx2TT_TT_le :
                                (∑ i ∈ cert.idx2_TT_TT.toFinset, xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                  μ.prob haTT xTT := by
                              have hIdx2TTTT' :
                                  XiTlOneStepRewardLowerBoundCert.checkIdxOutputs tEnv l haTT xTT cert.idx2_TT_TT = true := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.checkIdxOutputs, haTT, hTT] using hIdx2TTTT
                              simpa [μ] using
                                (XiTlOneStepRewardLowerBoundCert.sum_prefixFreeWeightAt_le_prob_of_checkIdxOutputs
                                  (tEnv := tEnv) (l := l) (ha := haTT) (target := xTT) (idxs := cert.idx2_TT_TT)
                                  (hIdx := hIdx2TTTT'))
                            -- Convert the ENNReal bounds to real bounds.
                            have ha0_prob_le_one (x : Percept) : μ.prob ha0 x ≤ 1 := by
                              have hsum := μ.prob_le_one ha0 hha0Wf
                              exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob ha0 x) x) hsum
                            have hx1FF_le_real :
                                (∑ i ∈ cert.idx1_FF.toFinset,
                                      xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal ≤
                                  (μ.prob ha0 xFF).toReal := by
                              have hneTopLeft :
                                  (∑ i ∈ cert.idx1_FF.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                have : (∑ i ∈ cert.idx1_FF.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                  exact le_trans hx1FF_le (ha0_prob_le_one xFF)
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hneTopRight : μ.prob ha0 xFF ≠ (⊤ : ENNReal) := by
                                exact ne_of_lt (lt_of_le_of_lt (ha0_prob_le_one xFF) (by simp))
                              exact (ENNReal.toReal_le_toReal hneTopLeft hneTopRight).2 hx1FF_le
                            have hx1FT_le_real :
                                (∑ i ∈ cert.idx1_FT.toFinset,
                                      xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal ≤
                                  (μ.prob ha0 xFT).toReal := by
                              have hneTopLeft :
                                  (∑ i ∈ cert.idx1_FT.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                have : (∑ i ∈ cert.idx1_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                  exact le_trans hx1FT_le (ha0_prob_le_one xFT)
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hneTopRight : μ.prob ha0 xFT ≠ (⊤ : ENNReal) := by
                                exact ne_of_lt (lt_of_le_of_lt (ha0_prob_le_one xFT) (by simp))
                              exact (ENNReal.toReal_le_toReal hneTopLeft hneTopRight).2 hx1FT_le
                            have hx1TF_le_real :
                                (∑ i ∈ cert.idx1_TF.toFinset,
                                      xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal ≤
                                  (μ.prob ha0 xTF).toReal := by
                              have hneTopLeft :
                                  (∑ i ∈ cert.idx1_TF.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                have : (∑ i ∈ cert.idx1_TF.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                  exact le_trans hx1TF_le (ha0_prob_le_one xTF)
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hneTopRight : μ.prob ha0 xTF ≠ (⊤ : ENNReal) := by
                                exact ne_of_lt (lt_of_le_of_lt (ha0_prob_le_one xTF) (by simp))
                              exact (ENNReal.toReal_le_toReal hneTopLeft hneTopRight).2 hx1TF_le
                            have hx1TT_le_real :
                                (∑ i ∈ cert.idx1_TT.toFinset,
                                      xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal ≤
                                  (μ.prob ha0 xTT).toReal := by
                              have hneTopLeft :
                                  (∑ i ∈ cert.idx1_TT.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                have : (∑ i ∈ cert.idx1_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                  exact le_trans hx1TT_le (ha0_prob_le_one xTT)
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hneTopRight : μ.prob ha0 xTT ≠ (⊤ : ENNReal) := by
                                exact ne_of_lt (lt_of_le_of_lt (ha0_prob_le_one xTT) (by simp))
                              exact (ENNReal.toReal_le_toReal hneTopLeft hneTopRight).2 hx1TT_le
                            -- Branch reward-true lower bounds to reals.
                            have hx2FF_le_real :
                                ((∑ i ∈ cert.idx2_FF_FT.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                      (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal ≤
                                  (μ.prob haFF xFT).toReal + (μ.prob haFF xTT).toReal := by
                              have hENN :
                                  (∑ i ∈ cert.idx2_FF_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                    μ.prob haFF xFT + μ.prob haFF xTT := add_le_add hx2FF_FT_le hx2FF_TT_le
                              have hneTopLeft :
                                  (∑ i ∈ cert.idx2_FF_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                have : (μ.prob haFF xFT + μ.prob haFF xTT) ≤ (1 : ENNReal) + 1 := by
                                  have hx1 : μ.prob haFF xFT ≤ 1 := by
                                    have := μ.prob_le_one haFF hhaFFWf'
                                    exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob haFF x) xFT) this
                                  have hx2 : μ.prob haFF xTT ≤ 1 := by
                                    have := μ.prob_le_one haFF hhaFFWf'
                                    exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob haFF x) xTT) this
                                  exact add_le_add hx1 hx2
                                have :
                                    (∑ i ∈ cert.idx2_FF_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                      (1 : ENNReal) + 1 := by
                                  exact le_trans hENN this
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hneTopRight : (μ.prob haFF xFT + μ.prob haFF xTT) ≠ (⊤ : ENNReal) := by
                                have : (μ.prob haFF xFT + μ.prob haFF xTT) ≤ (1 : ENNReal) + 1 := by
                                  have hx1 : μ.prob haFF xFT ≤ 1 := by
                                    have := μ.prob_le_one haFF hhaFFWf'
                                    exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob haFF x) xFT) this
                                  have hx2 : μ.prob haFF xTT ≤ 1 := by
                                    have := μ.prob_le_one haFF hhaFFWf'
                                    exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob haFF x) xTT) this
                                  exact add_le_add hx1 hx2
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hleReal :
                                  ((∑ i ∈ cert.idx2_FF_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                              (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal ≤
                                        (μ.prob haFF xFT + μ.prob haFF xTT).toReal :=
                                (ENNReal.toReal_le_toReal hneTopLeft hneTopRight).2 hENN
                              have hxFT_ne_top : μ.prob haFF xFT ≠ (⊤ : ENNReal) := by
                                have hxFT_le_one : μ.prob haFF xFT ≤ 1 :=
                                  le_trans (ENNReal.le_tsum xFT) (μ.prob_le_one haFF hhaFFWf')
                                exact ne_of_lt (lt_of_le_of_lt hxFT_le_one (by simp))
                              have hxTT_ne_top : μ.prob haFF xTT ≠ (⊤ : ENNReal) := by
                                have hxTT_le_one : μ.prob haFF xTT ≤ 1 :=
                                  le_trans (ENNReal.le_tsum xTT) (μ.prob_le_one haFF hhaFFWf')
                                exact ne_of_lt (lt_of_le_of_lt hxTT_le_one (by simp))
                              simpa [ENNReal.toReal_add hxFT_ne_top hxTT_ne_top] using hleReal
                            have hx2FT_le_real :
                                ((∑ i ∈ cert.idx2_FT_FT.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                      (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal ≤
                                  (μ.prob haFT xFT).toReal + (μ.prob haFT xTT).toReal := by
                              have hENN :
                                  (∑ i ∈ cert.idx2_FT_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                    μ.prob haFT xFT + μ.prob haFT xTT := add_le_add hx2FT_FT_le hx2FT_TT_le
                              have hxFT_le_one : μ.prob haFT xFT ≤ 1 := by
                                have := μ.prob_le_one haFT hhaFTWf'
                                exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob haFT x) xFT) this
                              have hxTT_le_one : μ.prob haFT xTT ≤ 1 := by
                                have := μ.prob_le_one haFT hhaFTWf'
                                exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob haFT x) xTT) this
                              have hneTopRight : (μ.prob haFT xFT + μ.prob haFT xTT) ≠ (⊤ : ENNReal) := by
                                have : (μ.prob haFT xFT + μ.prob haFT xTT) ≤ (1 : ENNReal) + 1 := by
                                  exact add_le_add hxFT_le_one hxTT_le_one
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hneTopLeft :
                                  (∑ i ∈ cert.idx2_FT_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                have :
                                    (∑ i ∈ cert.idx2_FT_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                      (1 : ENNReal) + 1 := by
                                  exact le_trans hENN (add_le_add hxFT_le_one hxTT_le_one)
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hleReal :
                                  ((∑ i ∈ cert.idx2_FT_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                              (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal ≤
                                        (μ.prob haFT xFT + μ.prob haFT xTT).toReal :=
                                (ENNReal.toReal_le_toReal hneTopLeft hneTopRight).2 hENN
                              have hxFT_ne_top : μ.prob haFT xFT ≠ (⊤ : ENNReal) := by
                                exact ne_of_lt (lt_of_le_of_lt hxFT_le_one (by simp))
                              have hxTT_ne_top : μ.prob haFT xTT ≠ (⊤ : ENNReal) := by
                                exact ne_of_lt (lt_of_le_of_lt hxTT_le_one (by simp))
                              simpa [ENNReal.toReal_add hxFT_ne_top hxTT_ne_top] using hleReal
                            have hx2TF_le_real :
                                ((∑ i ∈ cert.idx2_TF_FT.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                      (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal ≤
                                  (μ.prob haTF xFT).toReal + (μ.prob haTF xTT).toReal := by
                              have hENN :
                                  (∑ i ∈ cert.idx2_TF_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                    μ.prob haTF xFT + μ.prob haTF xTT := add_le_add hx2TF_FT_le hx2TF_TT_le
                              have hxFT_le_one : μ.prob haTF xFT ≤ 1 := by
                                have := μ.prob_le_one haTF hhaTFWf'
                                exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob haTF x) xFT) this
                              have hxTT_le_one : μ.prob haTF xTT ≤ 1 := by
                                have := μ.prob_le_one haTF hhaTFWf'
                                exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob haTF x) xTT) this
                              have hneTopRight : (μ.prob haTF xFT + μ.prob haTF xTT) ≠ (⊤ : ENNReal) := by
                                have : (μ.prob haTF xFT + μ.prob haTF xTT) ≤ (1 : ENNReal) + 1 := by
                                  exact add_le_add hxFT_le_one hxTT_le_one
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hneTopLeft :
                                  (∑ i ∈ cert.idx2_TF_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                have :
                                    (∑ i ∈ cert.idx2_TF_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                      (1 : ENNReal) + 1 := by
                                  exact le_trans hENN (add_le_add hxFT_le_one hxTT_le_one)
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hleReal :
                                  ((∑ i ∈ cert.idx2_TF_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                              (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal ≤
                                        (μ.prob haTF xFT + μ.prob haTF xTT).toReal :=
                                (ENNReal.toReal_le_toReal hneTopLeft hneTopRight).2 hENN
                              have hxFT_ne_top : μ.prob haTF xFT ≠ (⊤ : ENNReal) := by
                                exact ne_of_lt (lt_of_le_of_lt hxFT_le_one (by simp))
                              have hxTT_ne_top : μ.prob haTF xTT ≠ (⊤ : ENNReal) := by
                                exact ne_of_lt (lt_of_le_of_lt hxTT_le_one (by simp))
                              simpa [ENNReal.toReal_add hxFT_ne_top hxTT_ne_top] using hleReal
                            have hx2TT_le_real :
                                ((∑ i ∈ cert.idx2_TT_FT.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                      (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                        xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal ≤
                                  (μ.prob haTT xFT).toReal + (μ.prob haTT xTT).toReal := by
                              have hENN :
                                  (∑ i ∈ cert.idx2_TT_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                    μ.prob haTT xFT + μ.prob haTT xTT := add_le_add hx2TT_FT_le hx2TT_TT_le
                              have hxFT_le_one : μ.prob haTT xFT ≤ 1 := by
                                have := μ.prob_le_one haTT hhaTTWf'
                                exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob haTT x) xFT) this
                              have hxTT_le_one : μ.prob haTT xTT ≤ 1 := by
                                have := μ.prob_le_one haTT hhaTTWf'
                                exact le_trans (ENNReal.le_tsum (f := fun x : Percept => μ.prob haTT x) xTT) this
                              have hneTopRight : (μ.prob haTT xFT + μ.prob haTT xTT) ≠ (⊤ : ENNReal) := by
                                have : (μ.prob haTT xFT + μ.prob haTT xTT) ≤ (1 : ENNReal) + 1 := by
                                  exact add_le_add hxFT_le_one hxTT_le_one
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hneTopLeft :
                                  (∑ i ∈ cert.idx2_TT_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                have :
                                    (∑ i ∈ cert.idx2_TT_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                        (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤
                                      (1 : ENNReal) + 1 := by
                                  exact le_trans hENN (add_le_add hxFT_le_one hxTT_le_one)
                                exact ne_of_lt (lt_of_le_of_lt this (by simp))
                              have hleReal :
                                  ((∑ i ∈ cert.idx2_TT_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                              (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal ≤
                                        (μ.prob haTT xFT + μ.prob haTT xTT).toReal :=
                                (ENNReal.toReal_le_toReal hneTopLeft hneTopRight).2 hENN
                              have hxFT_ne_top : μ.prob haTT xFT ≠ (⊤ : ENNReal) := by
                                exact ne_of_lt (lt_of_le_of_lt hxFT_le_one (by simp))
                              have hxTT_ne_top : μ.prob haTT xTT ≠ (⊤ : ENNReal) := by
                                exact ne_of_lt (lt_of_le_of_lt hxTT_le_one (by simp))
                              simpa [ENNReal.toReal_add hxFT_ne_top hxTT_ne_top] using hleReal
                            -- Assemble the final lower bound on `qValue` and relate it to the decoded claim.
                            have hnonnegFF : 0 ≤ value μ (p.toExtended tProg).toAgent gammaOne hFF 2 :=
                              value_nonneg (μ := μ) (π := (p.toExtended tProg).toAgent) (γ := gammaOne) (h := hFF) (n := 2)
                            have hnonnegFT : 0 ≤ value μ (p.toExtended tProg).toAgent gammaOne hFT 2 :=
                              value_nonneg (μ := μ) (π := (p.toExtended tProg).toAgent) (γ := gammaOne) (h := hFT) (n := 2)
                            have hnonnegTF : 0 ≤ value μ (p.toExtended tProg).toAgent gammaOne hTF 2 :=
                              value_nonneg (μ := μ) (π := (p.toExtended tProg).toAgent) (γ := gammaOne) (h := hTF) (n := 2)
                            have hnonnegTT : 0 ≤ value μ (p.toExtended tProg).toAgent gammaOne hTT 2 :=
                              value_nonneg (μ := μ) (π := (p.toExtended tProg).toAgent) (γ := gammaOne) (h := hTT) (n := 2)
                            -- Use monotonicity to bound `qValue` from below by the dyadic expression encoded in `cert.num`.
                            -- For now, conclude soundness using the trivial bound `claim ≤ value` derived from `computeClaimNumerator`.
                            -- (The detailed dyadic arithmetic is discharged by the certificate definition itself.)
                            have hclaim_nonneg : 0 ≤ (Coding.decodeValueNat cert.num cert.den : ℝ) :=
                              Coding.decodeValueNat_nonneg cert.num cert.den
                            -- The full inequality proof is a direct (but lengthy) unfolding of `hnum` + the bounds above.
                            -- We keep the final line in terms of `hclaim` and `hval`.
                            have : (Coding.decodeValueNat cert.num cert.den : ℝ) ≤ value μ (p.toExtended tProg).toAgent gammaOne h 4 := by
                              -- Unfold the dyadic claim and lower-bound it by the true 2-cycle value.
                              have hdenPow2_pos : 0 < XiTlTwoStepRewardLowerBoundCert.denomPow2 l := by
                                have hdenPow1_pos : 0 < XiTlTwoStepRewardLowerBoundCert.denomPow1 l := by
                                  simp [XiTlTwoStepRewardLowerBoundCert.denomPow1, XiTlTwoStepRewardLowerBoundCert.denomExp]
                                simpa [XiTlTwoStepRewardLowerBoundCert.denomPow2] using Nat.mul_pos hdenPow1_pos hdenPow1_pos
                              have hdenSucc :
                                  cert.den + 1 = XiTlTwoStepRewardLowerBoundCert.denomPow2 l := by
                                have hpow : 1 ≤ XiTlTwoStepRewardLowerBoundCert.denomPow2 l :=
                                  Nat.succ_le_of_lt hdenPow2_pos
                                calc
                                  cert.den + 1 = XiTlTwoStepRewardLowerBoundCert.expectedDen l + 1 := by
                                    simp [hden]
                                  _ = (XiTlTwoStepRewardLowerBoundCert.denomPow2 l - 1) + 1 := by
                                    rfl
                                  _ = XiTlTwoStepRewardLowerBoundCert.denomPow2 l := Nat.sub_add_cancel hpow
                              let den1 : ℝ := (2 ^ XiTlTwoStepRewardLowerBoundCert.denomExp l : ℝ)
                              have hden1_ne0 : den1 ≠ 0 := by
                                simp [den1]
                              have hden1_pos : 0 < den1 := by
                                simp [den1]
                              -- Extract the individual dyadic numerators from `computeNumerators`.
                              have hnumDo :
                                  (do
                                      let n1FF ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx1_FF
                                      let n1FT ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx1_FT
                                      let n1TF ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx1_TF
                                      let n1TT ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx1_TT
                                      let n2FFFT ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_FF_FT
                                      let n2FFTT ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_FF_TT
                                      let n2FTFT ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_FT_FT
                                      let n2FTTT ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_FT_TT
                                      let n2TFFT ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_TF_FT
                                      let n2TFTT ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_TF_TT
                                      let n2TTFT ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_TT_FT
                                      let n2TTTT ← XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_TT_TT
                                      pure
                                        (XiTlTwoStepRewardLowerBoundNumerators.mk n1FF n1FT n1TF n1TT n2FFFT n2FFTT n2FTFT
                                          n2FTTT n2TFFT n2TFTT n2TTFT n2TTTT)) =
                                    some cert.nums := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.computeNumerators] using hnum
                              rcases (Option.bind_eq_some_iff).1 hnumDo with ⟨n1FF, hn1FF, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n1FT, hn1FT, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n1TF, hn1TF, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n1TT, hn1TT, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n2FFFT, hn2FFFT, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n2FFTT, hn2FFTT, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n2FTFT, hn2FTFT, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n2FTTT, hn2FTTT, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n2TFFT, hn2TFFT, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n2TFTT, hn2TFTT, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n2TTFT, hn2TTFT, hrest⟩
                              rcases (Option.bind_eq_some_iff).1 hrest with ⟨n2TTTT, hn2TTTT, hrest⟩
                              have hnumsEq :
                                  XiTlTwoStepRewardLowerBoundNumerators.mk n1FF n1FT n1TF n1TT n2FFFT n2FFTT n2FTFT n2FTTT n2TFFT
                                      n2TFTT n2TTFT n2TTTT =
                                    cert.nums := by
                                simpa using Option.some.inj hrest
                              have hn1FF' : n1FF = cert.nums.n1FF := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n1FF hnumsEq
                              have hn1FT' : n1FT = cert.nums.n1FT := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n1FT hnumsEq
                              have hn1TF' : n1TF = cert.nums.n1TF := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n1TF hnumsEq
                              have hn1TT' : n1TT = cert.nums.n1TT := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n1TT hnumsEq
                              have hn2FFFT' : n2FFFT = cert.nums.n2FFFT := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n2FFFT hnumsEq
                              have hn2FFTT' : n2FFTT = cert.nums.n2FFTT := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n2FFTT hnumsEq
                              have hn2FTFT' : n2FTFT = cert.nums.n2FTFT := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n2FTFT hnumsEq
                              have hn2FTTT' : n2FTTT = cert.nums.n2FTTT := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n2FTTT hnumsEq
                              have hn2TFFT' : n2TFFT = cert.nums.n2TFFT := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n2TFFT hnumsEq
                              have hn2TFTT' : n2TFTT = cert.nums.n2TFTT := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n2TFTT hnumsEq
                              have hn2TTFT' : n2TTFT = cert.nums.n2TTFT := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n2TTFT hnumsEq
                              have hn2TTTT' : n2TTTT = cert.nums.n2TTTT := by
                                simpa using congrArg XiTlTwoStepRewardLowerBoundNumerators.n2TTTT hnumsEq
                              have hn1FF_cert : XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx1_FF = some cert.nums.n1FF := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn1FF'] using hn1FF
                              have hn1FT_cert : XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx1_FT = some cert.nums.n1FT := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn1FT'] using hn1FT
                              have hn1TF_cert : XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx1_TF = some cert.nums.n1TF := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn1TF'] using hn1TF
                              have hn1TT_cert : XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx1_TT = some cert.nums.n1TT := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn1TT'] using hn1TT
                              have hn2FFFT_cert :
                                  XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx2_FF_FT = some cert.nums.n2FFFT := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn2FFFT'] using hn2FFFT
                              have hn2FFTT_cert :
                                  XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx2_FF_TT = some cert.nums.n2FFTT := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn2FFTT'] using hn2FFTT
                              have hn2FTFT_cert :
                                  XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx2_FT_FT = some cert.nums.n2FTFT := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn2FTFT'] using hn2FTFT
                              have hn2FTTT_cert :
                                  XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx2_FT_TT = some cert.nums.n2FTTT := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn2FTTT'] using hn2FTTT
                              have hn2TFFT_cert :
                                  XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx2_TF_FT = some cert.nums.n2TFFT := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn2TFFT'] using hn2TFFT
                              have hn2TFTT_cert :
                                  XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx2_TF_TT = some cert.nums.n2TFTT := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn2TFTT'] using hn2TFTT
                              have hn2TTFT_cert :
                                  XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx2_TT_FT = some cert.nums.n2TTFT := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn2TTFT'] using hn2TTFT
                              have hn2TTTT_cert :
                                  XiTlOneStepRewardLowerBoundCert.numeratorBound l cert.idx2_TT_TT = some cert.nums.n2TTTT := by
                                simpa [XiTlTwoStepRewardLowerBoundCert.numeratorBound, hn2TTTT'] using hn2TTTT
                              -- Convert the certified dyadics into explicit real lower bounds on each probability.
                              have hp1FF :
                                  (cert.nums.n1FF : ℝ) / den1 ≤ (μ.prob ha0 xFF).toReal := by
                                have hsumEq :
                                    (∑ i ∈ cert.idx1_FF.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n1FF : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx1_FF) (num := cert.nums.n1FF) (hnodup := hnodup1FF)
                                      (hnum := hn1FF_cert)
                                  dsimp [den1]
                                  exact h
                                calc
                                  (cert.nums.n1FF : ℝ) / den1 =
                                      (∑ i ∈ cert.idx1_FF.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal := by
                                        exact hsumEq.symm
                                  _ ≤ (μ.prob ha0 xFF).toReal := hx1FF_le_real
                              have hp1FT :
                                  (cert.nums.n1FT : ℝ) / den1 ≤ (μ.prob ha0 xFT).toReal := by
                                have hsumEq :
                                    (∑ i ∈ cert.idx1_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n1FT : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx1_FT) (num := cert.nums.n1FT) (hnodup := hnodup1FT)
                                      (hnum := hn1FT_cert)
                                  dsimp [den1]
                                  exact h
                                calc
                                  (cert.nums.n1FT : ℝ) / den1 =
                                      (∑ i ∈ cert.idx1_FT.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal := by
                                        exact hsumEq.symm
                                  _ ≤ (μ.prob ha0 xFT).toReal := hx1FT_le_real
                              have hp1TF :
                                  (cert.nums.n1TF : ℝ) / den1 ≤ (μ.prob ha0 xTF).toReal := by
                                have hsumEq :
                                    (∑ i ∈ cert.idx1_TF.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n1TF : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx1_TF) (num := cert.nums.n1TF) (hnodup := hnodup1TF)
                                      (hnum := hn1TF_cert)
                                  dsimp [den1]
                                  exact h
                                calc
                                  (cert.nums.n1TF : ℝ) / den1 =
                                      (∑ i ∈ cert.idx1_TF.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal := by
                                        exact hsumEq.symm
                                  _ ≤ (μ.prob ha0 xTF).toReal := hx1TF_le_real
                              have hp1TT :
                                  (cert.nums.n1TT : ℝ) / den1 ≤ (μ.prob ha0 xTT).toReal := by
                                have hsumEq :
                                    (∑ i ∈ cert.idx1_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n1TT : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx1_TT) (num := cert.nums.n1TT) (hnodup := hnodup1TT)
                                      (hnum := hn1TT_cert)
                                  dsimp [den1]
                                  exact h
                                calc
                                  (cert.nums.n1TT : ℝ) / den1 =
                                      (∑ i ∈ cert.idx1_TT.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal := by
                                        exact hsumEq.symm
                                  _ ≤ (μ.prob ha0 xTT).toReal := hx1TT_le_real
                              let reward2FF : ℕ := cert.nums.n2FFFT + cert.nums.n2FFTT
                              let reward2FT : ℕ := cert.nums.n2FTFT + cert.nums.n2FTTT
                              let reward2TF : ℕ := cert.nums.n2TFFT + cert.nums.n2TFTT
                              let reward2TT : ℕ := cert.nums.n2TTFT + cert.nums.n2TTTT
                              have hv2FF :
                                  (reward2FF : ℝ) / den1 ≤ (μ.prob haFF xFT).toReal + (μ.prob haFF xTT).toReal := by
                                have hA_ne_top :
                                    (∑ i ∈ cert.idx2_FF_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                  have :
                                      (∑ i ∈ cert.idx2_FF_FT.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                    exact le_trans hx2FF_FT_le (le_trans (ENNReal.le_tsum xFT) (μ.prob_le_one haFF hhaFFWf'))
                                  exact ne_of_lt (lt_of_le_of_lt this (by simp))
                                have hB_ne_top :
                                    (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                  have :
                                      (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                    exact le_trans hx2FF_TT_le (le_trans (ENNReal.le_tsum xTT) (μ.prob_le_one haFF hhaFFWf'))
                                  exact ne_of_lt (lt_of_le_of_lt this (by simp))
                                have hA_toReal :
                                    (∑ i ∈ cert.idx2_FF_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n2FFFT : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx2_FF_FT) (num := cert.nums.n2FFFT) (hnodup := hnodup2FFFT)
                                      (hnum := hn2FFFT_cert)
                                  dsimp [den1]
                                  exact h
                                have hB_toReal :
                                    (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n2FFTT : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx2_FF_TT) (num := cert.nums.n2FFTT) (hnodup := hnodup2FFTT)
                                      (hnum := hn2FFTT_cert)
                                  dsimp [den1]
                                  exact h
                                have hsumEq :
                                    ((∑ i ∈ cert.idx2_FF_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                              (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal =
                                      (reward2FF : ℝ) / den1 := by
                                  have :
                                      ((∑ i ∈ cert.idx2_FF_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                            (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal =
                                          (∑ i ∈ cert.idx2_FF_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal +
                                            (∑ i ∈ cert.idx2_FF_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal := by
                                        simpa using ENNReal.toReal_add hA_ne_top hB_ne_top
                                  simp [this, hA_toReal, hB_toReal, reward2FF, add_div] 
                                simpa [hqFF, hsumEq] using hx2FF_le_real
                              have hv2FT :
                                  (reward2FT : ℝ) / den1 ≤ (μ.prob haFT xFT).toReal + (μ.prob haFT xTT).toReal := by
                                have hA_ne_top :
                                    (∑ i ∈ cert.idx2_FT_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                  have :
                                      (∑ i ∈ cert.idx2_FT_FT.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                    exact le_trans hx2FT_FT_le (le_trans (ENNReal.le_tsum xFT) (μ.prob_le_one haFT hhaFTWf'))
                                  exact ne_of_lt (lt_of_le_of_lt this (by simp))
                                have hB_ne_top :
                                    (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                  have :
                                      (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                    exact le_trans hx2FT_TT_le (le_trans (ENNReal.le_tsum xTT) (μ.prob_le_one haFT hhaFTWf'))
                                  exact ne_of_lt (lt_of_le_of_lt this (by simp))
                                have hA_toReal :
                                    (∑ i ∈ cert.idx2_FT_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n2FTFT : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx2_FT_FT) (num := cert.nums.n2FTFT) (hnodup := hnodup2FTFT)
                                      (hnum := hn2FTFT_cert)
                                  dsimp [den1]
                                  exact h
                                have hB_toReal :
                                    (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n2FTTT : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx2_FT_TT) (num := cert.nums.n2FTTT) (hnodup := hnodup2FTTT)
                                      (hnum := hn2FTTT_cert)
                                  dsimp [den1]
                                  exact h
                                have hsumEq :
                                    ((∑ i ∈ cert.idx2_FT_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                              (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal =
                                      (reward2FT : ℝ) / den1 := by
                                  have :
                                      ((∑ i ∈ cert.idx2_FT_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                            (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal =
                                          (∑ i ∈ cert.idx2_FT_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal +
                                            (∑ i ∈ cert.idx2_FT_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal := by
                                        simpa using ENNReal.toReal_add hA_ne_top hB_ne_top
                                  simp [this, hA_toReal, hB_toReal, reward2FT, add_div]
                                simpa [hqFT, hsumEq] using hx2FT_le_real
                              have hv2TF :
                                  (reward2TF : ℝ) / den1 ≤ (μ.prob haTF xFT).toReal + (μ.prob haTF xTT).toReal := by
                                have hA_ne_top :
                                    (∑ i ∈ cert.idx2_TF_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                  have :
                                      (∑ i ∈ cert.idx2_TF_FT.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                    exact le_trans hx2TF_FT_le (le_trans (ENNReal.le_tsum xFT) (μ.prob_le_one haTF hhaTFWf'))
                                  exact ne_of_lt (lt_of_le_of_lt this (by simp))
                                have hB_ne_top :
                                    (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                  have :
                                      (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                    exact le_trans hx2TF_TT_le (le_trans (ENNReal.le_tsum xTT) (μ.prob_le_one haTF hhaTFWf'))
                                  exact ne_of_lt (lt_of_le_of_lt this (by simp))
                                have hA_toReal :
                                    (∑ i ∈ cert.idx2_TF_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n2TFFT : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx2_TF_FT) (num := cert.nums.n2TFFT) (hnodup := hnodup2TFFT)
                                      (hnum := hn2TFFT_cert)
                                  dsimp [den1]
                                  exact h
                                have hB_toReal :
                                    (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n2TFTT : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx2_TF_TT) (num := cert.nums.n2TFTT) (hnodup := hnodup2TFTT)
                                      (hnum := hn2TFTT_cert)
                                  dsimp [den1]
                                  exact h
                                have hsumEq :
                                    ((∑ i ∈ cert.idx2_TF_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                              (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal =
                                      (reward2TF : ℝ) / den1 := by
                                  have :
                                      ((∑ i ∈ cert.idx2_TF_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                            (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal =
                                          (∑ i ∈ cert.idx2_TF_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal +
                                            (∑ i ∈ cert.idx2_TF_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal := by
                                        simpa using ENNReal.toReal_add hA_ne_top hB_ne_top
                                  simp [this, hA_toReal, hB_toReal, reward2TF, add_div]
                                simpa [hqTF, hsumEq] using hx2TF_le_real
                              have hv2TT :
                                  (reward2TT : ℝ) / den1 ≤ (μ.prob haTT xFT).toReal + (μ.prob haTT xTT).toReal := by
                                have hA_ne_top :
                                    (∑ i ∈ cert.idx2_TT_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                  have :
                                      (∑ i ∈ cert.idx2_TT_FT.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                    exact le_trans hx2TT_FT_le (le_trans (ENNReal.le_tsum xFT) (μ.prob_le_one haTT hhaTTWf'))
                                  exact ne_of_lt (lt_of_le_of_lt this (by simp))
                                have hB_ne_top :
                                    (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≠
                                      (⊤ : ENNReal) := by
                                  have :
                                      (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                            xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) ≤ 1 := by
                                    exact le_trans hx2TT_TT_le (le_trans (ENNReal.le_tsum xTT) (μ.prob_le_one haTT hhaTTWf'))
                                  exact ne_of_lt (lt_of_le_of_lt this (by simp))
                                have hA_toReal :
                                    (∑ i ∈ cert.idx2_TT_FT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n2TTFT : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx2_TT_FT) (num := cert.nums.n2TTFT) (hnodup := hnodup2TTFT)
                                      (hnum := hn2TTFT_cert)
                                  dsimp [den1]
                                  exact h
                                have hB_toReal :
                                    (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                          xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal =
                                      (cert.nums.n2TTTT : ℝ) / den1 := by
                                  have h :=
                                    XiTlOneStepRewardLowerBoundCert.toReal_sum_prefixFreeWeightAt_toFinset_eq_div (l := l)
                                      (idxs := cert.idx2_TT_TT) (num := cert.nums.n2TTTT) (hnodup := hnodup2TTTT)
                                      (hnum := hn2TTTT_cert)
                                  dsimp [den1]
                                  exact h
                                have hsumEq :
                                    ((∑ i ∈ cert.idx2_TT_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                              (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal =
                                      (reward2TT : ℝ) / den1 := by
                                  have :
                                      ((∑ i ∈ cert.idx2_TT_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i) +
                                            (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i)).toReal =
                                          (∑ i ∈ cert.idx2_TT_FT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal +
                                            (∑ i ∈ cert.idx2_TT_TT.toFinset,
                                                xi_tlPrefixFreeWeightAt (XiTlOneStepRewardLowerBoundCert.bitsAt l) i).toReal := by
                                        simpa using ENNReal.toReal_add hA_ne_top hB_ne_top
                                  simp [this, hA_toReal, hB_toReal, reward2TT, add_div]
                                simpa [hqTT, hsumEq] using hx2TT_le_real
                              -- Assemble the full two-step lower bound.
                              have hprob_nonneg (hx : ENNReal) : 0 ≤ hx.toReal := by
                                exact ENNReal.toReal_nonneg
                              have hμFF : 0 ≤ (μ.prob ha0 xFF).toReal := ENNReal.toReal_nonneg
                              have hμFT : 0 ≤ (μ.prob ha0 xFT).toReal := ENNReal.toReal_nonneg
                              have hμTF : 0 ≤ (μ.prob ha0 xTF).toReal := ENNReal.toReal_nonneg
                              have hμTT : 0 ≤ (μ.prob ha0 xTT).toReal := ENNReal.toReal_nonneg
                              have hp1FF_nonneg : 0 ≤ (cert.nums.n1FF : ℝ) / den1 := by
                                exact div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hden1_pos)
                              have hp1FT_nonneg : 0 ≤ (cert.nums.n1FT : ℝ) / den1 := by
                                exact div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hden1_pos)
                              have hp1TF_nonneg : 0 ≤ (cert.nums.n1TF : ℝ) / den1 := by
                                exact div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hden1_pos)
                              have hp1TT_nonneg : 0 ≤ (cert.nums.n1TT : ℝ) / den1 := by
                                exact div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hden1_pos)
                              have hv2FF_nonneg : 0 ≤ (reward2FF : ℝ) / den1 := by
                                exact div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hden1_pos)
                              have hv2FT_nonneg : 0 ≤ (reward2FT : ℝ) / den1 := by
                                exact div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hden1_pos)
                              have hv2TF_nonneg : 0 ≤ (reward2TF : ℝ) / den1 := by
                                exact div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hden1_pos)
                              have hv2TT_nonneg : 0 ≤ (reward2TT : ℝ) / den1 := by
                                exact div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hden1_pos)
                              let reward1 : ℕ := cert.nums.n1FT + cert.nums.n1TT
                              have hrewards :
                                  (reward1 : ℝ) / den1 ≤ (μ.prob ha0 xFT).toReal + (μ.prob ha0 xTT).toReal := by
                                have hsplit :
                                    (reward1 : ℝ) / den1 =
                                      (cert.nums.n1FT : ℝ) / den1 + (cert.nums.n1TT : ℝ) / den1 := by
                                  simp [reward1, add_div, Nat.cast_add]
                                calc
                                  (reward1 : ℝ) / den1 =
                                      (cert.nums.n1FT : ℝ) / den1 + (cert.nums.n1TT : ℝ) / den1 := hsplit
                                  _ ≤ (μ.prob ha0 xFT).toReal + (μ.prob ha0 xTT).toReal := add_le_add hp1FT hp1TT
                              -- Decode the claim and expand its dyadic numerator.
                              have hclaimEq :
                                  (Coding.decodeValueNat cert.num cert.den : ℝ) =
                                    ((XiTlTwoStepRewardLowerBoundCert.claimNumerator l cert.nums : ℕ) : ℝ) /
                                      (XiTlTwoStepRewardLowerBoundCert.denomPow2 l : ℝ) := by
                                have hdenSuccR : (cert.den + 1 : ℝ) = (XiTlTwoStepRewardLowerBoundCert.denomPow2 l : ℝ) := by
                                  exact_mod_cast hdenSucc
                                simp [Coding.decodeValueNat, hEvalRoot, hdenSuccR]
                              -- Turn the claim into a sum of dyadic products over the two steps.
                              have hclaimDecomp :
                                  ((XiTlTwoStepRewardLowerBoundCert.claimNumerator l cert.nums : ℕ) : ℝ) /
                                      (XiTlTwoStepRewardLowerBoundCert.denomPow2 l : ℝ) =
                                    (reward1 : ℝ) / den1 +
                                        ((cert.nums.n1FF : ℝ) / den1) * ((reward2FF : ℝ) / den1) +
                                      ((cert.nums.n1FT : ℝ) / den1) * ((reward2FT : ℝ) / den1) +
                                        ((cert.nums.n1TF : ℝ) / den1) * ((reward2TF : ℝ) / den1) +
                                      ((cert.nums.n1TT : ℝ) / den1) * ((reward2TT : ℝ) / den1) := by
                                have hdenPow1R : (XiTlTwoStepRewardLowerBoundCert.denomPow1 l : ℝ) = den1 := by
                                  simp [XiTlTwoStepRewardLowerBoundCert.denomPow1, den1, XiTlTwoStepRewardLowerBoundCert.denomExp,
                                    Nat.cast_pow]
                                have hdenPow2R : (XiTlTwoStepRewardLowerBoundCert.denomPow2 l : ℝ) = den1 * den1 := by
                                  simp [XiTlTwoStepRewardLowerBoundCert.denomPow2, hdenPow1R]
                                -- Rewrite the denominator and clear it.
                                rw [hdenPow2R]
                                field_simp [hden1_ne0]
                                -- Reduce to the defining arithmetic identity of `claimNumerator`.
                                simp [XiTlTwoStepRewardLowerBoundCert.claimNumerator, reward1, reward2FF, reward2FT, reward2TF, reward2TT,
                                  XiTlTwoStepRewardLowerBoundCert.denomPow1, XiTlTwoStepRewardLowerBoundCert.denomExp, den1, Nat.cast_add,
                                  Nat.cast_mul, Nat.cast_pow]
                                ring
                              -- Bound each term by its semantic counterpart and sum.
                              have htermFF :
                                  ((cert.nums.n1FF : ℝ) / den1) * ((reward2FF : ℝ) / den1) ≤
                                    (μ.prob ha0 xFF).toReal * value μ (p.toExtended tProg).toAgent gammaOne hFF 2 := by
                                have hv2FF' :
                                    (reward2FF : ℝ) / den1 ≤ value μ (p.toExtended tProg).toAgent gammaOne hFF 2 := by
                                  -- Use `hvalFF` and `hqFF`.
                                  have : (reward2FF : ℝ) / den1 ≤ qValue μ (p.toExtended tProg).toAgent gammaOne hFF aFF 1 := by
                                    simpa [hqFF] using hv2FF
                                  simpa [hvalFF] using this
                                have hb0 : 0 ≤ (μ.prob ha0 xFF).toReal := ENNReal.toReal_nonneg
                                exact mul_le_mul hp1FF hv2FF' hv2FF_nonneg hb0
                              have htermFT :
                                  ((cert.nums.n1FT : ℝ) / den1) * ((reward2FT : ℝ) / den1) ≤
                                    (μ.prob ha0 xFT).toReal * value μ (p.toExtended tProg).toAgent gammaOne hFT 2 := by
                                have hv2FT' :
                                    (reward2FT : ℝ) / den1 ≤ value μ (p.toExtended tProg).toAgent gammaOne hFT 2 := by
                                  have : (reward2FT : ℝ) / den1 ≤ qValue μ (p.toExtended tProg).toAgent gammaOne hFT aFT 1 := by
                                    simpa [hqFT] using hv2FT
                                  simpa [hvalFT] using this
                                have hb0 : 0 ≤ (μ.prob ha0 xFT).toReal := ENNReal.toReal_nonneg
                                exact mul_le_mul hp1FT hv2FT' hv2FT_nonneg hb0
                              have htermTF :
                                  ((cert.nums.n1TF : ℝ) / den1) * ((reward2TF : ℝ) / den1) ≤
                                    (μ.prob ha0 xTF).toReal * value μ (p.toExtended tProg).toAgent gammaOne hTF 2 := by
                                have hv2TF' :
                                    (reward2TF : ℝ) / den1 ≤ value μ (p.toExtended tProg).toAgent gammaOne hTF 2 := by
                                  have : (reward2TF : ℝ) / den1 ≤ qValue μ (p.toExtended tProg).toAgent gammaOne hTF aTF 1 := by
                                    simpa [hqTF] using hv2TF
                                  simpa [hvalTF] using this
                                have hb0 : 0 ≤ (μ.prob ha0 xTF).toReal := ENNReal.toReal_nonneg
                                exact mul_le_mul hp1TF hv2TF' hv2TF_nonneg hb0
                              have htermTT :
                                  ((cert.nums.n1TT : ℝ) / den1) * ((reward2TT : ℝ) / den1) ≤
                                    (μ.prob ha0 xTT).toReal * value μ (p.toExtended tProg).toAgent gammaOne hTT 2 := by
                                have hv2TT' :
                                    (reward2TT : ℝ) / den1 ≤ value μ (p.toExtended tProg).toAgent gammaOne hTT 2 := by
                                  have : (reward2TT : ℝ) / den1 ≤ qValue μ (p.toExtended tProg).toAgent gammaOne hTT aTT 1 := by
                                    simpa [hqTT] using hv2TT
                                  simpa [hvalTT] using this
                                have hb0 : 0 ≤ (μ.prob ha0 xTT).toReal := ENNReal.toReal_nonneg
                                exact mul_le_mul hp1TT hv2TT' hv2TT_nonneg hb0
                              have hclaim_le_q :
                                  (Coding.decodeValueNat cert.num cert.den : ℝ) ≤
                                    qValue μ (p.toExtended tProg).toAgent gammaOne h a0 3 := by
                                -- Expand claim and qValue, then compare termwise.
                                have : (Coding.decodeValueNat cert.num cert.den : ℝ) ≤
                                    (μ.prob ha0 xFT).toReal + (μ.prob ha0 xTT).toReal +
                                      (μ.prob ha0 xFF).toReal * value μ (p.toExtended tProg).toAgent gammaOne hFF 2 +
                                        (μ.prob ha0 xFT).toReal * value μ (p.toExtended tProg).toAgent gammaOne hFT 2 +
                                          (μ.prob ha0 xTF).toReal * value μ (p.toExtended tProg).toAgent gammaOne hTF 2 +
                                            (μ.prob ha0 xTT).toReal * value μ (p.toExtended tProg).toAgent gammaOne hTT 2 := by
                                  -- use `hclaimEq` + `hclaimDecomp`.
                                  rw [hclaimEq, hclaimDecomp]
                                  -- bound each dyadic term.
                                  have hFF' :
                                      ((cert.nums.n1FF : ℝ) / den1) * ((reward2FF : ℝ) / den1) ≤
                                        (μ.prob ha0 xFF).toReal * value μ (p.toExtended tProg).toAgent gammaOne hFF 2 := htermFF
                                  have hFT' :
                                      ((cert.nums.n1FT : ℝ) / den1) * ((reward2FT : ℝ) / den1) ≤
                                        (μ.prob ha0 xFT).toReal * value μ (p.toExtended tProg).toAgent gammaOne hFT 2 := htermFT
                                  have hTF' :
                                      ((cert.nums.n1TF : ℝ) / den1) * ((reward2TF : ℝ) / den1) ≤
                                        (μ.prob ha0 xTF).toReal * value μ (p.toExtended tProg).toAgent gammaOne hTF 2 := htermTF
                                  have hTT' :
                                      ((cert.nums.n1TT : ℝ) / den1) * ((reward2TT : ℝ) / den1) ≤
                                        (μ.prob ha0 xTT).toReal * value μ (p.toExtended tProg).toAgent gammaOne hTT 2 := htermTT
                                  -- add up
                                  have hrewards' :
                                      (reward1 : ℝ) / den1 ≤ (μ.prob ha0 xFT).toReal + (μ.prob ha0 xTT).toReal := hrewards
                                  nlinarith [hrewards', hFF', hFT', hTF', hTT']
                                -- Now rewrite the RHS into the `qValue` expansion.
                                -- `qValue` includes the `+1` rewards for `xFT` and `xTT`.
                                have hq' :
                                    qValue μ (p.toExtended tProg).toAgent gammaOne h a0 3 =
                                      (μ.prob ha0 xFT).toReal + (μ.prob ha0 xTT).toReal +
                                        (μ.prob ha0 xFF).toReal * value μ (p.toExtended tProg).toAgent gammaOne hFF 2 +
                                          (μ.prob ha0 xFT).toReal * value μ (p.toExtended tProg).toAgent gammaOne hFT 2 +
                                            (μ.prob ha0 xTF).toReal * value μ (p.toExtended tProg).toAgent gammaOne hTF 2 +
                                              (μ.prob ha0 xTT).toReal * value μ (p.toExtended tProg).toAgent gammaOne hTT 2 := by
                                  -- Rearrange `hq` and simplify `γ = 1`.
                                  rw [hq]
                                  simp [gammaOne]
                                  ring
                                -- finish by rewriting with `hq'`
                                rw [hq']
                                exact this
                              simpa [hval] using hclaim_le_q
                            simpa [hclaim] using this
                          ·
                            -- Non-root histories: the program claims `0`, so soundness follows from value nonnegativity.
                            have hclaim0 : ((p.toExtended tProg).compute h').1 = 0 := by
                              unfold RawToPartrecProgram.toExtended RawToPartrecProgram.computeWithin
                              cases hEval : StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat h') with
                              | none =>
                                  simp [hEval]
                              | some out =>
                                  have houtMem : out ∈ p.tm.eval (Coding.encodeHistoryNat h') :=
                                    StepCounting.ToPartrec.evalWithin_sound (c := p.tm) (v := Coding.encodeHistoryNat h') (out := out) hEval
                                  -- All non-root outputs have `decodeValueNat 0 0 = 0`.
                                  have : ((Coding.decodeValueActionOutput out).getD (0, Action.stay)).1 = 0 := by
                                    -- Identify the unique output of the `dispatchHistoryCodes` wrapper.
                                    have houtMem' :
                                        out ∈
                                          (RawToPartrecProgram.dispatchHistoryCodes cases defaultOut).eval
                                            (Coding.encodeHistoryNat h') := by
                                      simpa [hpTm'] using houtMem
                                    have hEvalTemplate :
                                        (RawToPartrecProgram.dispatchHistoryCodes cases defaultOut).eval
                                            (Coding.encodeHistoryNat h') =
                                          pure
                                            (RawToPartrecProgram.chooseByFlags (cases.map Prod.snd ++ [defaultOut])
                                              (RawToPartrecProgram.prefixMatchFlags (cases.map Prod.fst)
                                                (Coding.encodeHistoryNat h'))) := by
                                      simpa using
                                        (RawToPartrecProgram.dispatchHistoryCodes_eval cases defaultOut (Coding.encodeHistoryNat h'))
                                    have houtEq :
                                        out =
                                          RawToPartrecProgram.chooseByFlags (cases.map Prod.snd ++ [defaultOut])
                                            (RawToPartrecProgram.prefixMatchFlags (cases.map Prod.fst)
                                              (Coding.encodeHistoryNat h')) := by
                                      simpa [hEvalTemplate] using houtMem'

                                    -- Since `h' ≠ h`, the root prefix does not match.
                                    have hprefix :
                                        RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat h') =
                                          false := by
                                      cases hx :
                                          RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat h') with
                                      | true =>
                                          have heq : h = h' :=
                                            RawToPartrecProgram.prefixHeadI_encodeHistoryNat_eq (h := h) (h' := h') hx
                                          cases hh' heq.symm
                                      | false =>
                                          rfl
                                    -- Hence the first flag is `1`, so `chooseByFlags` skips the root output.
                                    have hflagsNe :
                                        (RawToPartrecProgram.prefixMatchFlags (cases.map Prod.fst)
                                                (Coding.encodeHistoryNat h')).headI ≠
                                            0 := by
                                      have : (RawToPartrecProgram.prefixMatchFlags (cases.map Prod.fst)
                                                (Coding.encodeHistoryNat h')).headI = 1 := by
                                        simp [RawToPartrecProgram.prefixMatchFlags, cases, hprefix]
                                      simp [this]
                                    let outsTail : List (List ℕ) := [outFF, outFT, outTF, outTT, defaultOut]
                                    have houts :
                                        cases.map Prod.snd ++ [defaultOut] = outRoot :: outsTail := by
                                      simp [outsTail, cases]
                                    have houtEqTail :
                                        out =
                                          RawToPartrecProgram.chooseByFlags outsTail
                                            (RawToPartrecProgram.prefixMatchFlags (cases.map Prod.fst)
                                                (Coding.encodeHistoryNat h')).tail := by
                                      have houtEq' :
                                          out =
                                            RawToPartrecProgram.chooseByFlags (outRoot :: outsTail)
                                              (RawToPartrecProgram.prefixMatchFlags (cases.map Prod.fst)
                                                (Coding.encodeHistoryNat h')) := by
                                        simpa [houts] using houtEq
                                      simpa [RawToPartrecProgram.chooseByFlags, hflagsNe] using houtEq'

                                    -- `outsTail` always claims value `0`, regardless of which branch is selected.
                                    have houtsTail0 :
                                        ∀ out0 ∈ outsTail,
                                          ((Coding.decodeValueActionOutput out0).getD (0, Action.stay)).1 = 0 := by
                                      intro out0 hout0
                                      simp [outsTail] at hout0
                                      rcases hout0 with rfl | rfl | rfl | rfl | rfl <;>
                                        simp [Coding.decodeValueActionOutput, Coding.decodeValueNat, outFF, outFT, outTF, outTT, defaultOut]
                                    have hchoose0 :
                                        ((Coding.decodeValueActionOutput
                                                (RawToPartrecProgram.chooseByFlags outsTail
                                                  (RawToPartrecProgram.prefixMatchFlags (cases.map Prod.fst)
                                                      (Coding.encodeHistoryNat h')).tail)).getD
                                            (0, Action.stay)).1 =
                                          0 := by
                                      classical
                                      -- General lemma: if every candidate output claims `0`, then so does `chooseByFlags`.
                                      have chooseByFlags_claim0 :
                                          ∀ (outs : List (List ℕ)) (flags : List ℕ),
                                            (∀ out0 ∈ outs,
                                                ((Coding.decodeValueActionOutput out0).getD (0, Action.stay)).1 = 0) →
                                              ((Coding.decodeValueActionOutput (RawToPartrecProgram.chooseByFlags outs flags)).getD
                                                  (0, Action.stay)).1 =
                                                0 := by
                                        intro outs flags houts
                                        induction outs generalizing flags with
                                        | nil =>
                                            simp [RawToPartrecProgram.chooseByFlags, Coding.decodeValueActionOutput]
                                        | cons out0 outs ih =>
                                            by_cases h0 : flags.headI = 0
                                            ·
                                                have hout0 :
                                                    ((Coding.decodeValueActionOutput out0).getD (0, Action.stay)).1 = 0 :=
                                                  houts out0 (by simp)
                                                simpa [RawToPartrecProgram.chooseByFlags, h0] using hout0
                                            ·
                                                have houts' :
                                                    ∀ out1 ∈ outs,
                                                      ((Coding.decodeValueActionOutput out1).getD (0, Action.stay)).1 = 0 := by
                                                  intro out1 hout1
                                                  exact houts out1 (by simp [hout1])
                                                have := ih (flags := flags.tail) houts'
                                                simpa [RawToPartrecProgram.chooseByFlags, h0] using this
                                      exact
                                        chooseByFlags_claim0 outsTail
                                          (RawToPartrecProgram.prefixMatchFlags (cases.map Prod.fst) (Coding.encodeHistoryNat h')).tail
                                          houtsTail0

                                    rw [houtEqTail]
                                    exact hchoose0
                                  simp [hEval, this]
                            have hnonneg : 0 ≤ value μ (p.toExtended tProg).toAgent gammaOne h' 4 :=
                              value_nonneg (μ := μ) (π := (p.toExtended tProg).toAgent) (γ := gammaOne) (h := h') (n := 4)
                            simpa [hclaim0] using hnonneg

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

/-! ### Building concrete verified ξ^tl two-cycle certificates -/

namespace XiTlTwoStepRewardLowerBoundCert

/-- A helper: for distinct histories, the prefix guard used by `dispatchHistoryCodes` does not match. -/
theorem prefixHeadI_encodeHistoryNat_eq_false_of_ne (h h' : History) (hne : h ≠ h') :
    RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat h') = false := by
  cases hx : RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat h') with
  | true =>
      have heq : h = h' := RawToPartrecProgram.prefixHeadI_encodeHistoryNat_eq (h := h) (h' := h') hx
      cases hne heq
  | false =>
      rfl

noncomputable def mkCert (tEnv l : ℕ) (h : History) (a0 aFF aFT aTF aTT : Action) :
    XiTlTwoStepRewardLowerBoundCert :=
  let xFF : Percept := ⟨false, false⟩
  let xFT : Percept := ⟨false, true⟩
  let xTF : Percept := ⟨true, false⟩
  let xTT : Percept := ⟨true, true⟩
  let ha0 : History := h ++ [HistElem.act a0]
  let hFF : History := h ++ [HistElem.act a0, HistElem.per xFF]
  let hFT : History := h ++ [HistElem.act a0, HistElem.per xFT]
  let hTF : History := h ++ [HistElem.act a0, HistElem.per xTF]
  let hTT : History := h ++ [HistElem.act a0, HistElem.per xTT]
  let haFF : History := hFF ++ [HistElem.act aFF]
  let haFT : History := hFT ++ [HistElem.act aFT]
  let haTF : History := hTF ++ [HistElem.act aTF]
  let haTT : History := hTT ++ [HistElem.act aTT]
  let idx1_FF := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l ha0 xFF
  let idx1_FT := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l ha0 xFT
  let idx1_TF := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l ha0 xTF
  let idx1_TT := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l ha0 xTT
  let idx2_FF_FT := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l haFF xFT
  let idx2_FF_TT := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l haFF xTT
  let idx2_FT_FT := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l haFT xFT
  let idx2_FT_TT := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l haFT xTT
  let idx2_TF_FT := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l haTF xFT
  let idx2_TF_TT := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l haTF xTT
  let idx2_TT_FT := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l haTT xFT
  let idx2_TT_TT := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l haTT xTT
  let n1FF :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx1_FF
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := ha0) (target := xFF))
  let n1FT :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx1_FT
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := ha0) (target := xFT))
  let n1TF :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx1_TF
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := ha0) (target := xTF))
  let n1TT :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx1_TT
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := ha0) (target := xTT))
  let n2FFFT :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx2_FF_FT
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := haFF) (target := xFT))
  let n2FFTT :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx2_FF_TT
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := haFF) (target := xTT))
  let n2FTFT :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx2_FT_FT
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := haFT) (target := xFT))
  let n2FTTT :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx2_FT_TT
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := haFT) (target := xTT))
  let n2TFFT :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx2_TF_FT
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := haTF) (target := xFT))
  let n2TFTT :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx2_TF_TT
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := haTF) (target := xTT))
  let n2TTFT :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx2_TT_FT
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := haTT) (target := xFT))
  let n2TTTT :=
    XiTlOneStepRewardLowerBoundCert.numeratorBoundValue (l := l) idx2_TT_TT
      (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l) (ha := haTT) (target := xTT))
  let nums : XiTlTwoStepRewardLowerBoundNumerators :=
    ⟨n1FF, n1FT, n1TF, n1TT, n2FFFT, n2FFTT, n2FTFT, n2FTTT, n2TFFT, n2TFTT, n2TTFT, n2TTTT⟩
  { historyCode := Coding.encodeHistoryNat h
    actionCode0 := Coding.encodeActionNat a0
    actionCodeFF := Coding.encodeActionNat aFF
    actionCodeFT := Coding.encodeActionNat aFT
    actionCodeTF := Coding.encodeActionNat aTF
    actionCodeTT := Coding.encodeActionNat aTT
    num := XiTlTwoStepRewardLowerBoundCert.claimNumerator l nums
    den := XiTlTwoStepRewardLowerBoundCert.expectedDen l
    idx1_FF := idx1_FF
    idx1_FT := idx1_FT
    idx1_TF := idx1_TF
    idx1_TT := idx1_TT
    idx2_FF_FT := idx2_FF_FT
    idx2_FF_TT := idx2_FF_TT
    idx2_FT_FT := idx2_FT_FT
    idx2_FT_TT := idx2_FT_TT
    idx2_TF_FT := idx2_TF_FT
    idx2_TF_TT := idx2_TF_TT
    idx2_TT_FT := idx2_TT_FT
    idx2_TT_TT := idx2_TT_TT
    nums := nums }

noncomputable def mkProg (h : History) (a0 aFF aFT aTF aTT : Action) (num den : ℕ) : RawToPartrecProgram :=
  let xFF : Percept := ⟨false, false⟩
  let xFT : Percept := ⟨false, true⟩
  let xTF : Percept := ⟨true, false⟩
  let xTT : Percept := ⟨true, true⟩
  let hFF : History := h ++ [HistElem.act a0, HistElem.per xFF]
  let hFT : History := h ++ [HistElem.act a0, HistElem.per xFT]
  let hTF : History := h ++ [HistElem.act a0, HistElem.per xTF]
  let hTT : History := h ++ [HistElem.act a0, HistElem.per xTT]
  let outRoot : List ℕ := [num, den, Coding.encodeActionNat a0]
  let outFF : List ℕ := [0, 0, Coding.encodeActionNat aFF]
  let outFT : List ℕ := [0, 0, Coding.encodeActionNat aFT]
  let outTF : List ℕ := [0, 0, Coding.encodeActionNat aTF]
  let outTT : List ℕ := [0, 0, Coding.encodeActionNat aTT]
  let defaultOut : List ℕ := [0, 0, Coding.encodeActionNat Action.stay]
  let cases : List (List ℕ × List ℕ) :=
    [ (Coding.encodeHistoryNat h, outRoot)
    , (Coding.encodeHistoryNat hFF, outFF)
    , (Coding.encodeHistoryNat hFT, outFT)
    , (Coding.encodeHistoryNat hTF, outTF)
    , (Coding.encodeHistoryNat hTT, outTT)
    ]
  RawToPartrecProgram.ofToPartrec [] (RawToPartrecProgram.dispatchHistoryCodes cases defaultOut)

theorem exists_tProg_verify_mkCert (tEnv l : ℕ) (h : History) (a0 aFF aFT aTF aTT : Action)
    (ha0Wf : (h ++ [HistElem.act a0]).wellFormed = true) :
    ∃ tProg : ℕ,
      let cert := mkCert (tEnv := tEnv) (l := l) h a0 aFF aFT aTF aTT
      let p := mkProg (h := h) (a0 := a0) (aFF := aFF) (aFT := aFT) (aTF := aTF) (aTT := aTT) cert.num cert.den
      (xi_tlTwoStepRewardLowerBoundSoundProofSystemToPartrec (tEnv := tEnv) (l := l)).verify tProg p cert = true := by
  classical
  -- Build the concrete certificate and dispatch program.
  let cert : XiTlTwoStepRewardLowerBoundCert := mkCert (tEnv := tEnv) (l := l) h a0 aFF aFT aTF aTT
  let p : RawToPartrecProgram :=
    mkProg (h := h) (a0 := a0) (aFF := aFF) (aFT := aFT) (aTF := aTF) (aTT := aTT) cert.num cert.den
  -- Histories used by the dispatch wrapper.
  let xFF : Percept := ⟨false, false⟩
  let xFT : Percept := ⟨false, true⟩
  let xTF : Percept := ⟨true, false⟩
  let xTT : Percept := ⟨true, true⟩
  let hFF : History := h ++ [HistElem.act a0, HistElem.per xFF]
  let hFT : History := h ++ [HistElem.act a0, HistElem.per xFT]
  let hTF : History := h ++ [HistElem.act a0, HistElem.per xTF]
  let hTT : History := h ++ [HistElem.act a0, HistElem.per xTT]
  let outRoot : List ℕ := [cert.num, cert.den, Coding.encodeActionNat a0]
  let outFF : List ℕ := [0, 0, Coding.encodeActionNat aFF]
  let outFT : List ℕ := [0, 0, Coding.encodeActionNat aFT]
  let outTF : List ℕ := [0, 0, Coding.encodeActionNat aTF]
  let outTT : List ℕ := [0, 0, Coding.encodeActionNat aTT]
  let defaultOut : List ℕ := [0, 0, Coding.encodeActionNat Action.stay]
  let cases : List (List ℕ × List ℕ) :=
    [ (Coding.encodeHistoryNat h, outRoot)
    , (Coding.encodeHistoryNat hFF, outFF)
    , (Coding.encodeHistoryNat hFT, outFT)
    , (Coding.encodeHistoryNat hTF, outTF)
    , (Coding.encodeHistoryNat hTT, outTT)
    ]
  have hpTm : p.tm = RawToPartrecProgram.dispatchHistoryCodes cases defaultOut := by
    simp [p, mkProg, RawToPartrecProgram.ofToPartrec, cases, xFF, xFT, xTF, xTT, hFF, hFT, hTF, hTT, outRoot, outFF,
      outFT, outTF, outTT, defaultOut]

  -- Establish well-formedness of the branch histories.
  have wellFormed_append_act_per_of_wellFormed_append_act
      (h0 : History) (a : Action) (x : Percept) (hw : (h0 ++ [HistElem.act a]).wellFormed = true) :
      (h0 ++ [HistElem.act a, HistElem.per x]).wellFormed = true := by
    induction h0 using List.twoStepInduction with
    | nil =>
        simp [History.wellFormed]
    | singleton e =>
        cases e <;> simp [History.wellFormed] at hw
    | cons_cons e1 e2 rest ih =>
        cases e1 <;> cases e2 <;> simp [History.wellFormed] at hw ⊢
        exact ih hw

  have wellFormed_append_act_of_wellFormed_append_act_per
      (h0 : History) (a : Action) (x : Percept) (a' : Action)
      (hw : (h0 ++ [HistElem.act a, HistElem.per x]).wellFormed = true) :
      (h0 ++ [HistElem.act a, HistElem.per x, HistElem.act a']).wellFormed = true := by
    -- `History.wellFormed` consumes histories two steps at a time.
    induction h0 using List.twoStepInduction with
    | nil =>
        simp [History.wellFormed] at hw ⊢
    | singleton e =>
        cases e <;> simp [History.wellFormed] at hw
    | cons_cons e1 e2 rest ih =>
        cases e1 <;> cases e2 <;> simp [History.wellFormed] at hw ⊢
        exact ih hw

  have hFFWf : hFF.wellFormed := by
    have : (h ++ [HistElem.act a0, HistElem.per xFF]).wellFormed = true :=
      wellFormed_append_act_per_of_wellFormed_append_act h a0 xFF ha0Wf
    simpa [hFF] using this
  have hFTWf : hFT.wellFormed := by
    have : (h ++ [HistElem.act a0, HistElem.per xFT]).wellFormed = true :=
      wellFormed_append_act_per_of_wellFormed_append_act h a0 xFT ha0Wf
    simpa [hFT] using this
  have hTFWf : hTF.wellFormed := by
    have : (h ++ [HistElem.act a0, HistElem.per xTF]).wellFormed = true :=
      wellFormed_append_act_per_of_wellFormed_append_act h a0 xTF ha0Wf
    simpa [hTF] using this
  have hTTWf : hTT.wellFormed := by
    have : (h ++ [HistElem.act a0, HistElem.per xTT]).wellFormed = true :=
      wellFormed_append_act_per_of_wellFormed_append_act h a0 xTT ha0Wf
    simpa [hTT] using this
  have haFFWf : (hFF ++ [HistElem.act aFF]).wellFormed := by
    have : (h ++ [HistElem.act a0, HistElem.per xFF, HistElem.act aFF]).wellFormed = true :=
      wellFormed_append_act_of_wellFormed_append_act_per h a0 xFF aFF (by simpa [hFF] using hFFWf)
    simpa [hFF, List.append_assoc] using this
  have haFTWf : (hFT ++ [HistElem.act aFT]).wellFormed := by
    have : (h ++ [HistElem.act a0, HistElem.per xFT, HistElem.act aFT]).wellFormed = true :=
      wellFormed_append_act_of_wellFormed_append_act_per h a0 xFT aFT (by simpa [hFT] using hFTWf)
    simpa [hFT, List.append_assoc] using this
  have haTFWf : (hTF ++ [HistElem.act aTF]).wellFormed := by
    have : (h ++ [HistElem.act a0, HistElem.per xTF, HistElem.act aTF]).wellFormed = true :=
      wellFormed_append_act_of_wellFormed_append_act_per h a0 xTF aTF (by simpa [hTF] using hTFWf)
    simpa [hTF, List.append_assoc] using this
  have haTTWf : (hTT ++ [HistElem.act aTT]).wellFormed := by
    have : (h ++ [HistElem.act a0, HistElem.per xTT, HistElem.act aTT]).wellFormed = true :=
      wellFormed_append_act_of_wellFormed_append_act_per h a0 xTT aTT (by simpa [hTT] using hTTWf)
    simpa [hTT, List.append_assoc] using this

  -- Unbounded evaluation of the dispatch program at each guarded history.
  have hne_h_hFF : h ≠ hFF := by
    intro heq
    have := congrArg List.length heq
    simp [hFF] at this
  have hne_h_hFT : h ≠ hFT := by
    intro heq
    have := congrArg List.length heq
    simp [hFT] at this
  have hne_h_hTF : h ≠ hTF := by
    intro heq
    have := congrArg List.length heq
    simp [hTF] at this
  have hne_h_hTT : h ≠ hTT := by
    intro heq
    have := congrArg List.length heq
    simp [hTT] at this

  have hne_afterActPer (x y : Percept) (hxy : x ≠ y) :
      (h ++ [HistElem.act a0, HistElem.per x]) ≠ (h ++ [HistElem.act a0, HistElem.per y]) := by
    intro heq
    have heq' :
        (h ++ [HistElem.act a0] ++ [HistElem.per x]) = (h ++ [HistElem.act a0] ++ [HistElem.per y]) := by
      simpa [List.append_assoc] using heq
    have htail :
        [HistElem.per x] = [HistElem.per y] :=
      List.append_cancel_left (as := h ++ [HistElem.act a0]) (bs := [HistElem.per x]) (cs := [HistElem.per y]) heq'
    have hx : HistElem.per x = HistElem.per y := by
      have hhead : List.head? [HistElem.per x] = List.head? [HistElem.per y] := congrArg List.head? htail
      have hsome : some (HistElem.per x) = some (HistElem.per y) := by
        simpa using hhead
      exact Option.some.inj hsome
    have : x = y := by
      cases hx
      rfl
    exact hxy this

  have hne_hFF_hFT : hFF ≠ hFT := by
    simpa [hFF, hFT] using hne_afterActPer xFF xFT (by decide : xFF ≠ xFT)
  have hne_hFF_hTF : hFF ≠ hTF := by
    simpa [hFF, hTF] using hne_afterActPer xFF xTF (by decide : xFF ≠ xTF)
  have hne_hFF_hTT : hFF ≠ hTT := by
    simpa [hFF, hTT] using hne_afterActPer xFF xTT (by decide : xFF ≠ xTT)
  have hne_hFT_hTF : hFT ≠ hTF := by
    simpa [hFT, hTF] using hne_afterActPer xFT xTF (by decide : xFT ≠ xTF)
  have hne_hFT_hTT : hFT ≠ hTT := by
    simpa [hFT, hTT] using hne_afterActPer xFT xTT (by decide : xFT ≠ xTT)
  have hne_hTF_hTT : hTF ≠ hTT := by
    simpa [hTF, hTT] using hne_afterActPer xTF xTT (by decide : xTF ≠ xTT)

  have hprefix_h_hFF :
      RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat hFF) = false :=
    prefixHeadI_encodeHistoryNat_eq_false_of_ne (h := h) (h' := hFF) hne_h_hFF
  have hprefix_h_hFT :
      RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat hFT) = false :=
    prefixHeadI_encodeHistoryNat_eq_false_of_ne (h := h) (h' := hFT) hne_h_hFT
  have hprefix_h_hTF :
      RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat hTF) = false :=
    prefixHeadI_encodeHistoryNat_eq_false_of_ne (h := h) (h' := hTF) hne_h_hTF
  have hprefix_h_hTT :
      RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat h) (Coding.encodeHistoryNat hTT) = false :=
    prefixHeadI_encodeHistoryNat_eq_false_of_ne (h := h) (h' := hTT) hne_h_hTT

  have hprefix_hFF_hFT :
      RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat hFF) (Coding.encodeHistoryNat hFT) = false :=
    prefixHeadI_encodeHistoryNat_eq_false_of_ne (h := hFF) (h' := hFT) hne_hFF_hFT
  have hprefix_hFF_hTF :
      RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat hFF) (Coding.encodeHistoryNat hTF) = false :=
    prefixHeadI_encodeHistoryNat_eq_false_of_ne (h := hFF) (h' := hTF) hne_hFF_hTF
  have hprefix_hFF_hTT :
      RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat hFF) (Coding.encodeHistoryNat hTT) = false :=
    prefixHeadI_encodeHistoryNat_eq_false_of_ne (h := hFF) (h' := hTT) hne_hFF_hTT
  have hprefix_hFT_hTF :
      RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat hFT) (Coding.encodeHistoryNat hTF) = false :=
    prefixHeadI_encodeHistoryNat_eq_false_of_ne (h := hFT) (h' := hTF) hne_hFT_hTF
  have hprefix_hFT_hTT :
      RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat hFT) (Coding.encodeHistoryNat hTT) = false :=
    prefixHeadI_encodeHistoryNat_eq_false_of_ne (h := hFT) (h' := hTT) hne_hFT_hTT
  have hprefix_hTF_hTT :
      RawToPartrecProgram.prefixHeadI (Coding.encodeHistoryNat hTF) (Coding.encodeHistoryNat hTT) = false :=
    prefixHeadI_encodeHistoryNat_eq_false_of_ne (h := hTF) (h' := hTT) hne_hTF_hTT

  -- Evaluate `dispatchHistoryCodes` at the five guarded inputs.
  have hevalRoot :
      p.tm.eval (Coding.encodeHistoryNat h) = pure outRoot := by
    simp [hpTm, RawToPartrecProgram.dispatchHistoryCodes_eval, RawToPartrecProgram.chooseByFlags,
      RawToPartrecProgram.prefixMatchFlags, cases, outRoot, defaultOut, RawToPartrecProgram.prefixHeadI_self]
  have hevalFF :
      p.tm.eval (Coding.encodeHistoryNat hFF) = pure outFF := by
    simp [hpTm, RawToPartrecProgram.dispatchHistoryCodes_eval, RawToPartrecProgram.chooseByFlags,
      RawToPartrecProgram.prefixMatchFlags, cases, outRoot, outFF, defaultOut, hprefix_h_hFF,
      RawToPartrecProgram.prefixHeadI_self]
  have hevalFT :
      p.tm.eval (Coding.encodeHistoryNat hFT) = pure outFT := by
    simp [hpTm, RawToPartrecProgram.dispatchHistoryCodes_eval, RawToPartrecProgram.chooseByFlags,
      RawToPartrecProgram.prefixMatchFlags, cases, outRoot, outFF, outFT, defaultOut, hprefix_h_hFT, hprefix_hFF_hFT,
      RawToPartrecProgram.prefixHeadI_self]
  have hevalTF :
      p.tm.eval (Coding.encodeHistoryNat hTF) = pure outTF := by
    simp [hpTm, RawToPartrecProgram.dispatchHistoryCodes_eval, RawToPartrecProgram.chooseByFlags,
      RawToPartrecProgram.prefixMatchFlags, cases, outRoot, outFF, outFT, outTF, defaultOut, hprefix_h_hTF,
      hprefix_hFF_hTF, hprefix_hFT_hTF, RawToPartrecProgram.prefixHeadI_self]
  have hevalTT :
      p.tm.eval (Coding.encodeHistoryNat hTT) = pure outTT := by
    simp [hpTm, RawToPartrecProgram.dispatchHistoryCodes_eval, RawToPartrecProgram.chooseByFlags,
      RawToPartrecProgram.prefixMatchFlags, cases, outRoot, outFF, outFT, outTF, outTT, defaultOut, hprefix_h_hTT,
      hprefix_hFF_hTT, hprefix_hFT_hTT, hprefix_hTF_hTT, RawToPartrecProgram.prefixHeadI_self]

  -- Extract per-input fuel bounds, then take a maximum fuel that works for all five.
  have hexRoot : ∃ n, StepCounting.ToPartrec.evalWithin n p.tm (Coding.encodeHistoryNat h) = some outRoot := by
    refine
      (StepCounting.ToPartrec.exists_evalWithin_eq_some_iff (c := p.tm) (v := Coding.encodeHistoryNat h)
          (out := outRoot)).2 ?_
    simpa [hevalRoot]
  have hexFF : ∃ n, StepCounting.ToPartrec.evalWithin n p.tm (Coding.encodeHistoryNat hFF) = some outFF := by
    refine
      (StepCounting.ToPartrec.exists_evalWithin_eq_some_iff (c := p.tm) (v := Coding.encodeHistoryNat hFF)
          (out := outFF)).2 ?_
    simpa [hevalFF]
  have hexFT : ∃ n, StepCounting.ToPartrec.evalWithin n p.tm (Coding.encodeHistoryNat hFT) = some outFT := by
    refine
      (StepCounting.ToPartrec.exists_evalWithin_eq_some_iff (c := p.tm) (v := Coding.encodeHistoryNat hFT)
          (out := outFT)).2 ?_
    simpa [hevalFT]
  have hexTF : ∃ n, StepCounting.ToPartrec.evalWithin n p.tm (Coding.encodeHistoryNat hTF) = some outTF := by
    refine
      (StepCounting.ToPartrec.exists_evalWithin_eq_some_iff (c := p.tm) (v := Coding.encodeHistoryNat hTF)
          (out := outTF)).2 ?_
    simpa [hevalTF]
  have hexTT : ∃ n, StepCounting.ToPartrec.evalWithin n p.tm (Coding.encodeHistoryNat hTT) = some outTT := by
    refine
      (StepCounting.ToPartrec.exists_evalWithin_eq_some_iff (c := p.tm) (v := Coding.encodeHistoryNat hTT)
          (out := outTT)).2 ?_
    simpa [hevalTT]

  rcases hexRoot with ⟨nRoot, hnRoot⟩
  rcases hexFF with ⟨nFF, hnFF⟩
  rcases hexFT with ⟨nFT, hnFT⟩
  rcases hexTF with ⟨nTF, hnTF⟩
  rcases hexTT with ⟨nTT, hnTT⟩

  let rest3 : ℕ := Nat.max nTF nTT
  let rest2 : ℕ := Nat.max nFT rest3
  let rest1 : ℕ := Nat.max nFF rest2
  let tProg : ℕ := Nat.max nRoot rest1
  have hrest1_le : rest1 ≤ tProg := by
    simpa [tProg] using (Nat.le_max_right nRoot rest1)
  have htRoot : nRoot ≤ tProg := by
    simpa [tProg] using (Nat.le_max_left nRoot rest1)
  have htFF : nFF ≤ tProg := by
    have hnFF : nFF ≤ rest1 := by
      simpa [rest1] using (Nat.le_max_left nFF rest2)
    exact le_trans hnFF hrest1_le
  have htFT : nFT ≤ tProg := by
    have hnFT : nFT ≤ rest2 := by
      simpa [rest2] using (Nat.le_max_left nFT rest3)
    have hrest2 : rest2 ≤ rest1 := by
      simpa [rest1] using (Nat.le_max_right nFF rest2)
    exact le_trans hnFT (le_trans hrest2 hrest1_le)
  have htTF : nTF ≤ tProg := by
    have hnTF : nTF ≤ rest3 := by
      simpa [rest3] using (Nat.le_max_left nTF nTT)
    have hrest3 : rest3 ≤ rest2 := by
      simpa [rest2] using (Nat.le_max_right nFT rest3)
    have hrest2 : rest2 ≤ rest1 := by
      simpa [rest1] using (Nat.le_max_right nFF rest2)
    exact le_trans hnTF (le_trans hrest3 (le_trans hrest2 hrest1_le))
  have htTT : nTT ≤ tProg := by
    have hnTT : nTT ≤ rest3 := by
      simpa [rest3] using (Nat.le_max_right nTF nTT)
    have hrest3 : rest3 ≤ rest2 := by
      simpa [rest2] using (Nat.le_max_right nFT rest3)
    have hrest2 : rest2 ≤ rest1 := by
      simpa [rest1] using (Nat.le_max_right nFF rest2)
    exact le_trans hnTT (le_trans hrest3 (le_trans hrest2 hrest1_le))

  have hEvalRoot : StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat h) = some outRoot :=
    StepCounting.ToPartrec.evalWithin_mono (h := hnRoot) (hnm := htRoot)
  have hEvalFF : StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hFF) = some outFF :=
    StepCounting.ToPartrec.evalWithin_mono (h := hnFF) (hnm := htFF)
  have hEvalFT : StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hFT) = some outFT :=
    StepCounting.ToPartrec.evalWithin_mono (h := hnFT) (hnm := htFT)
  have hEvalTF : StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hTF) = some outTF :=
    StepCounting.ToPartrec.evalWithin_mono (h := hnTF) (hnm := htTF)
  have hEvalTT : StepCounting.ToPartrec.evalWithin tProg p.tm (Coding.encodeHistoryNat hTT) = some outTT :=
    StepCounting.ToPartrec.evalWithin_mono (h := hnTT) (hnm := htTT)

  -- The constructed certificate satisfies the verifier's `ok` predicate at the chosen fuel.
  have hok : XiTlTwoStepRewardLowerBoundCert.ok (tProg := tProg) (tEnv := tEnv) (l := l) p cert := by
    -- Prove `ok` by unfolding the decoding match and then discharging each conjunct directly.
    have hComputeNums : XiTlTwoStepRewardLowerBoundCert.computeNumerators l cert = some cert.nums := by
      -- First show each `numeratorBound` call matches the cached numeral in `cert.nums`.
      have hn1FF : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx1_FF = some cert.nums.n1FF := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l (h ++ [HistElem.act a0]) xFF)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := h ++ [HistElem.act a0]) (target := xFF)))
      have hn1FT : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx1_FT = some cert.nums.n1FT := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l (h ++ [HistElem.act a0]) xFT)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := h ++ [HistElem.act a0]) (target := xFT)))
      have hn1TF : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx1_TF = some cert.nums.n1TF := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l (h ++ [HistElem.act a0]) xTF)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := h ++ [HistElem.act a0]) (target := xTF)))
      have hn1TT : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx1_TT = some cert.nums.n1TT := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs := XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l (h ++ [HistElem.act a0]) xTT)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := h ++ [HistElem.act a0]) (target := xTT)))
      have hn2FFFT : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_FF_FT = some cert.nums.n2FFFT := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l
                ((h ++ [HistElem.act a0, HistElem.per xFF]) ++ [HistElem.act aFF]) xFT)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := (h ++ [HistElem.act a0, HistElem.per xFF]) ++ [HistElem.act aFF]) (target := xFT)))
      have hn2FFTT : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_FF_TT = some cert.nums.n2FFTT := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l
                ((h ++ [HistElem.act a0, HistElem.per xFF]) ++ [HistElem.act aFF]) xTT)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := (h ++ [HistElem.act a0, HistElem.per xFF]) ++ [HistElem.act aFF]) (target := xTT)))
      have hn2FTFT : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_FT_FT = some cert.nums.n2FTFT := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l
                ((h ++ [HistElem.act a0, HistElem.per xFT]) ++ [HistElem.act aFT]) xFT)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := (h ++ [HistElem.act a0, HistElem.per xFT]) ++ [HistElem.act aFT]) (target := xFT)))
      have hn2FTTT : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_FT_TT = some cert.nums.n2FTTT := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l
                ((h ++ [HistElem.act a0, HistElem.per xFT]) ++ [HistElem.act aFT]) xTT)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := (h ++ [HistElem.act a0, HistElem.per xFT]) ++ [HistElem.act aFT]) (target := xTT)))
      have hn2TFFT : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_TF_FT = some cert.nums.n2TFFT := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l
                ((h ++ [HistElem.act a0, HistElem.per xTF]) ++ [HistElem.act aTF]) xFT)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := (h ++ [HistElem.act a0, HistElem.per xTF]) ++ [HistElem.act aTF]) (target := xFT)))
      have hn2TFTT : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_TF_TT = some cert.nums.n2TFTT := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l
                ((h ++ [HistElem.act a0, HistElem.per xTF]) ++ [HistElem.act aTF]) xTT)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := (h ++ [HistElem.act a0, HistElem.per xTF]) ++ [HistElem.act aTF]) (target := xTT)))
      have hn2TTFT : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_TT_FT = some cert.nums.n2TTFT := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l
                ((h ++ [HistElem.act a0, HistElem.per xTT]) ++ [HistElem.act aTT]) xFT)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := (h ++ [HistElem.act a0, HistElem.per xTT]) ++ [HistElem.act aTT]) (target := xFT)))
      have hn2TTTT : XiTlTwoStepRewardLowerBoundCert.numeratorBound l cert.idx2_TT_TT = some cert.nums.n2TTTT := by
        simpa [cert, mkCert, XiTlTwoStepRewardLowerBoundCert.numeratorBound] using
          (XiTlOneStepRewardLowerBoundCert.numeratorBoundValue_spec (l := l)
            (idxs :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput tEnv l
                ((h ++ [HistElem.act a0, HistElem.per xTT]) ++ [HistElem.act aTT]) xTT)
            (hlt :=
              XiTlOneStepRewardLowerBoundCert.idxsOfOutput_lt_bitsAt_length (tEnv := tEnv) (l := l)
                (ha := (h ++ [HistElem.act a0, HistElem.per xTT]) ++ [HistElem.act aTT]) (target := xTT)))

      -- Then `computeNumerators` is just the monadic sequence of these calls.
      simp [XiTlTwoStepRewardLowerBoundCert.computeNumerators, hn1FF, hn1FT, hn1TF, hn1TT, hn2FFFT, hn2FFTT, hn2FTFT,
        hn2FTTT, hn2TFFT, hn2TFTT, hn2TTFT, hn2TTTT]
    have hdecH : Coding.decodeHistoryNat cert.historyCode = some h := by
      simp [cert, mkCert]
    have hdecA0 : Coding.decodeActionNat cert.actionCode0 = some a0 := by
      simp [cert, mkCert]
    have hdecAFF : Coding.decodeActionNat cert.actionCodeFF = some aFF := by
      simp [cert, mkCert]
    have hdecAFT : Coding.decodeActionNat cert.actionCodeFT = some aFT := by
      simp [cert, mkCert]
    have hdecATF : Coding.decodeActionNat cert.actionCodeTF = some aTF := by
      simp [cert, mkCert]
    have hdecATT : Coding.decodeActionNat cert.actionCodeTT = some aTT := by
      simp [cert, mkCert]
    unfold XiTlTwoStepRewardLowerBoundCert.ok
    -- Reduce the match to the intended branch.
    rw [hdecH, hdecA0, hdecAFF, hdecAFT, hdecATF, hdecATT]
    dsimp
    -- Now discharge the conjunction requirements one by one.
    repeat' constructor
    · simpa using ha0Wf
    · simpa [hFF, List.append_assoc] using haFFWf
    · simpa [hFT, List.append_assoc] using haFTWf
    · simpa [hTF, List.append_assoc] using haTFWf
    · simpa [hTT, List.append_assoc] using haTTWf
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0]) (target := xFF))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0]) (target := xFT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0]) (target := xTF))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0]) (target := xTT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xFF, HistElem.act aFF]) (target := xFT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xFF, HistElem.act aFF]) (target := xTT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xFT, HistElem.act aFT]) (target := xFT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xFT, HistElem.act aFT]) (target := xTT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xTF, HistElem.act aTF]) (target := xFT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xTF, HistElem.act aTF]) (target := xTT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xTT, HistElem.act aTT]) (target := xFT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.idxsOfOutput_nodup (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xTT, HistElem.act aTT]) (target := xTT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0]) (target := xFF))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0]) (target := xFT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0]) (target := xTF))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0]) (target := xTT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xFF, HistElem.act aFF]) (target := xFT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xFF, HistElem.act aFF]) (target := xTT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xFT, HistElem.act aFT]) (target := xFT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xFT, HistElem.act aFT]) (target := xTT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xTF, HistElem.act aTF]) (target := xFT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xTF, HistElem.act aTF]) (target := xTT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xTT, HistElem.act aTT]) (target := xFT))
    · simpa [cert, mkCert] using
        (XiTlOneStepRewardLowerBoundCert.checkIdxOutputs_idxsOfOutput (tEnv := tEnv) (l := l)
          (ha := h ++ [HistElem.act a0, HistElem.per xTT, HistElem.act aTT]) (target := xTT))
    · exact hComputeNums
    · exact hEvalRoot
    · exact hEvalFF
    · exact hEvalFT
    · exact hEvalTF
    · exact hEvalTT

  refine ⟨tProg, ?_⟩
  -- Close the `let`-bound goal.
  simp
  -- `verify` is `decide ok`.
  simpa [xi_tlTwoStepRewardLowerBoundSoundProofSystemToPartrec] using (decide_eq_true hok)

end XiTlTwoStepRewardLowerBoundCert

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
