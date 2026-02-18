import Mettapedia.Logic.Exchangeability
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.SolomonoffMeasure
import Mettapedia.Logic.SolomonoffPrior
import Mathlib.Data.List.OfFn

/-!
# Solomonoff Induction Restricted to Exchangeable Domains

This file formalizes the **predictor-level** collapse behind νPLN:
Solomonoff-style prediction restricted to an **exchangeable binary** domain factors through
the sufficient statistic `(n⁺, n⁻)` (counts of `true`/`false`).

## The Key Insight

Solomonoff's universal prior M(x) assigns probability to all computable sequences.
When restricted to **exchangeable binary** sequences:

1. Exchangeability implies probabilities depend only on counts (combinatorics).
2. Therefore the Solomonoff-style predictor `μ(x++[b]) / μ(x)` depends only on `(n⁺, n⁻)`.
3. Evidence accumulation is just `hplus` on evidence counts.

Note: The full measure-theoretic de Finetti representation theorem IS formalized in
`Mettapedia.Logic.DeFinetti` (with zero sorries), including the Hausdorff moment theorem.
This file focuses on the semimeasure-level predictor collapse, which is the direct
justification for PLN Evidence.

## Domain Characterization

**Theorem (predictor form)**: For the class of exchangeable binary environments, Solomonoff
prediction collapses from "arbitrary program mixture state" to just `(n⁺, n⁻)` (Evidence).

**Full de Finetti** (proven in `DeFinetti.lean`): Exchangeable ↔ Bernoulli mixture representation.
This gives the closed form of the predictor (Beta-Bernoulli conjugacy).

## References

- [LLM as Solomonoff Approximation](https://arxiv.org/abs/2505.15784) - domain restrictions
- [McCall 2004](https://onlinelibrary.wiley.com/doi/abs/10.1111/j.0026-1386.2004.00190.x) -
  Kolmogorov, Solomonoff, de Finetti connections
- [Diaconis & Freedman 1980](https://projecteuclid.org/journals/annals-of-probability/volume-8/issue-4/Finite-Exchangeable-Sequences/10.1214/aop/1176994663.full) - finite exchangeability

-/

namespace Mettapedia.Logic.SolomonoffExchangeable

open scoped ENNReal

open Mettapedia.Logic.SolomonoffPrior
open Mettapedia.Logic.Exchangeability
open Mettapedia.Logic.EvidenceQuantale

/-! ## Exchangeable Programs -/

section ExchangeablePrograms

/-- A semimeasure on finite strings is *exchangeable* if permuting coordinates of any
    length-`n` Boolean vector does not change the weight assigned to that string. -/
def SemimeasureExchangeable (μ : BinString → ℝ) : Prop :=
  ∀ n : ℕ, ∀ σ : Equiv.Perm (Fin n), ∀ xs : Fin n → Bool,
    μ (List.ofFn xs) = μ (List.ofFn (xs ∘ σ.symm))

/-! ### Basic Consequence: Dependence Only on Counts

The key structural consequence we use from exchangeability is count-invariance: two length-`n`
bitstrings with the same number of `true`s get the same weight.

This is the semimeasure analogue of `Exchangeability.exchangeable_same_counts_same_prob` and is the
exact statement needed for the "sufficient statistics = (n⁺, n⁻)" story at the Solomonoff level.
-/

theorem semimeasureExchangeable_same_counts {μ : BinString → ℝ} (hexch : SemimeasureExchangeable μ)
    {n : ℕ} (xs₁ xs₂ : Fin n → Bool) (hcount : countTrue xs₁ = countTrue xs₂) :
    μ (List.ofFn xs₁) = μ (List.ofFn xs₂) := by
  classical
  obtain ⟨σ, hσ⟩ := same_counts_exists_perm (n := n) xs₁ xs₂ hcount
  -- `hexch` gives invariance under permutation; choose the permutation witnessing `xs₂ = xs₁ ∘ σ`.
  have hperm := hexch n σ.symm xs₁
  -- `hperm : μ(ofFn xs₁) = μ(ofFn (xs₁ ∘ σ))`
  simpa [hσ] using hperm

/-- The cylinder semimeasure induced by a monotone machine and a finite program set
    is exchangeable. This is the semantic notion we need for "exchangeable programs". -/
def ProgramsExchangeable (U : MonotoneMachine) (programs : Finset BinString) : Prop :=
  SemimeasureExchangeable (fun x => U.cylinderMeasure programs x)

/- The class of programs that generate exchangeable binary sequences.

   In this file we avoid a per-program predicate because the current Solomonoff
   development treats exchangeability as a property of the *mixture semimeasure*
   over a program set.
-/
-- NOTE: for the current Solomonoff formalization, exchangeability is a property of the
-- *mixture semimeasure* over a program set, not of a single deterministic program.
-- We therefore work with `ProgramsExchangeable` instead of a per-program predicate.

/- TODO: connect `ProgramsExchangeable` to concrete program classes (e.g. samplers implementing
   i.i.d. Bernoulli, or Beta-Bernoulli mixtures) once a probabilistic program semantics is in place. -/

end ExchangeablePrograms

/-! ## Solomonoff Restricted to Exchangeable Class -/

section RestrictedSolomonoff

/-- A *restricted* Solomonoff-style prior, implemented as the cylinder semimeasure of a
    monotone machine over a finite, prefix-free set of programs.

    Exchangeability is taken to be a property of this induced semimeasure. -/
structure RestrictedSolomonoffPrior where
  U : MonotoneMachine
  programs : Finset BinString
  hpf : PrefixFree (↑programs : Set BinString)
  hexch : ProgramsExchangeable U programs

namespace RestrictedSolomonoffPrior

/-- The induced semimeasure on finite strings (cylinder weights). -/
noncomputable def μ (M : RestrictedSolomonoffPrior) : BinString → ℝ :=
  fun x => M.U.cylinderMeasure M.programs x

/-- Concrete program-mass completeness criterion: selected programs saturate the
Kraft mass exactly (`= 1`). -/
def ProgramMassComplete (M : RestrictedSolomonoffPrior) : Prop :=
  kraftSum M.programs = 1

/-- Program-mass completeness implies normalized root mass for the induced
restricted Solomonoff semimeasure. -/
theorem mu_nil_eq_one_of_programMassComplete
    (M : RestrictedSolomonoffPrior) (hcomplete : ProgramMassComplete M) :
    M.μ [] = 1 := by
  classical
  unfold RestrictedSolomonoffPrior.μ MonotoneMachine.cylinderMeasure
  have hfilter : M.programs.filter (fun p => M.U.produces p []) = M.programs := by
    ext p
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro _
    unfold MonotoneMachine.produces
    intro ⟨i, hi⟩
    simp at hi
  rw [hfilter]
  simpa [ProgramMassComplete, kraftSum] using hcomplete

theorem mu_same_counts (M : RestrictedSolomonoffPrior) {n : ℕ} (xs₁ xs₂ : Fin n → Bool)
    (hcount : countTrue xs₁ = countTrue xs₂) :
    M.μ (List.ofFn xs₁) = M.μ (List.ofFn xs₂) := by
  -- Unfold the induced semimeasure and apply the abstract exchangeability lemma.
  simpa [RestrictedSolomonoffPrior.μ, ProgramsExchangeable] using
    semimeasureExchangeable_same_counts (μ := fun x => M.U.cylinderMeasure M.programs x) M.hexch xs₁ xs₂ hcount

/-! ### Solomonoff-Style Prediction (Semimeasure Level)

The Solomonoff predictor uses the semimeasure ratio `μ(x++[b]) / μ(x)`. This is a *partial*
operation when `μ(x) = 0`, so we model it with `Option`.
-/

/-- Conditional prediction for the next bit under a (possibly defective) semimeasure.

Returns `none` when the conditioning event has weight `0`. -/
noncomputable def predictBit (M : RestrictedSolomonoffPrior) (x : BinString) (b : Bool) : Option ℝ :=
  if M.μ x = 0 then none else some (M.μ (x ++ [b]) / M.μ x)

private lemma countTrue_snoc {n : ℕ} (xs : Fin n → Bool) (b : Bool) :
    countTrue (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs b) =
      countTrue xs + (if b then 1 else 0) := by
  classical
  -- Turn this into a finset-card computation on `Fin (n+1)` and split off the last coordinate.
  unfold countTrue
  let s : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun i : Fin (n + 1) =>
      Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs b i = true)
  let t : Finset (Fin (n + 1)) :=
    (Finset.univ.filter (fun i : Fin n => xs i = true)).map Fin.castSuccEmb
  have hs : s = (if b then insert (Fin.last n) t else t) := by
    ext j
    -- Membership in `s` is just the defining predicate.
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    cases b <;> cases j using Fin.lastCases <;> simp [t]
  have htcard : t.card = (Finset.univ.filter (fun i : Fin n => xs i = true)).card := by
    simp [t]
  cases b with
  | false =>
    -- `s = t` (no new `true` at the end).
    have hst : s = t := by simp [hs]
    change s.card =
      (Finset.univ.filter (fun i : Fin n => xs i = true)).card + (if (false = true) then 1 else 0)
    -- Reduce to `t.card = ...` using `hst`.
    rw [hst]
    simp [htcard]
  | true =>
    -- `s = insert (last n) t`, and `last n ∉ t`.
    have hst : s = insert (Fin.last n) t := by simp [hs]
    change s.card =
      (Finset.univ.filter (fun i : Fin n => xs i = true)).card + (if (true = true) then 1 else 0)
    have hnot : Fin.last n ∉ t := by
      intro hmem
      rcases Finset.mem_map.1 hmem with ⟨i, _hi, hi_last⟩
      have hi_last' := hi_last
      -- Convert `castSuccEmb` to `castSucc` without solving the contradiction automatically.
      -- After simplification this hypothesis becomes `False`, closing the goal.
      simp [Fin.castSuccEmb_apply] at hi_last'
    -- Card adds one for the new `true`.
    rw [hst]
    simp [Finset.card_insert_of_notMem hnot, htcard]

/-- The induced semimeasure depends only on counts (already proven), and therefore so does the
Solomonoff-style predictor `μ(x++[b]) / μ(x)` for any fixed `b`. -/
theorem predictBit_ofFn_same_counts (M : RestrictedSolomonoffPrior) {n : ℕ}
    (xs₁ xs₂ : Fin n → Bool) (hcount : countTrue xs₁ = countTrue xs₂) (b : Bool) :
    M.predictBit (List.ofFn xs₁) b = M.predictBit (List.ofFn xs₂) b := by
  classical
  -- First, the denominators agree by exchangeability.
  have hden :
      M.μ (List.ofFn xs₁) = M.μ (List.ofFn xs₂) :=
    M.mu_same_counts xs₁ xs₂ hcount
  by_cases hzero : M.μ (List.ofFn xs₁) = 0
  · -- Both sides are `none`.
    have hzero₂ : M.μ (List.ofFn xs₂) = 0 := by
      simp [hden] at hzero
      simpa using hzero
    simp [RestrictedSolomonoffPrior.predictBit, hzero, hzero₂]
  · -- Denominators are nonzero, so we reduce to showing the numerators agree.
    have hcount' :
        countTrue (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₁ b) =
          countTrue (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₂ b) := by
      simp [countTrue_snoc, hcount]
    have hnum :
        M.μ (List.ofFn xs₁ ++ [b]) = M.μ (List.ofFn xs₂ ++ [b]) := by
      -- Rewrite `List.ofFn xs ++ [b]` as `List.ofFn (Fin.snoc xs b)`.
      have hsnoc₁ :
          List.ofFn (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₁ b) = List.ofFn xs₁ ++ [b] := by
        -- `ofFn_succ'` gives a `concat` form; `concat_eq_append` turns it into `++ [b]`.
        rw [List.ofFn_succ' (f := Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₁ b)]
        simp [List.concat_eq_append]
      have hsnoc₂ :
          List.ofFn (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₂ b) = List.ofFn xs₂ ++ [b] := by
        rw [List.ofFn_succ' (f := Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₂ b)]
        simp [List.concat_eq_append]
      -- Apply count-invariance at length `n+1`.
      have h :=
        M.mu_same_counts (n := n + 1)
          (xs₁ := Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₁ b)
          (xs₂ := Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₂ b)
          hcount'
      -- Rewrite the `Fin.snoc`-generated lists into `List.ofFn xs ++ [b]` without triggering
      -- simp expansions of `List.ofFn`.
      rw [hsnoc₁, hsnoc₂] at h
      exact h
    -- Finish by unfolding `predictBit`.
    have hzero₂ : M.μ (List.ofFn xs₂) ≠ 0 := by
      simpa [hden] using hzero
    simp [RestrictedSolomonoffPrior.predictBit, hzero₂, hnum, hden]

end RestrictedSolomonoffPrior

/-- **Practical νPLN Theorem**: For exchangeable Solomonoff priors, counts are sufficient.

    Probabilities depend only on (n⁺, n⁻), which follows directly from exchangeability
    via `mu_same_counts`. Note: the full de Finetti theorem IS formalized in
    `Mettapedia.Logic.DeFinetti` and gives the closed-form Beta-Bernoulli representation.

    **This justifies PLN Evidence = (n⁺, n⁻) for exchangeable binary domains.**
-/
theorem solomonoff_exchangeable_counts_sufficient (M : RestrictedSolomonoffPrior) :
    ∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
      countTrue xs₁ = countTrue xs₂ →
      M.μ (List.ofFn xs₁) = M.μ (List.ofFn xs₂) :=
  fun _n xs₁ xs₂ h => M.mu_same_counts xs₁ xs₂ h

/-- **νPLN Core Theorem (Predictor Form)**:

For an exchangeable restricted Solomonoff prior, the Solomonoff-style predictor
`μ(x++[b]) / μ(x)` depends only on the count statistic `(n⁺, n⁻)` of the observed prefix.

This is the precise “domain restriction ⇒ state compression” statement:
exchangeability collapses the relevant state from “program mixture” to `ℕ × ℕ`. -/
theorem solomonoff_exchangeable_predictBit_same_counts (M : RestrictedSolomonoffPrior) :
    ∀ {n : ℕ} (xs₁ xs₂ : Fin n → Bool),
      countTrue xs₁ = countTrue xs₂ →
      ∀ b : Bool,
        M.predictBit (List.ofFn xs₁) b = M.predictBit (List.ofFn xs₂) b := by
  intro n xs₁ xs₂ hcount b
  exact Mettapedia.Logic.SolomonoffExchangeable.RestrictedSolomonoffPrior.predictBit_ofFn_same_counts
    (M := M) xs₁ xs₂ hcount b

/-! ### Evidence View: Count Update = `hplus`

The Evidence quantale uses `hplus` to aggregate independent observations:
adding one `true` increments `n⁺`; adding one `false` increments `n⁻`.
-/

/-- Convert natural count statistics to Evidence counts. -/
def evidenceOfCounts (n_pos n_neg : ℕ) : Evidence :=
  ⟨(n_pos : ℝ≥0∞), (n_neg : ℝ≥0∞)⟩

/-- Evidence contributed by a single observation bit. -/
def evidenceOfBit (b : Bool) : Evidence :=
  if b then ⟨1, 0⟩ else ⟨0, 1⟩

/-- Evidence corresponding to a length-`n` observation vector. -/
def evidenceOfFn {n : ℕ} (xs : Fin n → Bool) : Evidence :=
  evidenceOfCounts (countTrue xs) (countFalse xs)

/-- `evidenceOfFn xs` is equivalent to knowing only `countTrue xs` (since `countFalse` is determined
by `count_partition`). -/
theorem evidenceOfFn_eq_iff_countTrue_eq {n : ℕ} (xs₁ xs₂ : Fin n → Bool) :
    evidenceOfFn xs₁ = evidenceOfFn xs₂ ↔ countTrue xs₁ = countTrue xs₂ := by
  constructor
  · intro heq
    have hpos :
        ((countTrue xs₁ : ℕ) : ℝ≥0∞) = ((countTrue xs₂ : ℕ) : ℝ≥0∞) := by
      simpa [evidenceOfFn, evidenceOfCounts] using congrArg Evidence.pos heq
    exact Nat.cast_injective hpos
  · intro hcount
    have hfalse : countFalse xs₁ = countFalse xs₂ := by
      -- Use `countTrue + countFalse = n` on both sides.
      have hpart₁ := count_partition (n := n) xs₁
      have hpart₂ := count_partition (n := n) xs₂
      have hsum : countTrue xs₁ + countFalse xs₁ = countTrue xs₂ + countFalse xs₂ := by
        calc
          countTrue xs₁ + countFalse xs₁ = n := hpart₁
          _ = countTrue xs₂ + countFalse xs₂ := hpart₂.symm
      -- Cancel the `countTrue` terms using `hcount`.
      have hsum' : countTrue xs₁ + countFalse xs₁ = countTrue xs₁ + countFalse xs₂ := by
        simpa [hcount] using hsum
      exact Nat.add_left_cancel hsum'
    ext <;> simp [evidenceOfFn, evidenceOfCounts, hcount, hfalse]

/-- **νPLN core (Evidence form)**: For an exchangeable restricted Solomonoff prior, the
Solomonoff-style predictor depends only on the Evidence state `evidenceOfFn xs`.

This is the clean “state compression” statement: in the exchangeable-binary setting, the
predictor factors through the sufficient statistic `(n⁺, n⁻)`. -/
theorem solomonoff_exchangeable_predictBit_same_evidence (M : RestrictedSolomonoffPrior) :
    ∀ {n : ℕ} (xs₁ xs₂ : Fin n → Bool),
      evidenceOfFn xs₁ = evidenceOfFn xs₂ →
      ∀ b : Bool,
        M.predictBit (List.ofFn xs₁) b = M.predictBit (List.ofFn xs₂) b := by
  intro n xs₁ xs₂ heq b
  -- Extract equality of `countTrue` from the equality of Evidence states.
  have hpos :
      ((countTrue xs₁ : ℕ) : ℝ≥0∞) = ((countTrue xs₂ : ℕ) : ℝ≥0∞) := by
    simpa [evidenceOfFn, evidenceOfCounts] using congrArg Evidence.pos heq
  have hcount : countTrue xs₁ = countTrue xs₂ := by
    exact Nat.cast_injective hpos
  exact solomonoff_exchangeable_predictBit_same_counts (M := M) xs₁ xs₂ hcount b

/-- Bridge theorem from semimeasure-level exchangeability to measure-level
infinite exchangeability.

If a probability measure on infinite binary sequences has the same finite-prefix
laws as a `RestrictedSolomonoffPrior`, then the coordinate process is
`InfiniteExchangeable` under that measure. -/
theorem restrictedSolomonoff_infiniteExchangeable_of_prefixLaw
    (M : RestrictedSolomonoffPrior)
    (μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString)
    (hμprob : MeasureTheory.IsProbabilityMeasure μ)
    (hprefix :
      ∀ (n : ℕ) (xs : Fin n → Bool),
        μ {ω | ∀ i : Fin n, ω i = xs i} =
          ENNReal.ofReal (M.μ (List.ofFn xs))) :
    InfiniteExchangeable (fun i ω => ω i) μ := by
  letI : MeasureTheory.IsProbabilityMeasure μ := hμprob
  refine ⟨?_⟩
  intro n
  refine ⟨?_⟩
  intro σ vals
  have hvals :
      μ {ω | ∀ i : Fin n, ω i = vals i} =
        ENNReal.ofReal (M.μ (List.ofFn vals)) := hprefix n vals
  have hpermVals :
      μ {ω | ∀ i : Fin n, ω i = vals (σ.symm i)} =
        ENNReal.ofReal (M.μ (List.ofFn (vals ∘ σ.symm))) := hprefix n (vals ∘ σ.symm)
  have hμ :
      M.μ (List.ofFn vals) = M.μ (List.ofFn (vals ∘ σ.symm)) := by
    simpa [RestrictedSolomonoffPrior.μ, ProgramsExchangeable] using M.hexch n σ vals
  have hreindex :
      μ {ω | ∀ i : Fin n, ω (σ i) = vals i} =
        μ {ω | ∀ i : Fin n, ω i = vals (σ.symm i)} := by
    congr 1
    ext ω
    constructor <;> intro h i
    · simpa using h (σ.symm i)
    · simpa using h (σ i)
  calc
    μ {ω | ∀ i : Fin n, ω i = vals i}
        = ENNReal.ofReal (M.μ (List.ofFn vals)) := hvals
    _ = ENNReal.ofReal (M.μ (List.ofFn (vals ∘ σ.symm))) := by simp [hμ]
    _ = μ {ω | ∀ i : Fin n, ω i = vals (σ.symm i)} := by simpa using hpermVals.symm
    _ = μ {ω | ∀ i : Fin n, ω (σ i) = vals i} := hreindex.symm

/-- One-hop version of the Solomonoff→exchangeability bridge using the named
no-leakage cylinder-law condition from `SolomonoffMeasure`, so no external
`hprefix` argument is required. -/
theorem restrictedSolomonoff_infiniteExchangeable_of_noLeakageAtCylindersLaw
    (M : RestrictedSolomonoffPrior)
    (μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString)
    (hμprob : MeasureTheory.IsProbabilityMeasure μ)
    (hNoLeak :
      Mettapedia.Logic.NoLeakageAtCylindersLaw (U := M.U) (programs := M.programs) μ) :
    InfiniteExchangeable (fun i ω => ω i) μ := by
  refine restrictedSolomonoff_infiniteExchangeable_of_prefixLaw
    (M := M) (μ := μ) (hμprob := hμprob) ?_
  exact Mettapedia.Logic.hprefix_of_noLeakageAtCylindersLaw
    (U := M.U) (programs := M.programs) (μ := μ) hNoLeak

/-- One-hop concrete criterion packaged without external witnesses:
if selected programs emit at every depth and root mass is normalized, then the
canonical machine-induced measure is probability and infinite-exchangeable. -/
theorem restrictedSolomonoff_infiniteExchangeable_exists_of_totalOutputOnPrograms
    (M : RestrictedSolomonoffPrior)
    (htot : Mettapedia.Logic.TotalOutputOnPrograms M.U M.programs)
    (hroot : M.μ [] = 1) :
    ∃ μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString,
      ∃ hμprob : MeasureTheory.IsProbabilityMeasure μ,
        μ = Mettapedia.Logic.totalOutputProgramMeasure
          (U := M.U) (programs := M.programs) htot ∧
        @InfiniteExchangeable _ _ (fun i ω => ω i) μ hμprob := by
  let μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString :=
    Mettapedia.Logic.totalOutputProgramMeasure (U := M.U) (programs := M.programs) htot
  have hμprob : MeasureTheory.IsProbabilityMeasure μ := by
    simpa [μ, RestrictedSolomonoffPrior.μ] using
      (Mettapedia.Logic.isProbabilityMeasure_totalOutputProgramMeasure_of_root_one
        (U := M.U) (programs := M.programs) (htot := htot) hroot)
  letI : MeasureTheory.IsProbabilityMeasure μ := hμprob
  have hNoLeak :
      Mettapedia.Logic.NoLeakageAtCylindersLaw (U := M.U) (programs := M.programs) μ := by
    simpa [μ] using
      (Mettapedia.Logic.noLeakageAtCylindersLaw_totalOutputProgramMeasure
        (U := M.U) (programs := M.programs) htot)
  refine ⟨μ, hμprob, rfl, ?_⟩
  exact restrictedSolomonoff_infiniteExchangeable_of_noLeakageAtCylindersLaw
    (M := M) (μ := μ) (hμprob := hμprob) hNoLeak

/-- One-hop concrete criterion with no explicit `hroot` argument:
derive normalization from `ProgramMassComplete` and then apply the
total-output route. -/
theorem restrictedSolomonoff_infiniteExchangeable_exists_of_totalOutputOnPrograms_and_programMassComplete
    (M : RestrictedSolomonoffPrior)
    (htot : Mettapedia.Logic.TotalOutputOnPrograms M.U M.programs)
    (hcomplete : RestrictedSolomonoffPrior.ProgramMassComplete M) :
    ∃ μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString,
      ∃ hμprob : MeasureTheory.IsProbabilityMeasure μ,
        μ = Mettapedia.Logic.totalOutputProgramMeasure
          (U := M.U) (programs := M.programs) htot ∧
        @InfiniteExchangeable _ _ (fun i ω => ω i) μ hμprob := by
  exact restrictedSolomonoff_infiniteExchangeable_exists_of_totalOutputOnPrograms
    (M := M) (htot := htot)
    (hroot := RestrictedSolomonoffPrior.mu_nil_eq_one_of_programMassComplete
      (M := M) hcomplete)

/-- Deprecated entrypoint: use
`restrictedSolomonoff_infiniteExchangeable_of_noLeakageAtCylindersLaw`
or the concrete
`restrictedSolomonoff_infiniteExchangeable_exists_of_totalOutputOnPrograms_and_programMassComplete`. -/
theorem restrictedSolomonoff_infiniteExchangeable_of_cylinderLaw
    (M : RestrictedSolomonoffPrior)
    (μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString)
    (hμprob : MeasureTheory.IsProbabilityMeasure μ)
    (hCylinder :
      ∀ x : BinString,
        μ (Mettapedia.Logic.SolomonoffPrior.InfBinString.Cylinder x) =
          ENNReal.ofReal (M.μ x)) :
    InfiniteExchangeable (fun i ω => ω i) μ :=
  restrictedSolomonoff_infiniteExchangeable_of_noLeakageAtCylindersLaw
    (M := M) (μ := μ) (hμprob := hμprob) hCylinder

theorem evidenceOfFn_snoc {n : ℕ} (xs : Fin n → Bool) (b : Bool) :
    evidenceOfFn (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs b) =
      evidenceOfFn xs + evidenceOfBit b := by
  classical
  -- Unfold and compute the count updates.
  cases b with
  | false =>
    unfold evidenceOfFn evidenceOfCounts evidenceOfBit
    have htrue :
        countTrue (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false) = countTrue xs := by
      simpa using (RestrictedSolomonoffPrior.countTrue_snoc (xs := xs) (b := false))
    have hfalse :
        countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false) = countFalse xs + 1 := by
      have hpart₁ := count_partition (n := n) xs
      have hpart₂ :=
        count_partition (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false)
      have hpart₂' :
          countTrue xs +
              countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false) =
            n + 1 := by
        simpa [htrue] using hpart₂
      have hpart₁' : countTrue xs + (countFalse xs + 1) = n + 1 := by
        simpa [Nat.add_assoc] using congrArg (fun t => t + 1) hpart₁
      have heq :
          countTrue xs +
              countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false) =
            countTrue xs + (countFalse xs + 1) := by
        calc
          countTrue xs +
                countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false) =
              n + 1 := hpart₂'
          _ = countTrue xs + (countFalse xs + 1) := by
              simpa using hpart₁'.symm
      exact Nat.add_left_cancel heq
    ext <;> simp [Evidence.hplus_def, htrue, hfalse, Nat.cast_add]
  | true =>
    unfold evidenceOfFn evidenceOfCounts evidenceOfBit
    have htrue :
        countTrue (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true) = countTrue xs + 1 := by
      simpa using (RestrictedSolomonoffPrior.countTrue_snoc (xs := xs) (b := true))
    have hfalse :
        countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true) = countFalse xs := by
      have hpart₁ := count_partition (n := n) xs
      have hpart₂ :=
        count_partition (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true)
      have hpart₂' : (countTrue xs + 1) +
            countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true) =
          n + 1 := by
        simpa [htrue, Nat.add_assoc] using hpart₂
      have hpart₁' : (countTrue xs + 1) + countFalse xs = n + 1 := by
        -- Add one to the count partition equation and reassociate to match the LHS of `hpart₂'`.
        have h1 : (countTrue xs + countFalse xs) + 1 = n + 1 :=
          congrArg (fun t => t + 1) hpart₁
        -- Reassociate and commute to put the `+ 1` next to `countTrue xs`.
        have h2 : countTrue xs + countFalse xs + 1 = n + 1 := by
          simpa [Nat.add_assoc] using h1
        have h3 : countTrue xs + 1 + countFalse xs = n + 1 := by
          simpa [Nat.add_right_comm] using h2
        simpa [Nat.add_assoc] using h3
      have heq :
          (countTrue xs + 1) +
              countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true) =
            (countTrue xs + 1) + countFalse xs := by
        calc
          (countTrue xs + 1) +
                countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true) =
              n + 1 := hpart₂'
          _ = (countTrue xs + 1) + countFalse xs := by
              simpa using hpart₁'.symm
      exact Nat.add_left_cancel heq
    ext <;> simp [Evidence.hplus_def, htrue, hfalse, Nat.cast_add]

end RestrictedSolomonoff

/-! ## The Domain Characterization Theorem -/

section DomainCharacterization

/- TODO: Domain characterization narrative.

   This section should eventually contain *precise* theorems stating:
   - when the (counts-only) Evidence/Beta update is optimal (exchangeable binary),
   - when it is not (non-exchangeable / correlated / non-binary),
   - and simple diagnostic conditions/tests that detect departures from exchangeability.
-/

end DomainCharacterization

/-! ## The νPLN Story -/

section NuPLN

/- TODO: νPLN main theorem.

   Once the Solomonoff→BernoulliMixture bridge is formalized, add a theorem that makes the
   restriction-to-exchangeable-domain statement precise.
-/

end NuPLN

/-! ## Computational Aspects -/

section Computational

/- TODO: computational statements (tractability, relation to LLM approximations).

   These should be written as prose, or as precise complexity statements once we have an
   explicit computational model for the restricted inference.
-/

end Computational

end Mettapedia.Logic.SolomonoffExchangeable
