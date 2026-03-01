import Mathlib.Data.List.OfFn
import Mettapedia.Logic.MarkovExchangeability
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure
import Mettapedia.Logic.UniversalPrediction.MarkovDirichletPredictor
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge

/-!
# Markov Exchangeability Bridge (Domain Test ⇒ Transition-Count Evidence)

This file connects the “domain restriction” notion of **Markov exchangeability** (probabilities
depend only on the initial state and the transition-count matrix) to the concrete
`MarkovDirichletPredictor` infrastructure:

* `Mettapedia.Logic.MarkovExchangeability.evidenceOf` defines the canonical Markov evidence on
  `Fin (n+1) → α` trajectories.
* `Mettapedia.Logic.UniversalPrediction.TransCounts.summary` computes the same transition-count
  evidence for finite words `List (Fin k)` and supports the “append bumps exactly one cell” update
  needed for Markov-Dirichlet predictors.

The main theorem in this file is a “domain test” statement:

> If a prefix-measure environment is Markov-exchangeable, then its 1-step predictions factor
> through the transition-count evidence state (counts + last symbol), as computed by `summary`.

This is the analogue of the i.i.d. “exchangeable ⇒ depends only on counts” theorem used for νPLN,
but for the next tractable restriction (Markov exchangeability).
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators

open Mettapedia.Logic.MarkovExchangeability

namespace MarkovExchangeabilityBridge

open FiniteAlphabet

variable {k : ℕ}

/-! ## Connecting `transCount` to `TransCounts.summary` -/

/-- Transition-count matrix extracted from a `Fin (n+1)` trajectory. -/
def countsOfFn {n : ℕ} (xs : Fin (n + 1) → Fin k) : TransCounts k :=
  ⟨fun a b => transCount (n := n) xs a b⟩

@[simp] theorem countsOfFn_apply {n : ℕ} (xs : Fin (n + 1) → Fin k) (a b : Fin k) :
    (countsOfFn (k := k) xs).counts a b = transCount (n := n) xs a b :=
  rfl

/-- `summary (ofFn xs)` computes the same transition-count matrix as `transCount` on the underlying
trajectory, and returns the last symbol. -/
theorem summary_ofFn {n : ℕ} (xs : Fin (n + 1) → Fin k) :
    TransCounts.summary (k := k) (List.ofFn xs) =
      some (countsOfFn (k := k) xs, xs (Fin.last n)) := by
  classical
  induction n with
  | zero =>
      -- Length-1 words have no transitions.
      have hcounts : countsOfFn (k := k) xs = TransCounts.zero := by
        ext a b
        simp [countsOfFn, TransCounts.zero, transCount]
      -- `List.ofFn xs` is a singleton list, so `summary` returns `(zero, xs 0)`.
      simp [TransCounts.summary, TransCounts.summaryAux, hcounts]
  | succ n ih =>
      -- Split `xs` into the initial segment and the last symbol.
      let xsInit : Fin (n + 1) → Fin k := fun i => xs (Fin.castSucc i)
      let last : Fin k := xs (Fin.last (n + 1))
      have hlist : List.ofFn xs = List.ofFn xsInit ++ [last] := by
        -- `ofFn_succ'` gives a `concat` form; `concat_eq_append` turns it into `++ [last]`.
        rw [List.ofFn_succ' (f := xs)]
        simp [xsInit, last, List.concat_eq_append]
      -- Evaluate the `summary` on `xsInit ++ [last]` using the append lemma.
      have hsumInit :
          TransCounts.summary (k := k) (List.ofFn xsInit) =
            some (countsOfFn (k := k) xsInit, xsInit (Fin.last n)) := by
        simpa [xsInit] using ih (xs := xsInit)
      have hsum :
          TransCounts.summary (k := k) (List.ofFn xsInit ++ [last]) =
            some (TransCounts.bump (countsOfFn (k := k) xsInit) (xsInit (Fin.last n)) last, last) := by
        -- `summary_append_singleton` reduces the summary of an appended list to a bump.
        have hsumInit' :
            TransCounts.summary (k := k) (xsInit 0 :: List.ofFn (fun i => xsInit i.succ)) =
              some (countsOfFn (k := k) xsInit, xsInit (Fin.last n)) := by
          simpa using hsumInit
        have :=
          TransCounts.summary_append_singleton (k := k) (xs := List.ofFn xsInit) (b := last)
        simpa [hsumInit'] using this
      -- Show that bumping agrees with `transCount_snoc` on the underlying trajectory.
      have hsnoc :
          xs = Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xsInit last := by
        funext i
        cases i using Fin.lastCases with
        | last =>
            simp [xsInit, last]
        | cast j =>
            simp [xsInit, last]
      have hbump :
          TransCounts.bump (countsOfFn (k := k) xsInit) (xsInit (Fin.last n)) last =
            countsOfFn (k := k) xs := by
        ext a b
        -- Expand definitions and use `transCount_snoc`.
        have htc :
            transCount (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xsInit last) a b =
              transCount (n := n) xsInit a b +
                (if xsInit (Fin.last n) = a ∧ last = b then 1 else 0) :=
          transCount_snoc (n := n) (xs := xsInit) (x := last) (a := a) (b := b)
        have htc' : transCount (n := n + 1) xs a b =
            transCount (n := n) xsInit a b +
              (if xsInit (Fin.last n) = a ∧ last = b then 1 else 0) := by
          simpa [hsnoc] using htc
        -- The `bump` definition matches the same “add one at exactly (prev,next)” formula.
        by_cases h : a = xsInit (Fin.last n) ∧ b = last
        · have h' : xsInit (Fin.last n) = a ∧ last = b := ⟨h.1.symm, h.2.symm⟩
          have htc'' : transCount (n := n + 1) xs a b = transCount (n := n) xsInit a b + 1 := by
            simpa [h'] using htc'
          -- `bump` increments exactly one cell; `transCount_snoc` increments exactly one transition.
          simpa [countsOfFn, TransCounts.bump, h] using htc''.symm
        · have h' : ¬(xsInit (Fin.last n) = a ∧ last = b) := by
            intro h'
            exact h ⟨h'.1.symm, h'.2.symm⟩
          have htc'' : transCount (n := n + 1) xs a b = transCount (n := n) xsInit a b := by
            simpa [h', Nat.add_zero] using htc'
          simpa [countsOfFn, TransCounts.bump, h] using htc''.symm
      -- Assemble the result.
      calc
        TransCounts.summary (k := k) (List.ofFn xs)
            = TransCounts.summary (k := k) (List.ofFn xsInit ++ [last]) := by
                simpa using congrArg (fun l => TransCounts.summary (k := k) l) hlist
        _ = some (TransCounts.bump (countsOfFn (k := k) xsInit) (xsInit (Fin.last n)) last, last) := hsum
        _ = some (countsOfFn (k := k) xs, xs (Fin.last (n + 1))) := by
              -- Use `hbump` and unfold `last`.
              simp [hbump, last]

/-! ## A prefix-measure notion of Markov exchangeability -/

/-- A `FiniteAlphabet.PrefixMeasure` is Markov-exchangeable if its probabilities for length `n+1`
trajectories depend only on `evidenceOf`. -/
def MarkovExchangeablePrefixMeasure (μ : PrefixMeasure (Fin k)) : Prop :=
  ∀ (n : ℕ) (xs₁ xs₂ : Fin (n + 1) → Fin k),
    evidenceOf (n := n) xs₁ = evidenceOf (n := n) xs₂ →
      μ (List.ofFn xs₁) = μ (List.ofFn xs₂)

/-! ## Domain test: prediction factors through transition-count evidence -/

private lemma evidenceOf_snoc_eq_of_evidenceOf_eq_of_last_eq
    {n : ℕ} (xs₁ xs₂ : Fin (n + 1) → Fin k)
    (he : evidenceOf (n := n) xs₁ = evidenceOf (n := n) xs₂)
    (hlast : xs₁ (Fin.last n) = xs₂ (Fin.last n)) (x : Fin k) :
    evidenceOf (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs₁ x) =
      evidenceOf (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs₂ x) := by
  apply MarkovEvidence.ext
  · -- start
    have hstart : xs₁ 0 = xs₂ 0 := by
      simpa [evidenceOf] using congrArg MarkovEvidence.start he
    simpa [evidenceOf] using hstart
  · -- trans
    funext a b
    -- Use `transCount_snoc` on both sides.
    have htc₁ :
        transCount (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs₁ x) a b =
          transCount (n := n) xs₁ a b + (if xs₁ (Fin.last n) = a ∧ x = b then 1 else 0) :=
      transCount_snoc (n := n) (xs := xs₁) (x := x) (a := a) (b := b)
    have htc₂ :
        transCount (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs₂ x) a b =
          transCount (n := n) xs₂ a b + (if xs₂ (Fin.last n) = a ∧ x = b then 1 else 0) :=
      transCount_snoc (n := n) (xs := xs₂) (x := x) (a := a) (b := b)
    -- Rewrite `transCount (n := n) xs₁ = transCount (n := n) xs₂` from `he`.
    have htrans : transCount (n := n) xs₁ a b = transCount (n := n) xs₂ a b := by
      simpa [evidenceOf] using congrArg (fun e => e.trans a b) he
    -- Use the last-symbol equality to align the indicator terms.
    have hind :
        (if xs₁ (Fin.last n) = a ∧ x = b then 1 else 0) =
          (if xs₂ (Fin.last n) = a ∧ x = b then 1 else 0) := by
      simp [hlast]
    -- Combine.
    calc
      transCount (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs₁ x) a b
          = transCount (n := n) xs₁ a b + (if xs₁ (Fin.last n) = a ∧ x = b then 1 else 0) := htc₁
      _ = transCount (n := n) xs₂ a b + (if xs₂ (Fin.last n) = a ∧ x = b then 1 else 0) := by
          simp [htrans, hind]
      _ = transCount (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs₂ x) a b := by
          simpa using htc₂.symm

/-- If `μ` is Markov-exchangeable, then for any two histories with the same transition-count state
(counts + last symbol, as computed by `summary`), the 1-step extension probabilities agree. -/
theorem mu_append_singleton_eq_of_same_summary
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {n : ℕ} (xs₁ xs₂ : Fin (n + 1) → Fin k)
    (hstart : xs₁ 0 = xs₂ 0)
    (hsum : TransCounts.summary (k := k) (List.ofFn xs₁) = TransCounts.summary (k := k) (List.ofFn xs₂))
    (x : Fin k) :
    μ (List.ofFn xs₁ ++ [x]) = μ (List.ofFn xs₂ ++ [x]) := by
  -- Extract equality of `evidenceOf` and last symbol from `hsum` using `summary_ofFn`.
  have hsum' :
      some (countsOfFn (k := k) xs₁, xs₁ (Fin.last n)) =
        some (countsOfFn (k := k) xs₂, xs₂ (Fin.last n)) := by
    calc
      some (countsOfFn (k := k) xs₁, xs₁ (Fin.last n))
          = TransCounts.summary (k := k) (List.ofFn xs₁) := by
              simpa using (summary_ofFn (k := k) xs₁).symm
      _ = TransCounts.summary (k := k) (List.ofFn xs₂) := hsum
      _ = some (countsOfFn (k := k) xs₂, xs₂ (Fin.last n)) := by
            simpa using (summary_ofFn (k := k) xs₂)
  have hpair :
      (countsOfFn (k := k) xs₁, xs₁ (Fin.last n)) = (countsOfFn (k := k) xs₂, xs₂ (Fin.last n)) :=
    Option.some.inj hsum'
  have hcounts : countsOfFn (k := k) xs₁ = countsOfFn (k := k) xs₂ :=
    congrArg Prod.fst hpair
  have hlast : xs₁ (Fin.last n) = xs₂ (Fin.last n) :=
    congrArg Prod.snd hpair
  -- Build `evidenceOf` equality from `hstart` and `hcounts`.
  have he : evidenceOf (n := n) xs₁ = evidenceOf (n := n) xs₂ := by
    apply MarkovEvidence.ext
    · simp [evidenceOf, hstart]
    · funext a b
      -- `countsOfFn` is defined as `transCount`.
      have : transCount (n := n) xs₁ a b = transCount (n := n) xs₂ a b := by
        simpa [countsOfFn] using congrArg (fun c : TransCounts k => c.counts a b) hcounts
      simpa [evidenceOf] using this
  -- Apply Markov exchangeability at length `n+2` to the `snoc` extensions.
  have he_snoc :
      evidenceOf (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs₁ x) =
        evidenceOf (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs₂ x) :=
    evidenceOf_snoc_eq_of_evidenceOf_eq_of_last_eq (k := k) xs₁ xs₂ he hlast x
  -- Rewrite `List.ofFn (Fin.snoc xs x)` as `List.ofFn xs ++ [x]` and use `hμ`.
  have ofFn_snoc {m : ℕ} (xs : Fin (m + 1) → Fin k) (x : Fin k) :
      List.ofFn (Fin.snoc (α := fun _ : Fin (m + 2) => Fin k) xs x) = List.ofFn xs ++ [x] := by
    rw [List.ofFn_succ' (f := Fin.snoc (α := fun _ : Fin (m + 2) => Fin k) xs x)]
    simp [List.concat_eq_append]
  have hμ' := hμ (n + 1)
    (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs₁ x)
    (Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs₂ x)
    he_snoc
  -- Rewrite the goal to an equality on `Fin.snoc` trajectories, then apply exchangeability.
  rw [← ofFn_snoc (xs := xs₁) (x := x)]
  rw [← ofFn_snoc (xs := xs₂) (x := x)]
  simpa using hμ'

/-- List-level wrapper for `mu_append_singleton_eq_of_same_summary`.

This is the “domain test” in the form most downstream code wants: it talks directly about
`List (Fin k)` histories (not `Fin (n+1)` trajectories). -/
theorem mu_append_singleton_eq_of_same_summary_list
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (xs ys : List (Fin k)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
    (hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
    (hsum : TransCounts.summary (k := k) xs = TransCounts.summary (k := k) ys)
    (x : Fin k) :
    μ (xs ++ [x]) = μ (ys ++ [x]) := by
  classical
  let n : ℕ := xs.length - 1
  have hn : n + 1 = xs.length := by
    have h1 : 1 ≤ xs.length := Nat.succ_le_of_lt hx
    simpa [n] using (Nat.sub_add_cancel h1)
  have hn' : n + 1 = ys.length := by
    simpa [hlen] using hn
  let xsFn : Fin (n + 1) → Fin k := fun i => xs.get (Fin.cast hn i)
  let ysFn : Fin (n + 1) → Fin k := fun i => ys.get (Fin.cast hn' i)
  have hofx : List.ofFn xsFn = xs := by
    have hcongr := (List.ofFn_congr (h := hn) (f := xsFn))
    have hfun : (fun i : Fin xs.length => xsFn (Fin.cast hn.symm i)) = xs.get := by
      funext i
      simp [xsFn]
    calc
      List.ofFn xsFn = List.ofFn (fun i : Fin xs.length => xsFn (Fin.cast hn.symm i)) := hcongr
      _ = List.ofFn xs.get := by simp [hfun]
      _ = xs := by simp
  have hofy : List.ofFn ysFn = ys := by
    have hcongr := (List.ofFn_congr (h := hn') (f := ysFn))
    have hfun : (fun i : Fin ys.length => ysFn (Fin.cast hn'.symm i)) = ys.get := by
      funext i
      simp [ysFn]
    calc
      List.ofFn ysFn = List.ofFn (fun i : Fin ys.length => ysFn (Fin.cast hn'.symm i)) := hcongr
      _ = List.ofFn ys.get := by simp [hfun]
      _ = ys := by simp
  have hstartFn : xsFn 0 = ysFn 0 := by
    simpa [xsFn, ysFn] using hstart
  have hsumFn :
      TransCounts.summary (k := k) (List.ofFn xsFn) =
        TransCounts.summary (k := k) (List.ofFn ysFn) := by
    -- Use `congrArg` on `hofx`/`hofy` (instead of rewriting) to avoid unfolding `List.ofFn`.
    have hx' :
        TransCounts.summary (k := k) (List.ofFn xsFn) = TransCounts.summary (k := k) xs :=
      congrArg (fun l => TransCounts.summary (k := k) l) hofx
    have hy' :
        TransCounts.summary (k := k) (List.ofFn ysFn) = TransCounts.summary (k := k) ys :=
      congrArg (fun l => TransCounts.summary (k := k) l) hofy
    calc
      TransCounts.summary (k := k) (List.ofFn xsFn)
          = TransCounts.summary (k := k) xs := hx'
      _ = TransCounts.summary (k := k) ys := hsum
      _ = TransCounts.summary (k := k) (List.ofFn ysFn) := hy'.symm
  have h :=
    mu_append_singleton_eq_of_same_summary (k := k) (μ := μ) (hμ := hμ)
      (xs₁ := xsFn) (xs₂ := ysFn) (n := n) (hstart := hstartFn) (hsum := hsumFn) (x := x)
  -- Convert back to the original lists without unfolding `List.ofFn`.
  have hx_append : xs ++ [x] = List.ofFn xsFn ++ [x] :=
    congrArg (fun l => l ++ [x]) hofx.symm
  have hy_append : ys ++ [x] = List.ofFn ysFn ++ [x] :=
    congrArg (fun l => l ++ [x]) hofy.symm
  have hμx : μ (xs ++ [x]) = μ (List.ofFn xsFn ++ [x]) := congrArg μ hx_append
  have hμy : μ (ys ++ [x]) = μ (List.ofFn ysFn ++ [x]) := congrArg μ hy_append
  calc
    μ (xs ++ [x]) = μ (List.ofFn xsFn ++ [x]) := hμx
    _ = μ (List.ofFn ysFn ++ [x]) := h
    _ = μ (ys ++ [x]) := hμy.symm

/-- Connection theorem (Markov domain test + Solomonoff-style regret):
for lower-semicomputable Markov-exchangeable prefix measures on `Fin k`,
one-step prediction depends only on Markov transition-count evidence, and the
finite-alphabet universal Solomonoff mixture gives the standard log-loss bound. -/
theorem markovExchangeable_summary_and_solomonoff_regret
    (μ : PrefixMeasure (Fin k))
    (hμMarkov : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hμLSC :
      Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
        (α := Fin k) μ) :
    (∀ (xs ys : List (Fin k)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : TransCounts.summary (k := k) xs = TransCounts.summary (k := k) ys)
      (x : Fin k),
      μ (xs ++ [x]) = μ (ys ++ [x])) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) μ c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
              (α := Fin k)) n ≤
            Real.log (1 / c.toReal)) := by
  refine ⟨?_, ?_⟩
  · intro xs ys hlen hx hstart hsum x
    exact mu_append_singleton_eq_of_same_summary_list
      (k := k) (μ := μ) (hμ := hμMarkov) xs ys hlen hx hstart hsum x
  · intro n
    simpa using
      (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.relEntropy_le_log_inv_M₂
        (α := Fin k) (μ := μ) hμLSC n)

end MarkovExchangeabilityBridge

end Mettapedia.Logic.UniversalPrediction
