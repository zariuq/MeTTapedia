import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mettapedia.Logic.MarkovDeFinetti
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti (Recurrence Assumption)

Diaconis–Freedman (1980) show that **Markov exchangeability** alone is not sufficient to
guarantee a mixture-of-Markov-chains representation unless one adds a **recurrence**
assumption (see their condition (4) and Theorem 7).

This file packages a *prefix-measure level* recurrence assumption in a way that can be
used by the hard-direction theorem:

* a prefix measure `μ` is **recurrent** if it extends to a probability measure on infinite
  trajectories and that extension returns to the initial state infinitely often (a.s.).

We also record a concrete counterexample: a deterministic Markov chain that leaves its
initial state once and never returns.  This chain is Markov‑exchangeable but not recurrent.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical
open MeasureTheory

namespace MarkovDeFinettiRecurrence

variable {k : ℕ}

/-! ## Cylinder sets on infinite trajectories -/

/-- Cylinder set for a finite word `xs` in the space of infinite trajectories. -/
def cylinder (xs : List (Fin k)) : Set (ℕ → Fin k) :=
  { ω | ∀ i : Fin xs.length, ω i = xs.get i }

/-! ## Recurrence event -/

/-- Return event at time `n`. -/
def returnEvent (n : ℕ) : Set (ℕ → Fin k) :=
  { ω | ω n = ω 0 }

/-- The event that the trajectory returns to its initial state infinitely often. -/
def recurrentEvent : Set (ℕ → Fin k) :=
  ⋂ N : ℕ, ⋃ n ≥ N, returnEvent (k := k) n

lemma measurable_returnEvent (n : ℕ) : MeasurableSet (returnEvent (k := k) n) := by
  classical
  have hf : Measurable fun ω : ℕ → Fin k => ω n := measurable_pi_apply n
  have hg : Measurable fun ω : ℕ → Fin k => ω 0 := measurable_pi_apply 0
  simpa [returnEvent, Set.setOf_app_iff] using (measurableSet_eq_fun hf hg)

lemma measurable_recurrentEvent : MeasurableSet (recurrentEvent (k := k)) := by
  classical
  unfold recurrentEvent
  refine MeasurableSet.iInter ?_
  intro N
  refine MeasurableSet.iUnion ?_
  intro n
  refine MeasurableSet.iUnion ?_
  intro _hn
  simpa using measurable_returnEvent (k := k) n

/-! ## Recurrence for prefix measures -/

/--
A prefix measure `μ` is **Markov-recurrent** if it extends to a probability measure on
infinite trajectories such that the recurrence event holds almost surely.

This mirrors Diaconis–Freedman’s recurrence condition (4):
`P{ X_n = X_0 for infinitely many n } = 1`.
-/
def MarkovRecurrentPrefixMeasure
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
    (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
    P (recurrentEvent (k := k)) = 1

/-! ## Counterexample: Markov exchangeability does not imply recurrence -/

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinetti

namespace Counterexample

/-- A two‑state chain that moves from 0 to 1 and then stays at 1 forever. -/
noncomputable def transientChain : MarkovChain 2 :=
  { init := fun a => if a = 0 then 1 else 0
    trans := fun _a b => if b = 0 then 0 else 1
    init_sum := by
      classical
      have : (∑ a : Fin 2, if a = 0 then (1 : ENNReal) else 0) = 1 := by
        have h1 : (1 : Fin 2) ≠ 0 := by decide
        simp [h1]
      simpa using this
    trans_sum := by
      intro a
      classical
      have : (∑ b : Fin 2, if b = 0 then (0 : ENNReal) else 1) = 1 := by
        have h1 : (1 : Fin 2) ≠ 0 := by decide
        simp [h1]
      simpa using this }

noncomputable def μ : PrefixMeasure (Fin 2) :=
  (transientChain).prefixMeasure

lemma trans_to_zero (a : Fin 2) : transientChain.trans a 0 = 0 := by
  simp [transientChain]

lemma trans_to_one (a : Fin 2) : transientChain.trans a 1 = 1 := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [transientChain, h]

lemma init_zero : transientChain.init 0 = 1 := by
  simp [transientChain]

lemma init_one : transientChain.init 1 = 0 := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [transientChain, h]

/-- The length-`n+1` word `[0,1,1,...,1]`. -/
def onesPrefix (n : ℕ) : List (Fin 2) :=
  (0 : Fin 2) :: List.replicate n (1 : Fin 2)

lemma get_replicate {α : Type*} (a : α) :
    ∀ {n : ℕ} (i : Fin n), (List.replicate n a).get i = a := by
  intro n i
  induction n with
  | zero =>
      exact (Fin.elim0 i)
  | succ n ih =>
      refine Fin.cases ?h0 ?hsucc i
      · simp [List.replicate, List.get]
      · intro i
        have h := ih i
        simp [List.replicate, List.get, h]

lemma onesPrefix_get_zero (n : ℕ) :
    (onesPrefix n).get ⟨0, by simp [onesPrefix]⟩ = (0 : Fin 2) := by
  simp [onesPrefix, List.get]

lemma onesPrefix_get_succ {n m : ℕ} (hm : m < n) :
    (onesPrefix n).get ⟨m + 1, by simpa [onesPrefix] using Nat.succ_lt_succ hm⟩ = (1 : Fin 2) := by
  have h := get_replicate (a := (1 : Fin 2)) (n := n) (i := ⟨m, hm⟩)
  simp [onesPrefix, List.get, h]

lemma mem_cylinder_onesPrefix (n : ℕ) (ω : ℕ → Fin 2) :
    ω ∈ cylinder (k := 2) (onesPrefix n) ↔
      ω 0 = (0 : Fin 2) ∧ ∀ m : ℕ, 1 ≤ m ∧ m ≤ n → ω m = (1 : Fin 2) := by
  constructor
  · intro h
    have h0 : ω 0 = (0 : Fin 2) := by
      have h0' := h ⟨0, by simp [onesPrefix]⟩
      simpa [onesPrefix, List.get] using h0'
    refine ⟨h0, ?_⟩
    intro m hm
    cases m with
    | zero =>
        cases (Nat.not_succ_le_zero _ hm.1)
    | succ m =>
        have hm' : m < n := Nat.lt_of_succ_le hm.2
        have hmn : ω (m + 1) =
            (onesPrefix n).get ⟨m + 1, by
              simpa [onesPrefix] using Nat.succ_lt_succ hm'⟩ := by
          exact h ⟨m + 1, by simpa [onesPrefix] using Nat.succ_lt_succ hm'⟩
        have hget : (onesPrefix n).get ⟨m + 1, by
              simpa [onesPrefix] using Nat.succ_lt_succ hm'⟩ = (1 : Fin 2) :=
          onesPrefix_get_succ (n := n) (m := m) hm'
        simpa [hget] using hmn
  · rintro ⟨h0, hrest⟩ i
    refine Fin.cases ?hzero ?hsucc i
    · simpa [onesPrefix, List.get] using h0
    · intro j
      have hj1 : (1 : ℕ) ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le _)
      have hjle : j + 1 ≤ n := Nat.succ_le_iff.mp j.isLt
      have hω : ω (j + 1) = (1 : Fin 2) := hrest (j + 1) ⟨hj1, hjle⟩
      have hget : (onesPrefix n).get ⟨j + 1, by
            simpa [onesPrefix] using Nat.succ_lt_succ j.isLt⟩ = (1 : Fin 2) :=
        onesPrefix_get_succ (n := n) (m := j) j.isLt
      simpa [hget] using hω

lemma prefixAux_replicate_one (prev : Fin 2) :
    ∀ n : ℕ, MarkovChain.prefixAux transientChain prev (List.replicate n (1 : Fin 2)) = 1 := by
  intro n
  induction n with
  | zero =>
      simp [MarkovChain.prefixAux]
  | succ n ih =>
      simp [MarkovChain.prefixAux, trans_to_one, ih]

lemma mu_onesPrefix (n : ℕ) : μ (onesPrefix n) = 1 := by
  simp [μ, onesPrefix, MarkovChain.prefixMeasure, MarkovChain.prefixProb, init_zero,
    prefixAux_replicate_one]

/-- The set of paths that start at 0 and are 1 thereafter. -/
def allOnesAfter0 : Set (ℕ → Fin 2) :=
  { ω | ω 0 = (0 : Fin 2) ∧ ∀ n : ℕ, 1 ≤ n → ω n = (1 : Fin 2) }

lemma inter_cylinder_subset_allOnesAfter0 :
    (⋂ n : ℕ, cylinder (k := 2) (onesPrefix n)) ⊆ allOnesAfter0 := by
  intro ω hω
  have h0 : ω 0 = (0 : Fin 2) := by
    have hmem0 := (Set.mem_iInter.mp hω 0)
    have h0' := (mem_cylinder_onesPrefix 0 ω).1 hmem0
    exact h0'.1
  refine ⟨h0, ?_⟩
  intro n hn
  have hmemn := (Set.mem_iInter.mp hω n)
  have hrest := (mem_cylinder_onesPrefix n ω).1 hmemn
  exact hrest.2 n ⟨hn, le_rfl⟩

lemma allOnesAfter0_subset_recurrent_compl :
    allOnesAfter0 ⊆ (recurrentEvent (k := 2))ᶜ := by
  intro ω hω hrec
  have h0 : ω 0 = (0 : Fin 2) := hω.1
  have h1 : ∀ n : ℕ, 1 ≤ n → ω n ≠ ω 0 := by
    intro n hn
    have hn' : ω n = (1 : Fin 2) := hω.2 n hn
    simpa [h0, hn'] using (by decide : (1 : Fin 2) ≠ (0 : Fin 2))
  have hrec1 : ω ∈ ⋃ n ≥ 1, returnEvent (k := 2) n := by
    have := Set.mem_iInter.mp hrec 1
    simpa using this
  rcases Set.mem_iUnion.mp hrec1 with ⟨n, hrecn⟩
  rcases Set.mem_iUnion.mp hrecn with ⟨hn, hmem⟩
  exact (h1 n hn) hmem

lemma not_recurrent :
    ¬ MarkovRecurrentPrefixMeasure (k := 2) μ := by
  intro hrec
  rcases hrec with ⟨P, hP, hμP, hrecP⟩
  let A : ℕ → Set (ℕ → Fin 2) := fun n => cylinder (k := 2) (onesPrefix n)
  have hA_meas : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    have hmeas : MeasurableSet (A n) := by
      unfold A cylinder
      refine MeasurableSet.iInter ?_
      intro i
      have hmeas_eval : Measurable (fun ω : ℕ → Fin 2 => ω i) := measurable_pi_apply i
      have hsingleton : MeasurableSet ({(onesPrefix n).get i} : Set (Fin 2)) :=
        measurableSet_singleton _
      simpa [Set.preimage, Set.setOf_app_iff] using hmeas_eval hsingleton
    exact hmeas.nullMeasurableSet
  have hA_antitone : Antitone A := by
    intro m n hmn ω hω
    have hmn' := (mem_cylinder_onesPrefix n ω).1 hω
    have h0 := hmn'.1
    have hrest := hmn'.2
    refine (mem_cylinder_onesPrefix m ω).2 ⟨h0, ?_⟩
    intro i hi
    exact hrest i ⟨hi.1, le_trans hi.2 hmn⟩
  have hA_one : ∀ n, P (A n) = 1 := by
    intro n
    have hμn : μ (onesPrefix n) = 1 := mu_onesPrefix n
    have hμn' : P (A n) = μ (onesPrefix n) := (hμP (onesPrefix n)).symm
    simpa [A, hμn] using hμn'
  have hfin : ∃ n, P (A n) ≠ ∞ := by
    refine ⟨0, ?_⟩
    have : (P (A 0)) = 1 := hA_one 0
    simpa [this] using (by simp : (1 : ENNReal) ≠ ∞)
  have hinter : P (⋂ n, A n) = 1 := by
    have := (Antitone.measure_iInter (μ := P) hA_antitone hA_meas hfin)
    simpa [hA_one] using this
  have hsubset : (⋂ n, A n) ⊆ allOnesAfter0 :=
    inter_cylinder_subset_allOnesAfter0
  have hsubset' : (⋂ n, A n) ⊆ (recurrentEvent (k := 2))ᶜ :=
    Set.Subset.trans hsubset allOnesAfter0_subset_recurrent_compl
  have hzero : P (recurrentEvent (k := 2)) = 0 := by
    have hmono : P (⋂ n, A n) ≤ P ((recurrentEvent (k := 2))ᶜ) :=
      measure_mono hsubset'
    have hcompl : P ((recurrentEvent (k := 2))ᶜ) = 1 := by
      have := le_trans hmono (by simpa using hP.measure_univ)
      exact le_antisymm this (by simpa using (measure_mono (Set.subset_univ _)))
    have hrec : P (recurrentEvent (k := 2)) = 1 - P ((recurrentEvent (k := 2))ᶜ) := by
      have hmeas : MeasurableSet (recurrentEvent (k := 2)) := measurable_recurrentEvent (k := 2)
      have hfin' : P (recurrentEvent (k := 2)) ≠ ∞ := by
        simpa using (hP.ne_top (recurrentEvent (k := 2)))
      simpa using (measure_compl (μ := P) (s := recurrentEvent (k := 2)) hmeas hfin')
    simpa [hcompl] using hrec
  exact by simpa [hrecP] using hzero

/-- A concrete counterexample showing recurrence is not implied. -/
theorem markov_exchangeable_not_recurrent :
    MarkovExchangeablePrefixMeasure (k := 2) μ ∧ ¬ MarkovRecurrentPrefixMeasure (k := 2) μ := by
  refine ⟨?_, not_recurrent⟩
  simpa [μ] using MarkovDeFinetti.MarkovChain.prefixMeasure_markovExchangeable
    (k := 2) (M := transientChain)

end Counterexample

end MarkovDeFinettiRecurrence

end Mettapedia.Logic
