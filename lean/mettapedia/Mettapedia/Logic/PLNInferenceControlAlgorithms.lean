import Mettapedia.Logic.PLNInferenceControlCore

/-!
# Chapter 13 Inference Control: Executable Algorithms

This module adds a verified, simple executable greedy selector over finite premise
pools (`Fact`) and connects it to the Chapter-13 theorem surface.

The algorithm is intentionally minimal:

1. Prefer uncovered dependencies (`a ∈ D ∧ a ∉ S`) when available.
2. Otherwise pick any still-unselected premise (`a ∉ S`).
3. Iterate for `k` steps.

The key output is a theorem-level bridge from the executable selector to the
existing Chapter-13 end-to-end theorem family.
-/

namespace Mettapedia.Logic.PLNInferenceControlAlgorithms

open scoped Classical
open Mettapedia.Logic.PremiseSelection
open Mettapedia.Logic.PremiseSelectionOptimality
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNInferenceControlCore

noncomputable section

/-! ## List helper: first satisfying element -/

def firstWhere? {α : Type*} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x then some x else firstWhere? p xs

lemma firstWhere?_some_mem {α : Type*} {p : α → Bool} {l : List α} {a : α}
    (h : firstWhere? p l = some a) : a ∈ l := by
  induction l with
  | nil =>
      cases h
  | cons x xs ih =>
      by_cases hx : p x
      · simp [firstWhere?, hx] at h
        cases h
        simp
      · simp [firstWhere?, hx] at h
        simp [ih h]

lemma firstWhere?_some_spec {α : Type*} {p : α → Bool} {l : List α} {a : α}
    (h : firstWhere? p l = some a) : p a = true := by
  induction l with
  | nil =>
      cases h
  | cons x xs ih =>
      by_cases hx : p x
      · simp [firstWhere?, hx] at h
        cases h
        simp [hx]
      · simp [firstWhere?, hx] at h
        exact ih h

lemma firstWhere?_none_iff_all_false {α : Type*} {p : α → Bool} {l : List α} :
    firstWhere? p l = none ↔ ∀ x ∈ l, p x = false := by
  induction l with
  | nil =>
      simp [firstWhere?]
  | cons x xs ih =>
      by_cases hx : p x
      · simp [firstWhere?, hx]
      · simp [firstWhere?, hx, ih]

lemma firstWhere?_some_of_exists {α : Type*} {p : α → Bool} {l : List α}
    (hex : ∃ x ∈ l, p x = true) : ∃ a, firstWhere? p l = some a := by
  by_cases hnone : firstWhere? p l = none
  · exfalso
    have hall : ∀ x ∈ l, p x = false :=
      (firstWhere?_none_iff_all_false (p := p) (l := l)).1 hnone
    rcases hex with ⟨x, hx, hpx⟩
    have hfalse : p x = false := hall x hx
    simp [hpx] at hfalse
  · cases hval : firstWhere? p l with
    | none =>
        exact (hnone hval).elim
    | some b =>
        refine ⟨b, ?_⟩
        rfl

/-! ## Executable greedy selector -/

section GreedyAlgorithm

variable {Fact : Type*} [Fintype Fact] [DecidableEq Fact]

def isUncoveredB (D S : Finset Fact) (a : Fact) : Bool :=
  decide (a ∈ D ∧ a ∉ S)

def isAvailableB (S : Finset Fact) (a : Fact) : Bool :=
  decide (a ∉ S)

/-- Greedy candidate picker over the finite universe:
prefer uncovered dependencies, fallback to any available premise. -/
noncomputable def greedyPick? (D S : Finset Fact) : Option Fact :=
  let l := (Finset.univ : Finset Fact).toList
  match firstWhere? (isUncoveredB D S) l with
  | some a => some a
  | none => firstWhere? (isAvailableB S) l

omit [DecidableEq Fact] in
lemma exists_not_mem_of_card_lt_univ (S : Finset Fact)
    (hS : S.card < Fintype.card Fact) :
    ∃ a : Fact, a ∉ S := by
  have hne : S ≠ (Finset.univ : Finset Fact) := by
    intro hEq
    have : S.card = Fintype.card Fact := by simp [hEq]
    exact (Nat.ne_of_lt hS) this
  have hssub : S ⊂ (Finset.univ : Finset Fact) :=
    Finset.ssubset_univ_iff.mpr hne
  rcases Finset.exists_of_ssubset hssub with ⟨a, haU, haS⟩
  exact ⟨a, haS⟩

lemma greedyPick?_some_of_card_lt_univ (D S : Finset Fact)
    (hS : S.card < Fintype.card Fact) :
    ∃ a, greedyPick? D S = some a := by
  classical
  rcases exists_not_mem_of_card_lt_univ (S := S) hS with ⟨a0, ha0S⟩
  have hexAvail :
      ∃ x ∈ (Finset.univ : Finset Fact).toList, isAvailableB S x = true := by
    refine ⟨a0, ?_, ?_⟩
    · exact by simp
    · simp [isAvailableB, ha0S]
  unfold greedyPick?
  by_cases hun :
      ∃ a, firstWhere? (isUncoveredB D S) ((Finset.univ : Finset Fact).toList) = some a
  · rcases hun with ⟨a, ha⟩
    exact ⟨a, by simp [ha]⟩
  · have hnone :
      firstWhere? (isUncoveredB D S) ((Finset.univ : Finset Fact).toList) = none := by
      cases hval : firstWhere? (isUncoveredB D S) ((Finset.univ : Finset Fact).toList) with
      | none => rfl
      | some a =>
          exact (hun ⟨a, hval⟩).elim
    rcases firstWhere?_some_of_exists (p := isAvailableB S)
      (l := (Finset.univ : Finset Fact).toList) hexAvail with ⟨a, ha⟩
    exact ⟨a, by simp [hnone, ha]⟩

lemma greedyPick?_isGreedyStep_of_card_lt_univ (D S : Finset Fact)
    (hS : S.card < Fintype.card Fact) :
    ∃ a, greedyPick? D S = some a ∧ IsGreedyStep D S a := by
  classical
  unfold greedyPick?
  by_cases hsome :
      ∃ a, firstWhere? (isUncoveredB D S) ((Finset.univ : Finset Fact).toList) = some a
  · rcases hsome with ⟨a, ha⟩
    refine ⟨a, ?_, ?_⟩
    · simp [ha]
    · have hmem : a ∈ (Finset.univ : Finset Fact).toList :=
        firstWhere?_some_mem (p := isUncoveredB D S) (l := (Finset.univ : Finset Fact).toList) ha
      have hspec : isUncoveredB D S a = true :=
        firstWhere?_some_spec (p := isUncoveredB D S) (l := (Finset.univ : Finset Fact).toList) ha
      have hDa : a ∈ D ∧ a ∉ S := by
        simpa [isUncoveredB] using hspec
      refine ⟨hDa.2, ?_⟩
      intro b hbS
      have hgainA : dependencyGain D S a = 1 := dependencyGain_eq_one_of_mem hDa.1 hDa.2
      have hgainB : dependencyGain D S b ≤ 1 := dependencyGain_le_one D S b
      simpa [hgainA] using hgainB
  · have hnoneUncovered :
      firstWhere? (isUncoveredB D S) ((Finset.univ : Finset Fact).toList) = none := by
      cases hval : firstWhere? (isUncoveredB D S) ((Finset.univ : Finset Fact).toList) with
      | none => rfl
      | some a =>
          exact (hsome ⟨a, hval⟩).elim
    have hallUncoveredFalse :
        ∀ x ∈ (Finset.univ : Finset Fact).toList, isUncoveredB D S x = false :=
      (firstWhere?_none_iff_all_false
        (p := isUncoveredB D S) (l := (Finset.univ : Finset Fact).toList)).1 hnoneUncovered
    rcases exists_not_mem_of_card_lt_univ (S := S) hS with ⟨a0, ha0S⟩
    have hexAvail :
        ∃ x ∈ (Finset.univ : Finset Fact).toList, isAvailableB S x = true := by
      refine ⟨a0, ?_, ?_⟩
      · exact by simp
      · simp [isAvailableB, ha0S]
    rcases firstWhere?_some_of_exists (p := isAvailableB S)
      (l := (Finset.univ : Finset Fact).toList) hexAvail with ⟨a, ha'⟩
    have ha : greedyPick? D S = some a := by
      simp [greedyPick?, hnoneUncovered, ha']
    refine ⟨a, ha, ?_⟩
    have haAvail : isAvailableB S a = true := by
      have hspecA := firstWhere?_some_spec
        (p := isAvailableB S) (l := (Finset.univ : Finset Fact).toList) ha'
      exact hspecA
    have haNotS : a ∉ S := by simpa [isAvailableB] using haAvail
    have haMem : a ∈ (Finset.univ : Finset Fact).toList := by
      exact firstWhere?_some_mem (p := isAvailableB S) (l := (Finset.univ : Finset Fact).toList) ha'
    have haUncoveredFalse : isUncoveredB D S a = false := hallUncoveredFalse a haMem
    have haNotD : a ∉ D := by
      intro haD
      have htrue : isUncoveredB D S a = true := by simp [isUncoveredB, haD, haNotS]
      simp [htrue] at haUncoveredFalse
    refine ⟨haNotS, ?_⟩
    intro b hbS
    have hbMem : b ∈ (Finset.univ : Finset Fact).toList := by
      exact by simp
    have hbUncoveredFalse : isUncoveredB D S b = false := hallUncoveredFalse b hbMem
    have hbNotD : b ∉ D := by
      intro hbD
      have htrue : isUncoveredB D S b = true := by simp [isUncoveredB, hbD, hbS]
      simp [htrue] at hbUncoveredFalse
    have hgainB0 : dependencyGain D S b = 0 := dependencyGain_eq_zero_of_not_mem hbNotD
    have hgainA0 : dependencyGain D S a = 0 := dependencyGain_eq_zero_of_not_mem haNotD
    simp [hgainA0, hgainB0]

/-- Executable greedy selector for `k` steps. -/
noncomputable def greedySelect (D : Finset Fact) : Nat → Finset Fact
  | 0 => ∅
  | k + 1 =>
      let S := greedySelect D k
      match greedyPick? D S with
      | some a => insert a S
      | none => S

omit [Fintype Fact] in
lemma greedyChain_card_eq_index {D S : Finset Fact} {k : Nat}
    (hchain : GreedyChain D k S) : S.card = k := by
  induction hchain with
  | zero =>
      simp
  | @succ i S a hprev hstep ih =>
      simp [Finset.card_insert_of_notMem hstep.1, ih]

theorem greedySelect_chain_of_le_card (D : Finset Fact) :
    ∀ {k : Nat}, k ≤ Fintype.card Fact → GreedyChain D k (greedySelect D k)
  | 0, _ => by
      simp [greedySelect, GreedyChain.zero]
  | k + 1, hk => by
      let S := greedySelect D k
      have hk' : k ≤ Fintype.card Fact := Nat.le_trans (Nat.le_succ k) hk
      have ih : GreedyChain D k S := by
        simpa [S] using greedySelect_chain_of_le_card (D := D) (k := k) hk'
      have hcardS : S.card = k := greedyChain_card_eq_index ih
      have hklt : k < Fintype.card Fact :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hSlt : S.card < Fintype.card Fact := by simpa [hcardS]
      rcases greedyPick?_isGreedyStep_of_card_lt_univ (D := D) (S := S) hSlt
        with ⟨a, hpick, hstep⟩
      have hsucc : GreedyChain D (k + 1) (insert a S) := GreedyChain.succ ih hstep
      simpa [greedySelect, S, hpick] using hsucc

theorem greedySelect_one_minus_exp_bound_of_le_card (D : Finset Fact) {k : Nat}
    (hk : k ≤ Fintype.card Fact) :
    (1 - Real.exp (-1)) * (Nat.min k D.card : ℝ) ≤ dependencyCoverage D (greedySelect D k) := by
  exact greedyChain_one_minus_exp_bound
    (hG := greedySelect_chain_of_le_card (D := D) (k := k) hk)

/-! ## Chapter-13 algorithmic end-to-end theorem -/

theorem ch13_inferenceControl_end_to_end_algorithmic
    {Goal Bin : Type*}
    (A : PriorNBAssumptionChecklist Goal Fact Bin)
    (η : Fact → ℝ)
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (g : Goal)
    (hLocal : A.localExchangeabilityInBin)
    (δ : Fact → ℝ) (ε : ℝ)
    (hTwoStage :
      BayesOptimalRanking η (ch13ScoreTwoStage globalPrior localPrior likelihood g))
    (hbound : ∀ x, |δ x| ≤ ε)
    (hmargin : ∀ x y, η x < η y →
      ch13ScorePooled globalPrior localPrior likelihood g y
        - ch13ScorePooled globalPrior localPrior likelihood g x > 2 * ε)
    (htie : ∀ x y, η x = η y → δ x = δ y)
    (D : Finset Fact) :
    let G := greedySelect D A.topK
    A.topK ≤ Fintype.card Fact
      ∧ (∀ g' f',
          0 ≤ (selectorDefaults_halfGate Goal Fact).gate g' f'
            ∧ (selectorDefaults_halfGate Goal Fact).gate g' f' ≤ 1)
      ∧ BayesOptimalRanking η
          (perturbedScore (ch13ScorePooled globalPrior localPrior likelihood g) δ)
      ∧ (1 - Real.exp (-1)) * (Nat.min A.topK D.card : ℝ) ≤ dependencyCoverage D G := by
  intro G
  have hGreedy : GreedyChain D A.topK G := by
    simpa [G] using
      (greedySelect_chain_of_le_card (D := D) (k := A.topK) A.topK_le_pool)
  simpa [G] using
    (ch13_inferenceControl_end_to_end
      (A := A) (η := η)
      (globalPrior := globalPrior) (localPrior := localPrior)
      (likelihood := likelihood) (g := g)
      hLocal δ ε hTwoStage hbound hmargin htie
      (D := D) (G := G) hGreedy)

/-! ## Minimal executable fixtures -/

section Fixtures

example :
    dependencyCoverage ({true} : Finset Bool)
      (greedySelect ({true} : Finset Bool) 0) = 0 := by
  simp [greedySelect, dependencyCoverage]

example :
    dependencyCoverage ({true} : Finset Bool)
      (greedySelect ({true} : Finset Bool) 1) = 1 := by
  have hchain :
      GreedyChain ({true} : Finset Bool) 1
        (greedySelect ({true} : Finset Bool) 1) := by
    exact greedySelect_chain_of_le_card (D := ({true} : Finset Bool)) (k := 1) (by decide)
  have hcov :
      dependencyCoverage ({true} : Finset Bool)
        (greedySelect ({true} : Finset Bool) 1)
        = Nat.min 1 ({true} : Finset Bool).card :=
    greedyChain_coverage_eq_min (D := ({true} : Finset Bool))
      (S := greedySelect ({true} : Finset Bool) 1) (i := 1) hchain
  simpa using hcov

end Fixtures

end GreedyAlgorithm

end

end Mettapedia.Logic.PLNInferenceControlAlgorithms
