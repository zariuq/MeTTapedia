import Algorithms.Quantitative.FiniteL1RatChecker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

namespace Mettapedia.Algorithms

open scoped BigOperators

section FiniteL1

variable {α : Type*}

/-- Finset-facing wrapper for the pure list-based rational `L1` checker kernel. -/
def finiteL1Rat (s : Finset α) (f g : α → ℚ) : ℚ :=
  ∑ x ∈ s, Algorithms.Quantitative.ratAbs (f x - g x)

lemma finiteL1Rat_eq_list (s : Finset α) (f g : α → ℚ) :
    finiteL1Rat s f g = Algorithms.Quantitative.finiteL1RatList s.toList f g := by
  classical
  unfold finiteL1Rat Algorithms.Quantitative.finiteL1RatList
  simp only [Finset.sum_eq_multiset_sum]
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]

/-- Finset wrapper for the pure checker. -/
noncomputable def finiteL1LeChecker (s : Finset α) (f g : α → ℚ) (C : ℚ) : Bool :=
  Algorithms.Quantitative.finiteL1LeCheckerList s.toList f g C

theorem finiteL1Le_of_checker_true
    {s : Finset α} {f g : α → ℚ} {C : ℚ}
    (h : finiteL1LeChecker s f g C = true) :
    finiteL1Rat s f g ≤ C := by
  have hlist :
      Algorithms.Quantitative.finiteL1RatList s.toList f g ≤ C :=
    Algorithms.Quantitative.finiteL1LeList_of_checker_true
      (xs := s.toList) (f := f) (g := g) (C := C) h
  simpa [finiteL1Rat_eq_list (s := s) (f := f) (g := g)] using hlist

theorem not_finiteL1Le_of_checker_false
    {s : Finset α} {f g : α → ℚ} {C : ℚ}
    (h : finiteL1LeChecker s f g C = false) :
    ¬ finiteL1Rat s f g ≤ C := by
  have hlist :
      ¬ Algorithms.Quantitative.finiteL1RatList s.toList f g ≤ C :=
    Algorithms.Quantitative.not_finiteL1LeList_of_checker_false
      (xs := s.toList) (f := f) (g := g) (C := C) h
  simpa [finiteL1Rat_eq_list (s := s) (f := f) (g := g)] using hlist

/-- Finset wrapper for the pure rate checker. -/
noncomputable def finiteL1RateChecker (s : Finset α) (f g : α → ℚ) (C R : ℚ) : Bool :=
  Algorithms.Quantitative.finiteL1RateCheckerList s.toList f g C R

theorem finiteL1Rate_of_checker_true
    {s : Finset α} {f g : α → ℚ} {C R : ℚ}
    (h : finiteL1RateChecker s f g C R = true) :
    0 < R ∧ finiteL1Rat s f g ≤ C / R := by
  rcases Algorithms.Quantitative.finiteL1RateList_of_checker_true
    (xs := s.toList) (f := f) (g := g) (C := C) (R := R) h with ⟨hR, hlist⟩
  refine ⟨hR, ?_⟩
  simpa [finiteL1Rat_eq_list (s := s) (f := f) (g := g)] using hlist

theorem not_finiteL1Rate_of_checker_false
    {s : Finset α} {f g : α → ℚ} {C R : ℚ}
    (h : finiteL1RateChecker s f g C R = false) :
    ¬ (0 < R ∧ finiteL1Rat s f g ≤ C / R) := by
  intro hrate
  have hlist : 0 < R ∧ Algorithms.Quantitative.finiteL1RatList s.toList f g ≤ C / R := by
    refine ⟨hrate.1, ?_⟩
    simpa [finiteL1Rat_eq_list (s := s) (f := f) (g := g)] using hrate.2
  exact (Algorithms.Quantitative.not_finiteL1RateList_of_checker_false
      (xs := s.toList) (f := f) (g := g) (C := C) (R := R) h) hlist

lemma ratAbs_cast (q : ℚ) :
    ((Algorithms.Quantitative.ratAbs q : ℚ) : ℝ) = |(q : ℝ)| := by
  by_cases hq : q < 0
  · have hqR : (q : ℝ) < 0 := by exact_mod_cast hq
    simp [Algorithms.Quantitative.ratAbs, hq, abs_of_neg hqR]
  · have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast (le_of_not_gt hq)
    simp [Algorithms.Quantitative.ratAbs, hq, abs_of_nonneg hqR]

/-- Real-valued lift for finite-support rational certificates. -/
theorem finiteL1RateReal_of_checker_true
    {s : Finset α} {f g : α → ℚ} {fr gr : α → ℝ} {C R : ℚ}
    (hcheck : finiteL1RateChecker s f g C R = true)
    (hfr : ∀ x, x ∈ s → fr x = (f x : ℝ))
    (hgr : ∀ x, x ∈ s → gr x = (g x : ℝ)) :
    (∑ x ∈ s, |fr x - gr x|) ≤ (C : ℝ) / R := by
  have ratCast_sum (t : Finset α) (h : α → ℚ) :
      ((∑ x ∈ t, h x : ℚ) : ℝ) = ∑ x ∈ t, ((h x : ℚ) : ℝ) := by
    classical
    refine Finset.induction_on t ?base ?step
    · simp
    · intro a t hat ih
      simp [hat, ih]
  rcases finiteL1Rate_of_checker_true (s := s) (f := f) (g := g) (C := C) (R := R) hcheck with
    ⟨_, hboundQ⟩
  have hsumCast :
      (∑ x ∈ s, |fr x - gr x|) = (finiteL1Rat s f g : ℝ) := by
    classical
    calc
      (∑ x ∈ s, |fr x - gr x|) = ∑ x ∈ s, |((f x : ℚ) : ℝ) - ((g x : ℚ) : ℝ)| := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simp [hfr x hx, hgr x hx]
      _ = ∑ x ∈ s, (((Algorithms.Quantitative.ratAbs (f x - g x)) : ℚ) : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simp [ratAbs_cast, Rat.cast_sub]
      _ = (finiteL1Rat s f g : ℝ) := by
        simpa [finiteL1Rat] using
          (ratCast_sum s (fun x => Algorithms.Quantitative.ratAbs (f x - g x))).symm
  have hboundR : (finiteL1Rat s f g : ℝ) ≤ (C : ℝ) / R := by
    exact_mod_cast hboundQ
  calc
    (∑ x ∈ s, |fr x - gr x|) = (finiteL1Rat s f g : ℝ) := hsumCast
    _ ≤ (C : ℝ) / R := hboundR

/-- HardBEST-facing adapter:
if per-pattern real WR/WOR masses are represented by rational certificate functions and
the finite rate checker succeeds, then the exact WR/WOR finite-pattern inequality holds. -/
theorem hardBEST_patternRateBound_of_checker_true
    {β : Type*} (patternSet : Finset β)
    (wrMass worMass : β → ℝ)
    (f g : β → ℚ) (C : ℚ) (R : ℕ)
    (hwr : ∀ p, p ∈ patternSet → wrMass p = (f p : ℝ))
    (hwor : ∀ p, p ∈ patternSet → worMass p = (g p : ℝ))
    (hcheck : finiteL1RateChecker patternSet f g C (R : ℚ) = true) :
    (∑ p ∈ patternSet, |wrMass p - worMass p|) ≤ (C : ℝ) / (R : ℝ) := by
  simpa using
    (finiteL1RateReal_of_checker_true
      (s := patternSet) (f := f) (g := g)
      (fr := wrMass) (gr := worMass)
      (C := C) (R := (R : ℚ)) hcheck hwr hwor)

/-- Existential-certificate form of `hardBEST_patternRateBound_of_checker_true`. -/
theorem hardBEST_patternRateBound_of_exists_certificate
    {β : Type*} (patternSet : Finset β)
    (wrMass worMass : β → ℝ)
    (C : ℚ) (R : ℕ)
    (hcert :
      ∃ f g : β → ℚ,
        (∀ p, p ∈ patternSet → wrMass p = (f p : ℝ)) ∧
        (∀ p, p ∈ patternSet → worMass p = (g p : ℝ)) ∧
        finiteL1RateChecker patternSet f g C (R : ℚ) = true) :
    (∑ p ∈ patternSet, |wrMass p - worMass p|) ≤ (C : ℝ) / (R : ℝ) := by
  rcases hcert with ⟨f, g, hwr, hwor, hcheck⟩
  exact hardBEST_patternRateBound_of_checker_true
    (patternSet := patternSet) (wrMass := wrMass) (worMass := worMass)
    (f := f) (g := g) (C := C) (R := R) hwr hwor hcheck

section Smoke

private def smokePatternSet : Finset (Fin 1) := {0}
private def smokeF : Fin 1 → ℚ := fun _ => (1 / 3 : ℚ)
private def smokeG : Fin 1 → ℚ := fun _ => (1 / 3 : ℚ)
private def smokeBadF : Fin 1 → ℚ := fun _ => (1 : ℚ)
private def smokeBadG : Fin 1 → ℚ := fun _ => (0 : ℚ)
private def smokeWrMass : Fin 1 → ℝ := fun p => (smokeF p : ℝ)
private def smokeWorMass : Fin 1 → ℝ := fun p => (smokeG p : ℝ)

private lemma smoke_hcheck_true :
    finiteL1RateChecker smokePatternSet smokeF smokeG 0 (1 : ℚ) = true := by
  unfold finiteL1RateChecker Algorithms.Quantitative.finiteL1RateCheckerList
  refine Algorithms.Quantitative.checker_true_of_prop ?_
  constructor
  · norm_num
  · simp [Algorithms.Quantitative.finiteL1RatList, Algorithms.Quantitative.ratAbs, smokePatternSet, smokeF, smokeG]

private lemma smoke_hcheck_false :
    finiteL1RateChecker smokePatternSet smokeBadF smokeBadG 0 (1 : ℚ) = false := by
  unfold finiteL1RateChecker Algorithms.Quantitative.finiteL1RateCheckerList
  refine Algorithms.Quantitative.checker_false_of_not_prop ?_
  intro h
  rcases h with ⟨_, hle⟩
  have hsum :
      Algorithms.Quantitative.finiteL1RatList smokePatternSet.toList smokeBadF smokeBadG = 1 := by
    simp [Algorithms.Quantitative.finiteL1RatList, Algorithms.Quantitative.ratAbs,
      smokePatternSet, smokeBadF, smokeBadG]
  have : (1 : ℚ) ≤ 0 := by simpa [hsum] using hle
  exact (by norm_num : ¬ ((1 : ℚ) ≤ 0)) this

/-- Minimal positive smoke check:
exact-match rational certificates imply the WR/WOR finite-pattern inequality. -/
theorem hardBEST_patternRateBound_smoke_singleton :
    (∑ p ∈ smokePatternSet, |smokeWrMass p - smokeWorMass p|) ≤ (0 : ℝ) / (1 : ℝ) := by
  have hcert :
      ∃ f g : Fin 1 → ℚ,
        (∀ p, p ∈ smokePatternSet → smokeWrMass p = (f p : ℝ)) ∧
        (∀ p, p ∈ smokePatternSet → smokeWorMass p = (g p : ℝ)) ∧
        finiteL1RateChecker smokePatternSet f g 0 (1 : ℚ) = true := by
    refine ⟨smokeF, smokeG, ?_, ?_, ?_⟩
    · intro p hp
      simp [smokeWrMass, smokeF]
    · intro p hp
      simp [smokeWorMass, smokeG]
    · simpa using smoke_hcheck_true
  simpa using
    (hardBEST_patternRateBound_of_exists_certificate
      (patternSet := smokePatternSet) (wrMass := smokeWrMass) (worMass := smokeWorMass)
      (C := 0) (R := 1) hcert)

/-- Minimal negative smoke check:
if checker fails, the corresponding finite rational rate statement is false. -/
theorem hardBEST_patternRateBound_smoke_singleton_negative :
    ¬ (0 < (1 : ℚ) ∧ finiteL1Rat smokePatternSet smokeBadF smokeBadG ≤ (0 : ℚ) / (1 : ℚ)) := by
  exact not_finiteL1Rate_of_checker_false
    (s := smokePatternSet) (f := smokeBadF) (g := smokeBadG) (C := 0) (R := (1 : ℚ))
    smoke_hcheck_false

end Smoke

end FiniteL1

end Mettapedia.Algorithms
