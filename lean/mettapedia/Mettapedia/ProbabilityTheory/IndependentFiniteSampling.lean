import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Independent finite sampling

Finite product distributions, real-valued expectations, and the distinction
between independence at a fixed environment and dependence after mixing over a
shared environment. The probability objects are Mathlib `PMF`s; finite sums are
used only to expose formulas useful for executable batch implementations.
-/

namespace Mettapedia.ProbabilityTheory.IndependentFiniteSampling

open scoped BigOperators ENNReal NNReal

noncomputable section

variable {A B I : Type*}

/-- Normalize frozen nonnegative weights. A zero total means no enabled
outcome, represented explicitly by `none`. -/
def weightedChoice [Fintype A] (weights : A → ℝ≥0) : PMF (Option A) :=
  if h : ∑ a, weights a = 0 then PMF.pure none
  else
    (PMF.normalize (fun a => (weights a : ℝ≥0∞))
      (by
        rw [tsum_fintype, ← ENNReal.ofNNReal_finsetSum]
        exact fun hz => h (ENNReal.coe_eq_zero.mp hz))
      (by
        rw [tsum_fintype, ← ENNReal.ofNNReal_finsetSum]
        exact ENNReal.coe_ne_top)).map some

theorem weightedChoice_zero [Fintype A] (weights : A → ℝ≥0)
    (h : ∑ a, weights a = 0) : weightedChoice weights = PMF.pure none := by
  simp [weightedChoice, h]

theorem weightedChoice_some [Fintype A] (weights : A → ℝ≥0)
    (h : ∑ a, weights a ≠ 0) (a : A) :
    weightedChoice weights (some a) =
      (weights a : ℝ≥0∞) * (∑ x, (weights x : ℝ≥0∞))⁻¹ := by
  classical
  simp [weightedChoice, h, PMF.map_apply, PMF.normalize_apply, tsum_fintype]

theorem weightedChoice_none [Fintype A] (weights : A → ℝ≥0)
    (h : ∑ a, weights a ≠ 0) : weightedChoice weights none = 0 := by
  simp [weightedChoice, h, PMF.map_apply]

/-- Sampling rows are occurrence identities. Several rows can report the
same outcome; mapping the normalized row law adds all their masses. -/
theorem weightedChoice_report [Fintype I] [DecidableEq A] (weights : I → ℝ≥0)
    (report : I → A) (h : ∑ i, weights i ≠ 0) (a : A) :
    (weightedChoice weights |>.map (Option.map report)) (some a) =
      ∑ i, if a = report i then
        (weights i : ℝ≥0∞) * (∑ j, (weights j : ℝ≥0∞))⁻¹ else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_option]
  simp [weightedChoice_some weights h]

/-- Reference interval selection for a categorical row vector. Returning an
index keeps repeated rows distinct until the reported-outcome observation. -/
def chooseRow : List ℝ → ℝ → Option ℕ
  | [], _ => none
  | weight :: rest, position =>
      if position < weight then some 0
      else (chooseRow rest (position - weight)).map Nat.succ

/-- Exactly the out-of-support positions are refused. Zero-weight rows do
not add support. This is an exact real-arithmetic law, separate from a finite
generator grid or a floating cumulative sum. -/
theorem chooseRow_none_iff (weights : List ℝ) (position : ℝ)
    (nonnegative : ∀ weight ∈ weights, 0 ≤ weight) (position_nonnegative : 0 ≤ position) :
    chooseRow weights position = none ↔ weights.sum ≤ position := by
  induction weights generalizing position with
  | nil => simp [chooseRow, position_nonnegative]
  | cons weight rest ih =>
    have head_nonnegative := nonnegative weight (by simp)
    have rest_nonnegative : ∀ w ∈ rest, 0 ≤ w := by
      intro w member
      exact nonnegative w (List.mem_cons_of_mem weight member)
    have sum_nonnegative : 0 ≤ rest.sum := List.sum_nonneg rest_nonnegative
    by_cases below : position < weight
    · simp only [chooseRow, below, ↓reduceIte, reduceCtorEq, List.sum_cons]
      constructor
      · intro impossible; contradiction
      · intro bound; linarith
    · have remainder_nonnegative : 0 ≤ position-weight := by linarith
      simp only [chooseRow, below, ↓reduceIte, Option.map_eq_none_iff, List.sum_cons]
      rw [ih (position-weight) rest_nonnegative remainder_nonnegative]
      constructor <;> intro bound <;> linarith

theorem chooseRow_has_result (weights : List ℝ) (position : ℝ)
    (nonnegative : ∀ weight ∈ weights, 0 ≤ weight) (position_nonnegative : 0 ≤ position)
    (within : position < weights.sum) : ∃ index, chooseRow weights position = some index := by
  have not_none : chooseRow weights position ≠ none := by
    intro refused
    exact (not_le.mpr within)
      ((chooseRow_none_iff weights position nonnegative position_nonnegative).mp refused)
  cases result : chooseRow weights position with
  | none => exact False.elim (not_none result)
  | some index => exact ⟨index, rfl⟩

/-- A chosen row is a real vector occurrence; the search cannot fabricate an
index beyond the supplied rows. -/
theorem chooseRow_index_bound (weights : List ℝ) (position : ℝ) (index : ℕ)
    (selected : chooseRow weights position = some index) : index < weights.length := by
  induction weights generalizing position index with
  | nil => simp [chooseRow] at selected
  | cons weight rest ih =>
    by_cases below : position < weight
    · simp [chooseRow, below] at selected
      subst index; simp
    · simp only [chooseRow, below, ↓reduceIte] at selected
      cases choice : chooseRow rest (position-weight) with
      | none => simp [choice] at selected
      | some previous =>
        simp only [choice, Option.map_some, Option.some.injEq] at selected
        subst index
        simpa using Nat.succ_lt_succ (ih (position-weight) previous choice)

/-- The selected row owns exactly its half-open cumulative interval. This
connects indexed sampling to a cumulative table without merging equal rows. -/
theorem chooseRow_interval (weights : List ℝ) (position : ℝ) (index : ℕ)
    (nonnegative : ∀ weight ∈ weights, 0 ≤ weight) (position_nonnegative : 0 ≤ position) :
    chooseRow weights position = some index ↔
      index < weights.length ∧ (weights.take index).sum ≤ position ∧
        position < (weights.take (index+1)).sum := by
  induction weights generalizing position index with
  | nil => simp [chooseRow]
  | cons weight rest ih =>
    have rest_nonnegative : ∀ w ∈ rest, 0 ≤ w := by
      intro w member
      exact nonnegative w (List.mem_cons_of_mem weight member)
    cases index with
    | zero =>
      by_cases below : position < weight
      · simp [chooseRow, below, position_nonnegative]
      · cases chosen : chooseRow rest (position-weight) <;>
          simp [chooseRow, below, chosen]
    | succ index =>
      by_cases below : position < weight
      · have prefix_nonnegative : 0 ≤ (rest.take index).sum := by
          apply List.sum_nonneg
          intro w member
          exact rest_nonnegative w (List.mem_of_mem_take member)
        have impossible : ¬weight + (rest.take index).sum ≤ position := by linarith
        simp [chooseRow, below, List.take_succ_cons, impossible]
      · have remainder_nonnegative : 0 ≤ position-weight := by linarith
        have selection :
            (chooseRow rest (position-weight)).map Nat.succ = some (index+1) ↔
              chooseRow rest (position-weight) = some index := by
          cases chosen : chooseRow rest (position-weight) <;> simp
        simp only [chooseRow, below, ↓reduceIte, selection]
        rw [ih (position-weight) index rest_nonnegative remainder_nonnegative]
        simp only [List.length_cons, Nat.succ_lt_succ_iff, List.take_succ_cons,
          List.sum_cons]
        constructor
        · rintro ⟨bounded, lower, upper⟩
          exact ⟨bounded, by linarith, by linarith⟩
        · rintro ⟨bounded, lower, upper⟩
          exact ⟨bounded, by linarith, by linarith⟩

/-- Real probability mass of a Mathlib probability mass function. -/
def mass (p : PMF A) (a : A) : ℝ := (p a).toReal

@[simp] theorem sum_mass [Fintype A] (p : PMF A) : ∑ a, mass p a = 1 := by
  unfold mass
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

/-- Expectation of a real observation on a finite sample space. -/
def expectation [Fintype A] (p : PMF A) (f : A → ℝ) : ℝ :=
  ∑ a, mass p a * f a

@[simp] theorem expectation_one [Fintype A] (p : PMF A) :
    expectation p (fun _ => 1) = 1 := by simp [expectation]

@[simp] theorem expectation_const [Fintype A] (p : PMF A) (c : ℝ) :
    expectation p (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul]

theorem expectation_add [Fintype A] (p : PMF A) (f g : A → ℝ) :
    expectation p (fun a => f a + g a) = expectation p f + expectation p g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sum [Fintype A] [Fintype I] (p : PMF A) (f : I → A → ℝ) :
    expectation p (fun a => ∑ i, f i a) = ∑ i, expectation p (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_map [Fintype A] [Fintype B] (p : PMF A)
    (g : A → B) (f : B → ℝ) :
    expectation (p.map g) f = expectation p (fun a => f (g a)) := by
  classical
  have hm (b : B) : mass (p.map g) b = ∑ a, if b = g a then mass p a else 0 := by
    simp only [mass, PMF.map_apply, tsum_fintype]
    rw [ENNReal.toReal_sum]
    · congr 1
      funext a
      split_ifs <;> simp
    · intro a _
      split_ifs <;> simp [p.apply_ne_top]
  simp only [expectation, hm, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

theorem expectation_bind [Fintype A] [Fintype B] (p : PMF A)
    (q : A → PMF B) (f : B → ℝ) :
    expectation (p.bind q) f = expectation p (fun a => expectation (q a) f) := by
  unfold expectation mass
  simp only [PMF.bind_apply, tsum_fintype]
  simp_rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (p.apply_ne_top a)
    ((q a).apply_ne_top _)), ENNReal.toReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

/-- Independent samples indexed by a finite set of identities. -/
def independent [Fintype I] [DecidableEq I] [Fintype A] (p : I → PMF A) : PMF (I → A) := by
  classical
  refine PMF.ofFintype (fun xs => ∏ i, p i (xs i)) ?_
  rw [← Fintype.prod_sum]
  have h (i : I) : ∑ a, p i a = 1 := by
    simpa [tsum_fintype] using (p i).tsum_coe
  simp [h]

@[simp] theorem independent_apply [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → PMF A) (xs : I → A) : independent p xs = ∏ i, p i (xs i) := by
  classical
  rfl

/-- The product moment law proves independence of all indexed observations. -/
theorem expectation_independent_product [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → PMF A) (f : I → A → ℝ) :
    expectation (independent p) (fun xs => ∏ i, f i (xs i)) =
      ∏ i, expectation (p i) (f i) := by
  classical
  simp only [expectation, mass, independent_apply, ENNReal.toReal_prod,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : I) (a : A) => (p i a).toReal * f i a)).symm

theorem expectation_coordinate [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → PMF A) (i : I) (f : A → ℝ) :
    expectation (independent p) (fun xs => f (xs i)) = expectation (p i) f := by
  classical
  have h (j : I) : expectation (p j) (fun a => if j = i then f a else 1) =
      if j = i then expectation (p i) f else 1 := by
    by_cases hj : j = i <;> simp [hj]
  simpa [h] using
    expectation_independent_product p (fun j a => if j = i then f a else 1)

/-- Linearity needs no equality or distinctness of the per-probe kernels. -/
theorem expectation_independent_sum [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → PMF A) (f : I → A → ℝ) :
    expectation (independent p) (fun xs => ∑ i, f i (xs i)) =
      ∑ i, expectation (p i) (f i) := by
  rw [expectation_sum]
  congr 1
  funext i
  exact expectation_coordinate p i (f i)

/-- Sampling two independent finite populations, with arbitrary internal state. -/
def pair (p : PMF A) (q : PMF B) : PMF (A × B) :=
  p.bind fun a => q.map fun b => (a, b)

theorem expectation_pair_product [Fintype A] [Fintype B]
    (p : PMF A) (q : PMF B) (f : A → ℝ) (g : B → ℝ) :
    expectation (pair p q) (fun ab => f ab.1 * g ab.2) =
      expectation p f * expectation q g := by
  rw [pair, expectation_bind]
  simp_rw [expectation_map]
  simp only [expectation, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Shared random environments must be averaged *after* the conditional product. -/
theorem expectation_shared_environment {S : Type*} [Fintype S]
    [Fintype A] [Fintype B] (snapshot : PMF S)
    (p : S → PMF A) (q : S → PMF B) (f : A → ℝ) (g : B → ℝ) :
    expectation (snapshot.bind fun s => pair (p s) (q s))
      (fun ab => f ab.1 * g ab.2) =
      expectation snapshot (fun s => expectation (p s) f * expectation (q s) g) := by
  rw [expectation_bind]
  simp_rw [expectation_pair_product]

/-- Iterating a discrete Markov kernel refreshes the shared environment between
rounds. There is no assumption that successive states are independent. -/
def evolve {S : Type*} (kernel : S → PMF S) : ℕ → PMF S → PMF S
  | 0, initial => initial
  | n + 1, initial => (evolve kernel n initial).bind kernel

/-- Evolution composes without replaying an earlier prefix. -/
theorem evolve_add {S : Type*} (kernel : S → PMF S) (n m : ℕ) (initial : PMF S) :
    evolve kernel (n + m) initial = evolve kernel m (evolve kernel n initial) := by
  induction m with
  | zero => simp [evolve]
  | succ m ih => simp [evolve, ih]

theorem expectation_evolve_succ {S : Type*} [Fintype S]
    (kernel : S → PMF S) (n : ℕ) (initial : PMF S) (f : S → ℝ) :
    expectation (evolve kernel (n + 1) initial) f =
      expectation (evolve kernel n initial) (fun s => expectation (kernel s) f) := by
  exact expectation_bind _ _ _

/-- Two components are independently sampled at the current snapshot, after
which their joint result updates the shared state for the following round. -/
def adaptiveKernel {S : Type*} (left : S → PMF A) (right : S → PMF B)
    (update : S → A → B → S) (snapshot : S) : PMF S :=
  (pair (left snapshot) (right snapshot)).map (fun ab => update snapshot ab.1 ab.2)

/-- Exact tower law for adaptive rounds. The next state may correlate all
future observations through `update`. -/
theorem expectation_adaptive_step {S : Type*} [Fintype S]
    [Fintype A] [Fintype B] (left : S → PMF A) (right : S → PMF B)
    (update : S → A → B → S) (snapshots : PMF S) (f : S → ℝ) :
    expectation (snapshots.bind (adaptiveKernel left right update)) f =
      expectation snapshots (fun s =>
        expectation (left s) (fun a => expectation (right s) (fun b => f (update s a b)))) := by
  rw [expectation_bind]
  simp_rw [adaptiveKernel, expectation_map, pair, expectation_bind, expectation_map]

/-! ## Arbitrary snapshot types and nonnegative observations

Trail values need not form a finite type. Countably supported laws on arbitrary
state types are handled by `PMF` and nonnegative expectations. Tonelli's law
permits the following interchanges without an integrability assumption.
-/

def nnExpectation (p : PMF A) (f : A → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * f a

@[simp] theorem nnExpectation_pure (a : A) (f : A → ℝ≥0∞) :
    nnExpectation (PMF.pure a) f = f a := by
  classical
  simp [nnExpectation, PMF.pure_apply]

@[simp] theorem nnExpectation_one (p : PMF A) : nnExpectation p (fun _ => 1) = 1 := by
  simp [nnExpectation, p.tsum_coe]

theorem nnExpectation_bind (p : PMF A) (q : A → PMF B) (f : B → ℝ≥0∞) :
    nnExpectation (p.bind q) f = nnExpectation p (fun a => nnExpectation (q a) f) := by
  simp only [nnExpectation, PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]

theorem nnExpectation_map (p : PMF A) (g : A → B) (f : B → ℝ≥0∞) :
    nnExpectation (p.map g) f = nnExpectation p (fun a => f (g a)) := by
  rw [PMF.map, nnExpectation_bind]
  simp

theorem nnExpectation_pair_product (p : PMF A) (q : PMF B)
    (f : A → ℝ≥0∞) (g : B → ℝ≥0∞) :
    nnExpectation (pair p q) (fun ab => f ab.1 * g ab.2) =
      nnExpectation p f * nnExpectation q g := by
  rw [pair, nnExpectation_bind]
  simp_rw [nnExpectation_map]
  simp only [nnExpectation, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  apply tsum_congr
  intro b
  ac_rfl

theorem nnExpectation_sum [Fintype I] (p : PMF A) (f : I → A → ℝ≥0∞) :
    nnExpectation p (fun a => ∑ i, f i a) = ∑ i, nnExpectation p (f i) := by
  unfold nnExpectation
  calc
    (∑' a, p a * ∑ i, f i a) = ∑' a, ∑' i, p a * f i a := by
      apply tsum_congr
      intro a
      rw [ENNReal.tsum_mul_left, tsum_fintype]
    _ = ∑' i, ∑' a, p a * f i a := ENNReal.tsum_comm
    _ = ∑ i, ∑' a, p a * f i a := tsum_fintype _

theorem nnExpectation_independent_product [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → PMF A) (f : I → A → ℝ≥0∞) :
    nnExpectation (independent p) (fun xs => ∏ i, f i (xs i)) =
      ∏ i, nnExpectation (p i) (f i) := by
  simp only [nnExpectation, tsum_fintype, independent_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : I) (a : A) => p i a * f i a)).symm

theorem nnExpectation_coordinate [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → PMF A) (i : I) (f : A → ℝ≥0∞) :
    nnExpectation (independent p) (fun xs => f (xs i)) = nnExpectation (p i) f := by
  classical
  have h (j : I) : nnExpectation (p j) (fun a => if j = i then f a else 1) =
      if j = i then nnExpectation (p i) f else 1 := by
    by_cases hj : j = i <;> simp [hj]
  simpa [h] using nnExpectation_independent_product p (fun j a => if j = i then f a else 1)

theorem nnExpectation_shared_environment {S : Type*} (snapshots : PMF S)
    (left : S → PMF A) (right : S → PMF B) (f : A → ℝ≥0∞) (g : B → ℝ≥0∞) :
    nnExpectation (snapshots.bind fun s => pair (left s) (right s))
      (fun ab => f ab.1 * g ab.2) =
      nnExpectation snapshots (fun s => nnExpectation (left s) f * nnExpectation (right s) g) := by
  rw [nnExpectation_bind]
  simp_rw [nnExpectation_pair_product]

theorem nnExpectation_adaptive_step {S : Type*} (left : S → PMF A) (right : S → PMF B)
    (update : S → A → B → S) (snapshots : PMF S) (f : S → ℝ≥0∞) :
    nnExpectation (snapshots.bind (adaptiveKernel left right update)) f =
      nnExpectation snapshots (fun s =>
        nnExpectation (left s) (fun a => nnExpectation (right s) (fun b => f (update s a b)))) := by
  rw [nnExpectation_bind]
  simp_rw [adaptiveKernel, nnExpectation_map, pair, nnExpectation_bind, nnExpectation_map]

theorem nnExpectation_evolve_succ {S : Type*} (kernel : S → PMF S)
    (n : ℕ) (initial : PMF S) (f : S → ℝ≥0∞) :
    nnExpectation (evolve kernel (n + 1) initial) f =
      nnExpectation (evolve kernel n initial) (fun s => nnExpectation (kernel s) f) :=
  nnExpectation_bind _ _ _

end

end Mettapedia.ProbabilityTheory.IndependentFiniteSampling
