import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonConstraints
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Shore–Johnson Appendix (discrete, calculus skeleton)

This file begins the formal Appendix-style calculus used in Shore–Johnson's Theorem I/II proof.
We start with a basic “two-coordinate shift” curve on `Fin n`, which preserves the total mass
and varies only two coordinates.  This is the standard device for extracting partial-derivative
relations on the simplex without invoking full multivariate calculus.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendix

open Classical
open scoped BigOperators
open Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropy

/-! ## Two-coordinate shift curve -/

/-- Shift mass between two coordinates `i` and `j`, keeping their sum constant. -/
def shift2 {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) (t : ℝ) : Fin n → ℝ :=
  fun k =>
    if k = i then t
    else if k = j then q i + q j - t
    else q k

theorem shift2_apply_i {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    shift2 q i j t i = t := by
  simp [shift2]

theorem shift2_apply_j {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) (t : ℝ) (hij : i ≠ j) :
    shift2 q i j t j = q i + q j - t := by
  have hji : j ≠ i := by
    exact ne_comm.mp hij
  simp [shift2, hji]

theorem shift2_apply_other {n : ℕ} (q : Fin n → ℝ) (i j k : Fin n) (t : ℝ)
    (hki : k ≠ i) (hkj : k ≠ j) :
    shift2 q i j t k = q k := by
  simp [shift2, hki, hkj]

/-! ## Sum invariance (to be used later)

The next step in the Shore–Johnson Appendix proof is to show that
`∑ k, shift2 q i j t k = ∑ k, q k`, i.e. the shift preserves total mass.
We will use this to build admissible “directional curves” within the simplex.
-/

theorem sum_shift2 {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) (t : ℝ) (hij : i ≠ j) :
    (∑ k : Fin n, shift2 q i j t k) = ∑ k : Fin n, q k := by
  classical
  let s : Finset (Fin n) := Finset.univ
  have hi : i ∈ s := by simp [s]
  have hj : j ∈ s.erase i := by
    exact Finset.mem_erase.mpr ⟨ne_comm.mp hij, by simp [s]⟩
  -- Peel off `i`, then `j` from the sum over `shift2`.
  have hsum_i :
      (Finset.sum (s.erase i) (fun k => shift2 q i j t k)) + shift2 q i j t i =
        Finset.sum s (fun k => shift2 q i j t k) := by
    exact (Finset.sum_erase_add (s := s) (f := fun k => shift2 q i j t k) (a := i) hi)
  have hsum_j :
      (Finset.sum ((s.erase i).erase j) (fun k => shift2 q i j t k)) + shift2 q i j t j =
        Finset.sum (s.erase i) (fun k => shift2 q i j t k) := by
    exact (Finset.sum_erase_add (s := s.erase i) (f := fun k => shift2 q i j t k) (a := j) hj)
  have hsum_shift :
      (∑ k : Fin n, shift2 q i j t k) =
        (Finset.sum ((s.erase i).erase j) (fun k => shift2 q i j t k)) +
          shift2 q i j t j + shift2 q i j t i := by
    calc
      ∑ k : Fin n, shift2 q i j t k
          = (Finset.sum (s.erase i) (fun k => shift2 q i j t k)) + shift2 q i j t i := by
              exact hsum_i.symm
      _ = ((Finset.sum ((s.erase i).erase j) (fun k => shift2 q i j t k)) + shift2 q i j t j) +
            shift2 q i j t i := by
              simp [hsum_j]
      _ = (Finset.sum ((s.erase i).erase j) (fun k => shift2 q i j t k)) +
            shift2 q i j t j + shift2 q i j t i := by
              ac_rfl
  -- On the erased set, `shift2` agrees with `q`.
  have hsum_rest :
      Finset.sum ((s.erase i).erase j) (fun k => shift2 q i j t k) =
        Finset.sum ((s.erase i).erase j) (fun k => q k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hk' : k ∈ s.erase i := (Finset.mem_erase.mp hk).2
    have hki : k ≠ i := (Finset.mem_erase.mp hk').1
    simp [shift2, hki, hkj]
  -- Rebuild the full sum of `q` by reinserting `j`, then `i`.
  have hsum_q_j :
      (Finset.sum ((s.erase i).erase j) (fun k => q k)) + q j =
        Finset.sum (s.erase i) (fun k => q k) := by
    exact (Finset.sum_erase_add (s := s.erase i) (f := q) (a := j) hj)
  have hsum_q_i :
      (Finset.sum (s.erase i) (fun k => q k)) + q i =
        Finset.sum s (fun k => q k) := by
    exact (Finset.sum_erase_add (s := s) (f := q) (a := i) hi)
  -- Combine the pieces.
  calc
    ∑ k : Fin n, shift2 q i j t k
        = (Finset.sum ((s.erase i).erase j) (fun k => q k)) + (q i + q j - t) + t := by
            -- Substitute `shift2` values on `i` and `j`.
            simp [hsum_shift, hsum_rest, shift2_apply_i, shift2_apply_j, hij]
    _ = (Finset.sum ((s.erase i).erase j) (fun k => q k)) + (q i + q j) := by
            ring
    _ = Finset.sum s (fun k => q k) := by
            -- Reinsert `j`, then `i`.
            calc
              (Finset.sum ((s.erase i).erase j) (fun k => q k)) + (q i + q j)
                  = ((Finset.sum ((s.erase i).erase j) (fun k => q k)) + q j) + q i := by
                      ac_rfl
              _ = (Finset.sum (s.erase i) (fun k => q k)) + q i := by
                      simp [hsum_q_j]
              _ = Finset.sum s (fun k => q k) := by
                      simp [hsum_q_i]
    _ = ∑ k : Fin n, q k := by simp [s]

theorem sum_shift2_eq_one {n : ℕ} (q : ProbDist n) (i j : Fin n) (t : ℝ) (hij : i ≠ j) :
    (∑ k : Fin n, shift2 q.p i j t k) = 1 := by
  simpa [q.sum_one] using sum_shift2 (q := q.p) (i := i) (j := j) (t := t) hij

/-! ## Shift curve as a probability distribution -/

/-- A `ProbDist` obtained by shifting mass between `i` and `j`. -/
noncomputable def shift2Prob {n : ℕ} (q : ProbDist n) (i j : Fin n) (hij : i ≠ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ q.p i + q.p j) : ProbDist n where
  p := shift2 q.p i j t
  nonneg := by
    intro k
    by_cases hki : k = i
    · subst hki
      simp [shift2, ht0]
    by_cases hkj : k = j
    · subst hkj
      have hnonneg : 0 ≤ q.p i + q.p j - t := by
        linarith [q.nonneg i, q.nonneg j, ht1]
      have hji : j ≠ i := ne_comm.mp hij
      simpa [shift2, hji] using hnonneg
    · simp [shift2, hki, hkj, q.nonneg k]
  sum_one := by
    simpa using sum_shift2_eq_one (q := q) (i := i) (j := j) (t := t) hij

@[simp] theorem shift2Prob_apply_i {n : ℕ} (q : ProbDist n) (i j : Fin n) (hij : i ≠ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ q.p i + q.p j) :
    (shift2Prob q i j hij t ht0 ht1).p i = t := by
  simp [shift2Prob, shift2_apply_i]

@[simp] theorem shift2Prob_apply_j {n : ℕ} (q : ProbDist n) (i j : Fin n) (hij : i ≠ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ q.p i + q.p j) :
    (shift2Prob q i j hij t ht0 ht1).p j = q.p i + q.p j - t := by
  simp [shift2Prob, shift2_apply_j, hij]

@[simp] theorem shift2Prob_apply_other {n : ℕ} (q : ProbDist n) (i j k : Fin n) (hij : i ≠ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ q.p i + q.p j) (hki : k ≠ i) (hkj : k ≠ j) :
    (shift2Prob q i j hij t ht0 ht1).p k = q.p k := by
  simp [shift2Prob, shift2_apply_other, hki, hkj]

theorem sum_shift2_weighted_eq {n : ℕ} (q : Fin n → ℝ) (c : Fin n → ℝ)
    (i j : Fin n) (t : ℝ) (hij : i ≠ j) (hcoeff : c i = c j) :
    (∑ k : Fin n, shift2 q i j t k * c k) = ∑ k : Fin n, q k * c k := by
  classical
  let s : Finset (Fin n) := Finset.univ
  have hi : i ∈ s := by simp [s]
  have hj : j ∈ s.erase i := by
    exact Finset.mem_erase.mpr ⟨ne_comm.mp hij, by simp [s]⟩
  -- Split the weighted sum into `i`, `j`, and the remainder.
  have hsum_i :
      (Finset.sum (s.erase i) (fun k => shift2 q i j t k * c k)) +
        shift2 q i j t i * c i =
      Finset.sum s (fun k => shift2 q i j t k * c k) := by
    exact Finset.sum_erase_add (s := s) (f := fun k => shift2 q i j t k * c k) (a := i) hi
  have hsum_j :
      (Finset.sum ((s.erase i).erase j) (fun k => shift2 q i j t k * c k)) +
        shift2 q i j t j * c j =
      Finset.sum (s.erase i) (fun k => shift2 q i j t k * c k) := by
    exact Finset.sum_erase_add (s := s.erase i)
      (f := fun k => shift2 q i j t k * c k) (a := j) hj
  have hsum_shift :
      (∑ k : Fin n, shift2 q i j t k * c k) =
        (Finset.sum ((s.erase i).erase j) (fun k => shift2 q i j t k * c k)) +
          shift2 q i j t j * c j + shift2 q i j t i * c i := by
    calc
      ∑ k : Fin n, shift2 q i j t k * c k
          = (Finset.sum (s.erase i) (fun k => shift2 q i j t k * c k)) +
              shift2 q i j t i * c i := by
                exact hsum_i.symm
      _ = ((Finset.sum ((s.erase i).erase j) (fun k => shift2 q i j t k * c k)) +
            shift2 q i j t j * c j) + shift2 q i j t i * c i := by
              simp [hsum_j]
      _ = (Finset.sum ((s.erase i).erase j) (fun k => shift2 q i j t k * c k)) +
            shift2 q i j t j * c j + shift2 q i j t i * c i := by
              ac_rfl
  -- On the remainder, `shift2` agrees with `q`.
  have hsum_rest :
      Finset.sum ((s.erase i).erase j) (fun k => shift2 q i j t k * c k) =
        Finset.sum ((s.erase i).erase j) (fun k => q k * c k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hk' : k ∈ s.erase i := (Finset.mem_erase.mp hk).2
    have hki : k ≠ i := (Finset.mem_erase.mp hk').1
    simp [shift2, hki, hkj]
  -- Rebuild the weighted sum of `q`.
  have hsum_q_j :
      (Finset.sum ((s.erase i).erase j) (fun k => q k * c k)) + q j * c j =
        Finset.sum (s.erase i) (fun k => q k * c k) := by
    exact (Finset.sum_erase_add (s := s.erase i) (f := fun k => q k * c k) (a := j) hj)
  have hsum_q_i :
      (Finset.sum (s.erase i) (fun k => q k * c k)) + q i * c i =
        Finset.sum s (fun k => q k * c k) := by
    exact (Finset.sum_erase_add (s := s) (f := fun k => q k * c k) (a := i) hi)
  calc
    ∑ k : Fin n, shift2 q i j t k * c k
        = (Finset.sum ((s.erase i).erase j) (fun k => q k * c k)) +
            (q i + q j - t) * c j + t * c i := by
          simp [hsum_shift, hsum_rest, shift2_apply_i, shift2_apply_j, hij]
    _ = (Finset.sum ((s.erase i).erase j) (fun k => q k * c k)) +
          ((q i + q j - t) * c j + t * c i) := by
          ac_rfl
    _ = (Finset.sum ((s.erase i).erase j) (fun k => q k * c k)) +
          (q i * c i + q j * c j) := by
          have hrewrite :
              (q i + q j - t) * c j + t * c i = q i * c i + q j * c j := by
            calc
              (q i + q j - t) * c j + t * c i
                  = (q i + q j - t) * c j + t * c j := by
                      simp [hcoeff]
              _ = (q i + q j) * c j := by ring
              _ = q i * c j + q j * c j := by ring
              _ = q i * c i + q j * c j := by simp [hcoeff]
          simp [hrewrite]
    _ = Finset.sum s (fun k => q k * c k) := by
          calc
            (Finset.sum ((s.erase i).erase j) (fun k => q k * c k)) + (q i * c i + q j * c j)
                = ((Finset.sum ((s.erase i).erase j) (fun k => q k * c k)) + q j * c j) +
                    q i * c i := by
                      ac_rfl
            _ = (Finset.sum (s.erase i) (fun k => q k * c k)) + q i * c i := by
                      simp [hsum_q_j]
            _ = Finset.sum s (fun k => q k * c k) := by
                      simp [hsum_q_i]
    _ = ∑ k : Fin n, q k * c k := by simp [s]

def satisfiesFn {n : ℕ} (c : ShoreJohnsonConstraints.EVConstraint n) (q : Fin n → ℝ) : Prop :=
  (∑ i : Fin n, q i * c.coeff i) = c.rhs

theorem satisfiesFn_shift2_of_coeff_eq {n : ℕ} (c : ShoreJohnsonConstraints.EVConstraint n)
    (q : Fin n → ℝ) (i j : Fin n) (t : ℝ) (hij : i ≠ j) (hcoeff : c.coeff i = c.coeff j) :
    satisfiesFn c (shift2 q i j t) ↔ satisfiesFn c q := by
  dsimp [satisfiesFn]
  have hsum :=
    sum_shift2_weighted_eq (q := q) (c := c.coeff) (i := i) (j := j) (t := t) hij hcoeff
  constructor
  · intro h
    simpa [hsum] using h
  · intro h
    simpa [hsum] using h

/-! ## Sum-of-atoms objective and a derivative along `shift2` -/

/-- A separable sum objective over coordinates. -/
noncomputable def sumObjective {n : ℕ} (φ : ℝ → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n, φ (q k)

/-- A separable sum objective with coordinate-specific functions. -/
noncomputable def sumObjectiveCoord {n : ℕ} (φ : Fin n → ℝ → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n, φ k (q k)

theorem hasDerivAt_sumObjective_shift2 {n : ℕ}
    (φ : ℝ → ℝ) (q : Fin n → ℝ) (i j : Fin n) (t : ℝ) (hij : i ≠ j)
    (φ'i φ'j : ℝ)
    (hφi : HasDerivAt φ φ'i t)
    (hφj : HasDerivAt φ φ'j (q i + q j - t)) :
    HasDerivAt (fun u => sumObjective φ (shift2 q i j u)) (φ'i - φ'j) t := by
  classical
  -- Derivative of the linear map `u ↦ q i + q j - u`.
  have hlin : HasDerivAt (fun u : ℝ => q i + q j - u) (-1) t := by
    have hconst : HasDerivAt (fun _ : ℝ => q i + q j) 0 t := hasDerivAt_const t (q i + q j)
    have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
    simpa using hconst.sub hid
  -- Build pointwise derivatives for each coordinate.
  have hcoord :
      ∀ k ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun u => φ (shift2 q i j u k))
          (if k = i then φ'i else if k = j then -φ'j else 0) t := by
    intro k _hk
    by_cases hki : k = i
    · subst hki
      simpa [shift2_apply_i] using hφi
    · by_cases hkj : k = j
      · have hji : j ≠ i := ne_comm.mp hij
        have hcomp : HasDerivAt (fun u => φ (q i + q j - u)) (φ'j * (-1)) t :=
          hφj.comp t hlin
        -- simplify the scalar product to `-φ'j`
        simpa [shift2, hki, hkj, hji, mul_comm, mul_left_comm, mul_assoc] using hcomp
      · have hconst : HasDerivAt (fun _ : ℝ => φ (q k)) 0 t := hasDerivAt_const t (φ (q k))
        have hrewrite : (fun u => φ (shift2 q i j u k)) = fun _ : ℝ => φ (q k) := by
          funext u
          simp [shift2_apply_other, hki, hkj]
        simpa [hrewrite, hki, hkj] using hconst
  -- Sum the coordinate derivatives.
  have hsum :
      HasDerivAt (fun u => sumObjective φ (shift2 q i j u))
        (∑ k : Fin n, if k = i then φ'i else if k = j then -φ'j else 0) t := by
    simpa [sumObjective] using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
        (A := fun k u => φ (shift2 q i j u k))
        (A' := fun k => if k = i then φ'i else if k = j then -φ'j else 0)
        (x := t) hcoord)
  -- Simplify the derivative sum.
  have hsum' :
      (∑ k : Fin n, if k = i then φ'i else if k = j then -φ'j else 0) = φ'i - φ'j := by
    classical
    let s : Finset (Fin n) := Finset.univ
    let f : Fin n → ℝ := fun k => if k = i then φ'i else if k = j then -φ'j else 0
    have hi : i ∈ s := by simp [s]
    have hj : j ∈ s.erase i := by
      exact Finset.mem_erase.mpr ⟨ne_comm.mp hij, by simp [s]⟩
    have hsum_i : (Finset.sum (s.erase i) f) + f i = Finset.sum s f :=
      Finset.sum_erase_add (s := s) (f := f) (a := i) hi
    have hsum_j : (Finset.sum ((s.erase i).erase j) f) + f j = Finset.sum (s.erase i) f :=
      Finset.sum_erase_add (s := s.erase i) (f := f) (a := j) hj
    have hsum_rest : Finset.sum ((s.erase i).erase j) f = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hk' : k ∈ s.erase i := (Finset.mem_erase.mp hk).2
      have hki : k ≠ i := (Finset.mem_erase.mp hk').1
      simp [hki, hkj]
    have hsum_s :
        Finset.sum s f =
          (Finset.sum ((s.erase i).erase j) f) + f j + f i := by
      calc
        Finset.sum s f = (Finset.sum (s.erase i) f) + f i := by
          simpa using hsum_i.symm
        _ = ((Finset.sum ((s.erase i).erase j) f) + f j) + f i := by
          simp [hsum_j.symm]
        _ = (Finset.sum ((s.erase i).erase j) f) + f j + f i := by
          ac_rfl
    have hji : j ≠ i := ne_comm.mp hij
    have hfi : f i = φ'i := by
      simp [f]
    have hfj : f j = -φ'j := by
      simp [f, hji]
    have hsum_f : Finset.sum s f = φ'i - φ'j := by
      calc
        Finset.sum s f = (Finset.sum ((s.erase i).erase j) f) + f j + f i := hsum_s
        _ = f j + f i := by simp [hsum_rest]
        _ = (-φ'j) + φ'i := by
              simp [hfj, hfi]
        _ = φ'i - φ'j := by
              ring
    simpa [s, f] using hsum_f
  -- Finish.
  simpa [hsum'] using hsum

theorem hasDerivAt_sumObjectiveCoord_shift2 {n : ℕ}
    (φ : Fin n → ℝ → ℝ) (q : Fin n → ℝ) (i j : Fin n) (t : ℝ) (hij : i ≠ j)
    (φ'i φ'j : ℝ)
    (hφi : HasDerivAt (fun x => φ i x) φ'i t)
    (hφj : HasDerivAt (fun x => φ j x) φ'j (q i + q j - t)) :
    HasDerivAt (fun u => sumObjectiveCoord φ (shift2 q i j u)) (φ'i - φ'j) t := by
  classical
  -- Derivative of the linear map `u ↦ q i + q j - u`.
  have hlin : HasDerivAt (fun u : ℝ => q i + q j - u) (-1) t := by
    have hconst : HasDerivAt (fun _ : ℝ => q i + q j) 0 t := hasDerivAt_const t (q i + q j)
    have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
    simpa using hconst.sub hid
  -- Build pointwise derivatives for each coordinate.
  have hcoord :
      ∀ k ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun u => φ k (shift2 q i j u k))
          (if k = i then φ'i else if k = j then -φ'j else 0) t := by
    intro k _hk
    by_cases hki : k = i
    · subst hki
      simpa [shift2_apply_i] using hφi
    · by_cases hkj : k = j
      · have hji : j ≠ i := ne_comm.mp hij
        have hcomp : HasDerivAt (fun u => φ j (q i + q j - u)) (φ'j * (-1)) t :=
          hφj.comp t hlin
        simpa [shift2, hki, hkj, hji, mul_comm, mul_left_comm, mul_assoc] using hcomp
      · have hconst : HasDerivAt (fun _ : ℝ => φ k (q k)) 0 t := hasDerivAt_const t (φ k (q k))
        have hrewrite : (fun u => φ k (shift2 q i j u k)) = fun _ : ℝ => φ k (q k) := by
          funext u
          simp [shift2_apply_other, hki, hkj]
        simpa [hrewrite, hki, hkj] using hconst
  -- Sum the coordinate derivatives.
  have hsum :
      HasDerivAt (fun u => sumObjectiveCoord φ (shift2 q i j u))
        (∑ k : Fin n, if k = i then φ'i else if k = j then -φ'j else 0) t := by
    simpa [sumObjectiveCoord] using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
        (A := fun k u => φ k (shift2 q i j u k))
        (A' := fun k => if k = i then φ'i else if k = j then -φ'j else 0)
        (x := t) hcoord)
  -- Simplify the derivative sum.
  have hsum' :
      (∑ k : Fin n, if k = i then φ'i else if k = j then -φ'j else 0) = φ'i - φ'j := by
    classical
    let s : Finset (Fin n) := Finset.univ
    let f : Fin n → ℝ := fun k => if k = i then φ'i else if k = j then -φ'j else 0
    have hi : i ∈ s := by simp [s]
    have hj : j ∈ s.erase i := by
      exact Finset.mem_erase.mpr ⟨ne_comm.mp hij, by simp [s]⟩
    have hsum_i : (Finset.sum (s.erase i) f) + f i = Finset.sum s f :=
      Finset.sum_erase_add (s := s) (f := f) (a := i) hi
    have hsum_j : (Finset.sum ((s.erase i).erase j) f) + f j = Finset.sum (s.erase i) f :=
      Finset.sum_erase_add (s := s.erase i) (f := f) (a := j) hj
    have hsum_rest : Finset.sum ((s.erase i).erase j) f = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hk' : k ∈ s.erase i := (Finset.mem_erase.mp hk).2
      have hki : k ≠ i := (Finset.mem_erase.mp hk').1
      simp [hki, hkj]
    have hsum_s :
        Finset.sum s f =
          (Finset.sum ((s.erase i).erase j) f) + f j + f i := by
      calc
        Finset.sum s f = (Finset.sum (s.erase i) f) + f i := by
          simpa using hsum_i.symm
        _ = ((Finset.sum ((s.erase i).erase j) f) + f j) + f i := by
          simp [hsum_j.symm]
        _ = (Finset.sum ((s.erase i).erase j) f) + f j + f i := by
          ac_rfl
    have hji : j ≠ i := ne_comm.mp hij
    have hfi : f i = φ'i := by
      simp [f]
    have hfj : f j = -φ'j := by
      simp [f, hji]
    have hsum_f : Finset.sum s f = φ'i - φ'j := by
      calc
        Finset.sum s f = (Finset.sum ((s.erase i).erase j) f) + f j + f i := hsum_s
        _ = f j + f i := by simp [hsum_rest]
        _ = (-φ'j) + φ'i := by
              simp [hfj, hfi]
        _ = φ'i - φ'j := by
              ring
    simpa [s, f] using hsum_f
  -- Finish.
  simpa [hsum'] using hsum

theorem shift2_critical_eq_coord {n : ℕ}
    (φ : Fin n → ℝ → ℝ) (q : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j)
    (φ'i φ'j : ℝ)
    (hφi : HasDerivAt (fun x => φ i x) φ'i (q i))
    (hφj : HasDerivAt (fun x => φ j x) φ'j (q j))
    (hcrit : HasDerivAt (fun u => sumObjectiveCoord φ (shift2 q i j u)) 0 (q i)) :
    φ'i = φ'j := by
  have hsum :=
    hasDerivAt_sumObjectiveCoord_shift2 (φ := φ) (q := q) (i := i) (j := j) (t := q i) hij
      φ'i φ'j hφi (by simpa using hφj)
  have hder : φ'i - φ'j = 0 := by
    have := hsum.unique hcrit
    simpa using this
  linarith

theorem shift2_critical_eq_coord_of_isLocalMin {n : ℕ}
    (φ : Fin n → ℝ → ℝ) (q : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j)
    (φ'i φ'j : ℝ)
    (hφi : HasDerivAt (fun x => φ i x) φ'i (q i))
    (hφj : HasDerivAt (fun x => φ j x) φ'j (q j))
    (hmin : IsLocalMin (fun u => sumObjectiveCoord φ (shift2 q i j u)) (q i)) :
    φ'i = φ'j := by
  have hder :=
    hasDerivAt_sumObjectiveCoord_shift2 (φ := φ) (q := q) (i := i) (j := j) (t := q i) hij
      φ'i φ'j hφi (by simpa using hφj)
  have hzero : φ'i - φ'j = 0 := hmin.hasDerivAt_eq_zero hder
  linarith

theorem shift2_critical_eq {n : ℕ}
    (φ : ℝ → ℝ) (q : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j)
    (φ'i φ'j : ℝ)
    (hφi : HasDerivAt φ φ'i (q i))
    (hφj : HasDerivAt φ φ'j (q j))
    (hcrit : HasDerivAt (fun u => sumObjective φ (shift2 q i j u)) 0 (q i)) :
    φ'i = φ'j := by
  have hsum :=
    hasDerivAt_sumObjective_shift2 (φ := φ) (q := q) (i := i) (j := j) (t := q i) hij
      φ'i φ'j hφi (by simpa using hφj)
  have hder : φ'i - φ'j = 0 := by
    -- Uniqueness of derivatives.
    have := hsum.unique hcrit
    simpa using this
  linarith

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendix
