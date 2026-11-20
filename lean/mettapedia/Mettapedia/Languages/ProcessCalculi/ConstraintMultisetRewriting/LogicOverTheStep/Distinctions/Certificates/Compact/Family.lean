import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Work
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Controls

/-!
# Many states in four classes: the blown-up leak chain

**The family** (`blowup m`): `m + 1` copies of each of the four states of the leak chain (`leak`):
safe, once, leaky, sink. Every state moves by two half-moves, each with probability `1/2`, to states
of other copies: safe moves to the next copy of safe; once to its own copy of safe or the next copy of
the sink; leaky to the next copy of leaky or its own copy of the sink; the sink to the next copy of the
sink. One indicator observation, of the sink. Same-class states have different successor
distributions (their supports are disjoint), yet the classes lump exactly onto the leak chain
(`blowup_lumping`), for every `m`.

**The certificate on classes** (`classCert m`): the class map, the leak chain, and the leak chain's
prefixpoint certificate with one listed coupling (`correct`). It is accepted for every `m`
(`classCert_accepted`), so the metric of every blown-up chain is at most the leak metric at the classes
(`bisimulationMetric_blowup_le`), and with the leak chain's dual certificate it is exactly that
(`bisimulationMetric_blowup`): `9/11` between every safe and every leaky state, `0` between copies.

**The incumbent's limit** (`listed_of_close`, `listed_count`, `prefixpointSize_ge`): every accepted
prefixpoint certificate of `blowup m` whose kernel is below `c/2` at two distinct once-or-leaky states
lists a coupling at the pair or at its reverse: there the independent coupling costs at least `1/2`,
from the observation condition alone. So a certificate proving bounds as strong as the class
certificate's (`close_of_le`) lists at least `(m + 1)(2m + 1)` couplings of `n²` entries each,
`n = 4(m + 1)`; the bound is attained at `m = 1` (`fullCert_accepted_one`, `fullCert_listed_one`).

**The measurement** (exact counts, `Work`):
* the class certificate's checker costs `(364, 16(m+1)² + 304, 20(m+1) + 116, 64(m+1)² + 15)`
  products, additions, comparisons and tests (`classWork_blowup`), and its size is `4m + 56`
  (`classSize_blowup`);
* every accepted prefixpoint certificate costs at least `n(n-1)(n²+1)` products and
  `n(n-1)(n²+n)` additions (`prefixpointWork_lower`);
* so for every `m ≥ 1` the class certificate is at least four times smaller than any incumbent
  certificate proving as much (`four_times_smaller`), and its checker's whole work is at most a quarter
  of the products and additions of any accepted incumbent certificate's checker
  (`four_times_cheaper`);
* at `m = 0` (no two states in a class) it loses: the same quotient check plus the lumping check, and
  a larger certificate (`loses_without_classes`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Family

open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Controls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact

/-! ## The family -/

/-- The states: a class (`0` safe, `1` once, `2` leaky, `3` sink) and a copy. -/
abbrev St (m : ℕ) := Fin 4 × Fin (m + 1)

/-- The first half-move: safe to the next safe, once to its own safe, leaky to the next leaky, the
sink to the next sink. -/
def firstMove {m : ℕ} (s : St m) : St m :=
  (![0, 0, 2, 3] s.1, ![s.2 + 1, s.2, s.2 + 1, s.2 + 1] s.1)

/-- The second half-move: safe to the next safe, once to the next sink, leaky to its own sink, the
sink to the next sink. -/
def secondMove {m : ℕ} (s : St m) : St m :=
  (![0, 3, 3, 3] s.1, ![s.2 + 1, s.2 + 1, s.2, s.2 + 1] s.1)

/-- Each half-move has probability `1/2`. -/
def blowTrans (m : ℕ) (s x : St m) : ℚ :=
  1 / 2 * dirac (firstMove s) x + 1 / 2 * dirac (secondMove s) x

theorem blowTrans_isDistribution (m : ℕ) (s : St m) : IsDistribution (blowTrans m s) where
  nonneg x := by unfold blowTrans dirac; split_ifs <;> norm_num
  sum_eq_one := by
    simp only [blowTrans, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [(isDistribution_dirac (𝕜 := ℚ) (firstMove s)).sum_eq_one,
      (isDistribution_dirac (𝕜 := ℚ) (secondMove s)).sum_eq_one]
    norm_num

/-- **The blown-up leak chain**: `m + 1` copies of each state of the leak chain. -/
def blowup (m : ℕ) : LabelledMarkovChain ℚ Unit Unit (St m) where
  trans _ := blowTrans m
  isDistribution _ := blowTrans_isDistribution m
  observe _ s := ![0, 0, 0, 1] s.1

theorem card_St (m : ℕ) : Fintype.card (St m) = 4 * (m + 1) := by
  simp [St]

theorem discount_pos : 0 < discount := by norm_num [discount]

/-! ## The classes lump onto the leak chain -/

/-- The two half-moves of a class, read on the classes, are the leak chain's row. -/
theorem classRow : ∀ i k : Fin 4,
    1 / 2 * (if (![0, 0, 2, 3] : Fin 4 → Fin 4) i = k then (1 : ℚ) else 0) +
      1 / 2 * (if (![0, 3, 3, 3] : Fin 4 → Fin 4) i = k then 1 else 0) = leakTrans i k := by
  decide +kernel

/-- **The classes are a lumping onto the leak chain**, for every number of copies. -/
theorem blowup_lumping (m : ℕ) : IsLumping (blowup m) leak Prod.fst where
  trans_eq _ s k := by
    change fibreMass Prod.fst
      (fun x => 1 / 2 * dirac (firstMove s) x + 1 / 2 * dirac (secondMove s) x) k = leakTrans s.1 k
    rw [fibreMass_add, fibreMass_mul_left, fibreMass_mul_left, fibreMass_dirac, fibreMass_dirac]
    exact classRow s.1 k
  observe_eq _ _ := rfl

/-! ## The certificate on classes, for every size -/

/-- **The certificate on classes**: the class map, the leak chain, and its prefixpoint certificate
with one listed coupling. -/
def classCert (m : ℕ) : OnClasses Unit Unit (St m) (Fin 4) := ⟨Prod.fst, leak, correct⟩

theorem classCert_accepted (m : ℕ) : classCheck (blowup m) discount (classCert m) = true :=
  classCheck_iff.mpr ⟨blowup_lumping m, correct_accepted⟩

/-- **The checked bound, for every size**: the metric of the blown-up chain is at most the leak
metric at the classes. -/
theorem bisimulationMetric_blowup_le (m : ℕ) (s t : St m) :
    bisimulationMetric (realChain (blowup m)) (realChain (blowup m)) (discount : ℝ) s t ≤
      (exactKernel s.1 t.1 : ℝ) :=
  classCheck_sound (classCert_accepted m) discount_nonneg s t

/-- **The exact metric, for every size**: with the leak chain's dual certificate, the metric of the
blown-up chain is the leak metric at the classes. -/
theorem bisimulationMetric_blowup (m : ℕ) (s t : St m) :
    bisimulationMetric (realChain (blowup m)) (realChain (blowup m)) (discount : ℝ) s t =
      (exactKernel s.1 t.1 : ℝ) :=
  classCheck_exact_of_dual (classCert_accepted m) (dual := exactDual) exactDual_accepted rfl
    discount_pos discount_lt_one

/-- **`9/11` between every safe and every leaky state**, at every size. -/
theorem metric_safe_leaky (m : ℕ) (j j' : Fin (m + 1)) :
    bisimulationMetric (realChain (blowup m)) (realChain (blowup m)) (9 / 10) (0, j) (2, j') =
      9 / 11 := by
  have value : exactKernel 0 2 = 9 / 11 := by decide +kernel
  rw [← discount_real, bisimulationMetric_blowup, value]
  norm_num

/-! ## The incumbent's limit -/

/-- The classes `once` and `leaky`. -/
def middle (i : Fin 4) : Prop := i = 1 ∨ i = 2

instance (i : Fin 4) : Decidable (middle i) := by unfold middle; infer_instance

/-- From a once-or-leaky state the first half-move is not the sink and the second is. -/
theorem middle_moves : ∀ i : Fin 4, middle i →
    (![0, 0, 0, 1] : Fin 4 → ℚ) ((![0, 0, 2, 3] : Fin 4 → Fin 4) i) = 0 ∧
      (![0, 0, 0, 1] : Fin 4 → ℚ) ((![0, 3, 3, 3] : Fin 4 → Fin 4) i) = 1 := by
  decide +kernel

/-- An expectation under two half-moves. -/
theorem sum_halves {m : ℕ} (s : St m) (f : St m → ℚ) :
    ∑ u, blowTrans m s u * f u = 1 / 2 * f (firstMove s) + 1 / 2 * f (secondMove s) := by
  unfold blowTrans dirac
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **The independent coupling of two half-move states** costs the average of the four pairs of
half-moves. -/
theorem jointCost_product_halves {m : ℕ} (s t : St m) (D : St m → St m → ℚ) :
    jointCost (productTable (blowTrans m s) (blowTrans m t)) D =
      1 / 2 * (1 / 2 * D (firstMove s) (firstMove t) + 1 / 2 * D (firstMove s) (secondMove t)) +
        1 / 2 * (1 / 2 * D (secondMove s) (firstMove t) +
          1 / 2 * D (secondMove s) (secondMove t)) := by
  unfold jointCost productTable
  have inner : ∀ u, ∑ v, blowTrans m s u * blowTrans m t v * D u v =
      blowTrans m s u * (1 / 2 * D u (firstMove t) + 1 / 2 * D u (secondMove t)) := by
    intro u
    simp only [mul_assoc]
    rw [← Finset.mul_sum, sum_halves t (D u)]
  simp only [inner]
  exact sum_halves s fun u => 1 / 2 * D u (firstMove t) + 1 / 2 * D u (secondMove t)

/-- **A pair of distinct once-or-leaky states with kernel below `c/2` needs a listed coupling**, at
the pair or at its reverse, in every accepted prefixpoint certificate, at every discount `0 < c`. -/
theorem listed_of_close {m : ℕ} {c : ℚ} {cert : Prefixpoint Unit (St m)}
    (accepted : check (blowup m) c cert = true) (c_pos : 0 < c) {s t : St m} (hs : middle s.1)
    (ht : middle t.1) (distinct : s ≠ t) (close : cert.kernel s t < c / 2) :
    (cert.listed () s t).isSome ∨ (cert.listed () t s).isSome := by
  obtain ⟨nonneg, observed, covered⟩ := coreCheck_iff.mp (check_iff.mp accepted).1
  by_contra neither
  simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    at neither
  obtain ⟨here_none, there_none⟩ := neither
  have here := covered () s t
  simp only [coveredAt, coveredBetween, here_none, there_none, Bool.or_eq_true, decide_eq_true_eq,
    distinct, Bool.false_eq_true, or_false, false_or] at here
  change c * jointCost (productTable (blowTrans m s) (blowTrans m t)) cert.kernel ≤ cert.kernel s t
    at here
  rw [jointCost_product_halves] at here
  have gap : ∀ x y : St m, middle x.1 → middle y.1 → 1 ≤ cert.kernel (firstMove x) (secondMove y) := by
    intro x y hx hy
    have bound := observed () (firstMove x) (secondMove y)
    have first : (blowup m).observe () (firstMove x) = 0 := (middle_moves x.1 hx).1
    have second : (blowup m).observe () (secondMove y) = 1 := (middle_moves y.1 hy).2
    rw [first, second] at bound
    norm_num at bound
    exact bound
  have gap' : ∀ x y : St m, middle x.1 → middle y.1 → 1 ≤ cert.kernel (secondMove x) (firstMove y) := by
    intro x y hx hy
    have bound := observed () (secondMove x) (firstMove y)
    have first : (blowup m).observe () (secondMove x) = 1 := (middle_moves x.1 hx).2
    have second : (blowup m).observe () (firstMove y) = 0 := (middle_moves y.1 hy).1
    rw [first, second] at bound
    norm_num at bound
    exact bound
  have one := gap s t hs ht
  have two := gap' s t hs ht
  have three := nonneg (firstMove s) (firstMove t)
  have four := nonneg (secondMove s) (secondMove t)
  have half : c * (1 / 2) ≤ c * (1 / 2 * (1 / 2 * cert.kernel (firstMove s) (firstMove t) +
      1 / 2 * cert.kernel (firstMove s) (secondMove t)) + 1 / 2 * (1 / 2 *
        cert.kernel (secondMove s) (firstMove t) + 1 / 2 * cert.kernel (secondMove s) (secondMove t))) :=
    mul_le_mul_of_nonneg_left (by linarith) c_pos.le
  linarith

/-- The once-or-leaky states. -/
def middleStates (m : ℕ) : Finset (St m) := Finset.univ.filter fun s => middle s.1

theorem card_middleStates (m : ℕ) : (middleStates m).card = 2 * (m + 1) := by
  have product : middleStates m =
      (Finset.univ.filter middle) ×ˢ (Finset.univ : Finset (Fin (m + 1))) := by
    ext s
    simp [middleStates]
  have two : (Finset.univ.filter middle : Finset (Fin 4)).card = 2 := by decide +kernel
  rw [product, Finset.card_product, two, Finset.card_univ, Fintype.card_fin]

/-- **Every accepted prefixpoint certificate with kernel below `c/2` at all pairs of distinct
once-or-leaky states lists at least `(m + 1)(2m + 1)` couplings.** -/
theorem listed_count {m : ℕ} {c : ℚ} {cert : Prefixpoint Unit (St m)}
    (accepted : check (blowup m) c cert = true) (c_pos : 0 < c)
    (close : ∀ s t : St m, middle s.1 → middle t.1 → s ≠ t → cert.kernel s t < c / 2) :
    (m + 1) * (2 * m + 1) ≤ (listedTriples cert).card := by
  set L := (listedTriples cert).image fun p => p.2 with L_def
  have cover : (middleStates m).offDiag ⊆ L ∪ L.image Prod.swap := by
    intro p member
    rw [Finset.mem_offDiag] at member
    obtain ⟨hs, ht, distinct⟩ := member
    simp only [middleStates, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
    rcases listed_of_close accepted c_pos hs ht distinct (close _ _ hs ht distinct) with here | there
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨((), p.1, p.2), ?_, rfl⟩)
      simp [listedTriples, here]
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p.2, p.1), ?_, rfl⟩)
      refine Finset.mem_image.mpr ⟨((), p.2, p.1), ?_, rfl⟩
      simp [listedTriples, there]
  have size := Finset.card_le_card cover
  have union := Finset.card_union_le L (L.image Prod.swap)
  have swapped : (L.image Prod.swap).card ≤ L.card := Finset.card_image_le
  have projected : L.card ≤ (listedTriples cert).card := Finset.card_image_le
  rw [Finset.offDiag_card, card_middleStates] at size
  have pairs : 2 * (m + 1) * (2 * (m + 1)) - 2 * (m + 1) = 2 * ((m + 1) * (2 * m + 1)) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [pairs] at size
  linarith

/-- **The size of every such certificate is at least `n² (1 + (m + 1)(2m + 1))`**, `n = 4(m + 1)`. -/
theorem prefixpointSize_ge {m : ℕ} {c : ℚ} {cert : Prefixpoint Unit (St m)}
    (accepted : check (blowup m) c cert = true) (c_pos : 0 < c)
    (close : ∀ s t : St m, middle s.1 → middle t.1 → s ≠ t → cert.kernel s t < c / 2) :
    4 * (m + 1) * (4 * (m + 1)) * (1 + (m + 1) * (2 * m + 1)) ≤ prefixpointSize cert := by
  have count := listed_count accepted c_pos close
  unfold prefixpointSize
  rw [card_St]
  exact Nat.mul_le_mul_left _ (by omega)

/-- **Proving bounds as strong as the class certificate's** at the once-or-leaky pairs puts the
kernel below `c/2` there, at the discount `9/10`. -/
theorem close_of_le {m : ℕ} {cert : Prefixpoint Unit (St m)}
    (le : ∀ s t : St m, middle s.1 → middle t.1 → cert.kernel s t ≤ exactKernel s.1 t.1) :
    ∀ s t : St m, middle s.1 → middle t.1 → s ≠ t → cert.kernel s t < discount / 2 := by
  intro s t hs ht _
  have small : ∀ i j : Fin 4, middle i → middle j → exactKernel i j < discount / 2 := by
    decide +kernel
  exact (le s t hs ht).trans_lt (small s.1 t.1 hs ht)

/-! ## The bound is attained -/

/-- One orientation of a pair: class first, then copy. -/
def before {m : ℕ} (s t : St m) : Prop := s.1 < t.1 ∨ (s.1 = t.1 ∧ s.2 < t.2)

instance {m : ℕ} (s t : St m) : Decidable (before s t) := by unfold before; infer_instance

/-- The coupling of two half-move states that matches first with first and second with second. -/
def matched {m : ℕ} (s t : St m) : St m → St m → ℚ := fun u v =>
  1 / 2 * (if u = firstMove s ∧ v = firstMove t then 1 else 0) +
    1 / 2 * (if u = secondMove s ∧ v = secondMove t then 1 else 0)

/-- **The incumbent's certificate of the exact metric**: the leak metric at the classes, and the
matched coupling at each pair of distinct once-or-leaky states, in one orientation. -/
def fullCert (m : ℕ) : Prefixpoint Unit (St m) where
  kernel s t := exactKernel s.1 t.1
  listed _ s t := if middle s.1 ∧ middle t.1 ∧ before s t then some (matched s t) else none

theorem fullCert_accepted_one : check (blowup 1) discount (fullCert 1) = true := by decide +kernel

/-- **At `m = 1` the lower bound `(m + 1)(2m + 1) = 6` is attained.** -/
theorem fullCert_listed_one : (listedTriples (fullCert 1)).card = 6 := by decide +kernel

theorem fullCert_close (m : ℕ) :
    ∀ s t : St m, middle s.1 → middle t.1 → s ≠ t → (fullCert m).kernel s t < discount / 2 :=
  close_of_le fun _ _ _ _ => le_rfl

/-! ## The measurement -/

/-- The quotient's check: the leak chain's certificate. -/
theorem quotientWork : prefixpointWork leak discount correct = (364, 304, 116, 15) := by
  decide +kernel

/-- **The work of the class certificate's checker, for every size.** -/
theorem classWork_blowup (m : ℕ) :
    classWork discount (classCert m) =
      (364, 16 * (m + 1) * (m + 1) + 304, 20 * (m + 1) + 116, 64 * (m + 1) * (m + 1) + 15) := by
  unfold classWork
  rw [lumpWork_eq]
  change _ + prefixpointWork leak discount correct = _
  rw [quotientWork]
  simp only [card_St, Fintype.card_unit, Fintype.card_fin, one_mul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp <;> ring

/-- **The size of the class certificate, for every size.** -/
theorem classSize_blowup (m : ℕ) : classSize (classCert m) = 4 * m + 56 := by
  have listed : (listedTriples correct).card = 1 := by decide +kernel
  simp only [classSize, prefixpointSize, classCert, card_St, Fintype.card_unit, Fintype.card_fin,
    listed]
  ring

/-- **Four times smaller**: for every `m ≥ 1`, every accepted prefixpoint certificate proving bounds as
strong as the class certificate's at the once-or-leaky pairs is at least four times larger. -/
theorem four_times_smaller {m : ℕ} (one_le : 1 ≤ m) {cert : Prefixpoint Unit (St m)}
    (accepted : check (blowup m) discount cert = true)
    (le : ∀ s t : St m, middle s.1 → middle t.1 → cert.kernel s t ≤ exactKernel s.1 t.1) :
    4 * classSize (classCert m) ≤ prefixpointSize cert := by
  have bound := prefixpointSize_ge accepted discount_pos (close_of_le le)
  rw [classSize_blowup]
  have m2 : 1 ≤ m * m := Nat.mul_le_mul one_le one_le
  have m3 : 1 ≤ m * m * m := Nat.mul_le_mul m2 one_le
  have m4 : 1 ≤ m * m * m * m := Nat.mul_le_mul m3 one_le
  nlinarith

/-- **Four times cheaper**: for every `m ≥ 1` and every accepted prefixpoint certificate, all the work of
the class certificate's checker is at most a quarter of the products and additions of the incumbent
checker. -/
theorem four_times_cheaper {m : ℕ} (one_le : 1 ≤ m) {cert : Prefixpoint Unit (St m)}
    (accepted : check (blowup m) discount cert = true) :
    4 * (classWork discount (classCert m)).all ≤
      (prefixpointWork (blowup m) discount cert).1 + (prefixpointWork (blowup m) discount cert).2.1 := by
  obtain ⟨products, additions⟩ := prefixpointWork_lower accepted
  rw [card_St, Fintype.card_unit, one_mul, show 4 * (m + 1) - 1 = 4 * m + 3 by omega] at products
  rw [card_St, Fintype.card_unit, one_mul, show 4 * (m + 1) - 1 = 4 * m + 3 by omega] at additions
  rw [classWork_blowup]
  simp only [Work.all]
  have m2 : 1 ≤ m * m := Nat.mul_le_mul one_le one_le
  have m3 : 1 ≤ m * m * m := Nat.mul_le_mul m2 one_le
  have m4 : 1 ≤ m * m * m * m := Nat.mul_le_mul m3 one_le
  nlinarith

/-- **Without classes it loses**: at `m = 0` every class has one state; the class certificate does the
quotient's check plus the lumping check, and is larger. -/
theorem loses_without_classes :
    check (blowup 0) discount (fullCert 0) = true ∧
      prefixpointWork (blowup 0) discount (fullCert 0) = (364, 304, 116, 15) ∧
      classWork discount (classCert 0) = (364, 320, 136, 79) ∧
      prefixpointSize (fullCert 0) = 32 ∧ classSize (classCert 0) = 56 :=
  ⟨by decide +kernel, by decide +kernel, by rw [classWork_blowup], by decide +kernel,
    classSize_blowup 0⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Family
