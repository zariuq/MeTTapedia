import Mettapedia.Cybernetics.DistinctionCalculus.Examples
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Contexts, evidence, distinctions and resonance

Goertzel, *Hyperseed in the d-Calculus*, ch. 3. Statement identifiers `HS3.*`
are the chapter's.

* **Evidence** (`HS3.Evidence`). A p-bit `(p, n) ∈ [0, 1]²` keeps support and
  opposition apart (`PBit`). The knowledge order is the componentwise order and
  its join is evidence accumulation; the truth order reverses opposition.
  Support, opposition, conflict and determinacy are monotone in the knowledge
  order and indeterminacy is antitone; bias is monotone in the truth order and
  neither monotone nor antitone in the knowledge order. Material implication
  sends `T ⇒ F` to `F` (the source example says `B`); designating support one,
  modus ponens fails and explosion fails. On real p-bits, the square embeds in
  the library's evidence quantale (`PBit.toBinaryEvidence`): orders, join,
  negation, the gain product and the four corners agree, and the unit gain
  `(1, 1)` is the corner `Both`.
* **Contexts and report geometry** (`HS3.Context`, `HS3.ReportDistance`,
  `HS3.01`, `HS3.02`). A context carries a sampling measure, an observer and
  reports on weighted probes (`Context`). The squared report distance is
  rational on rational reports (`reportDistSq`); its root is a real distance
  (`reportDistance`), the Euclidean distance of a weighted embedding
  (`dist_reportVector`). It is a pseudometric bounded by one
  (`reportTolerance_metric`), zero exactly on equal reports at positive-weight
  probes, and its zero quotient is a metric space (`ReportQuotient`); equal
  reports need not be equal tokens. Without the root the construction fails:
  the squared distance is not a pseudometric (`squaredReport_not_metric`). Report
  edits move distances by at most the two report movements
  (`report_edit_bound`).
* **Closure** (`HS3.03`, `HS3.04`). The shortest-path closure is the least
  metric tolerance above a raw one; it is monotone and idempotent, and any
  verified metric bound below the raw kernel survives it. Its cost in expected
  indistinction is the bracket of the added similarity.
* **The carrier bridge.** An order-preserving ring map between fields carries
  tolerances, measures, metric coherence, expected indistinction and the
  shortest-path closure (`Tolerance.mapValues`), so every rational computation
  is also a real one.

Positive and negative examples follow each concept.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus

universe u v w

/-! ## The evidence square -/

/-- **The evidence square** (`HS3.Evidence`): a p-bit `(p, n)` records support
`p` and opposition `n` to one claim, each in `[0, 1]`, with no constraint
`p + n = 1`. Values lie in a linearly ordered field, rational unless given. -/
@[ext]
structure PBit (R : Type := ℚ) [Field R] [LinearOrder R] [IsStrictOrderedRing R] where
  support : R
  opposition : R
  support_nonneg : 0 ≤ support
  support_le_one : support ≤ 1
  opposition_nonneg : 0 ≤ opposition
  opposition_le_one : opposition ≤ 1

namespace PBit

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The knowledge order is componentwise; its join `v ∨ₖ w` is evidence
accumulation, the componentwise maximum (`HS3.Evidence`). -/
instance : SemilatticeSup (PBit R) where
  le v w := v.support ≤ w.support ∧ v.opposition ≤ w.opposition
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1, h.2.trans k.2⟩
  le_antisymm _ _ h k := PBit.ext (le_antisymm h.1 k.1) (le_antisymm h.2 k.2)
  sup v w := ⟨max v.support w.support, max v.opposition w.opposition,
    le_max_of_le_left v.support_nonneg, max_le v.support_le_one w.support_le_one,
    le_max_of_le_left v.opposition_nonneg, max_le v.opposition_le_one w.opposition_le_one⟩
  le_sup_left _ _ := ⟨le_max_left _ _, le_max_left _ _⟩
  le_sup_right _ _ := ⟨le_max_right _ _, le_max_right _ _⟩
  sup_le _ _ _ h k := ⟨max_le h.1 k.1, max_le h.2 k.2⟩

theorem le_def {v w : PBit R} :
    v ≤ w ↔ v.support ≤ w.support ∧ v.opposition ≤ w.opposition := Iff.rfl

@[simp] theorem sup_support (v w : PBit R) : (v ⊔ w).support = max v.support w.support := rfl

@[simp] theorem sup_opposition (v w : PBit R) :
    (v ⊔ w).opposition = max v.opposition w.opposition := rfl

/-- The truth order: more support and less opposition. -/
def TruthLE (v w : PBit R) : Prop := v.support ≤ w.support ∧ w.opposition ≤ v.opposition

/-- Negation `N(p, n) = (n, p)`. -/
def neg (v : PBit R) : PBit R :=
  ⟨v.opposition, v.support, v.opposition_nonneg, v.opposition_le_one, v.support_nonneg,
    v.support_le_one⟩

/-- The corner `T = (1, 0)`. -/
def supported : PBit R := ⟨1, 0, zero_le_one, le_rfl, le_rfl, zero_le_one⟩

/-- The corner `F = (0, 1)`. -/
def opposed : PBit R := ⟨0, 1, le_rfl, zero_le_one, zero_le_one, le_rfl⟩

/-- The corner `B = (1, 1)`: conflict. -/
def both : PBit R := ⟨1, 1, zero_le_one, le_rfl, zero_le_one, le_rfl⟩

/-- The corner `N = (0, 0)`: no evidence. -/
def neither : PBit R := ⟨0, 0, le_rfl, zero_le_one, le_rfl, zero_le_one⟩

/-- Truth conjunction `(min p p', max n n')`. -/
def truthAnd (v w : PBit R) : PBit R :=
  ⟨min v.support w.support, max v.opposition w.opposition,
    le_min v.support_nonneg w.support_nonneg, min_le_of_left_le v.support_le_one,
    le_max_of_le_left v.opposition_nonneg, max_le v.opposition_le_one w.opposition_le_one⟩

/-- Truth disjunction `(max p p', min n n')`. -/
def truthOr (v w : PBit R) : PBit R :=
  ⟨max v.support w.support, min v.opposition w.opposition,
    le_max_of_le_left v.support_nonneg, max_le v.support_le_one w.support_le_one,
    le_min v.opposition_nonneg w.opposition_nonneg, min_le_of_left_le v.opposition_le_one⟩

/-- Bias `p − n`. -/
def bias (v : PBit R) : R := v.support - v.opposition

/-- Conflict `min (p, n)`. -/
def conflict (v : PBit R) : R := min v.support v.opposition

/-- Determinacy `max (p, n)`. -/
def determinacy (v : PBit R) : R := max v.support v.opposition

/-- Indeterminacy `1 − max (p, n)`. -/
def indeterminacy (v : PBit R) : R := 1 - max v.support v.opposition

theorem support_mono : Monotone (support : PBit R → R) := fun _ _ h => h.1

theorem opposition_mono : Monotone (opposition : PBit R → R) := fun _ _ h => h.2

theorem conflict_mono : Monotone (conflict : PBit R → R) := fun _ _ h => min_le_min h.1 h.2

theorem determinacy_mono : Monotone (determinacy : PBit R → R) := fun _ _ h => max_le_max h.1 h.2

theorem indeterminacy_anti : Antitone (indeterminacy : PBit R → R) :=
  fun _ _ h => sub_le_sub_left (max_le_max h.1 h.2) 1

/-- Bias is monotone in the truth order. -/
theorem bias_mono_of_truthLE {v w : PBit R} (h : v.TruthLE w) : v.bias ≤ w.bias :=
  sub_le_sub h.1 h.2

/-- **Bias is not monotone in the knowledge order**: adding opposition lowers it. -/
theorem bias_not_monotone : ¬ Monotone (bias : PBit R → R) := by
  intro mono
  have := mono (show (neither : PBit R) ≤ opposed from ⟨le_rfl, zero_le_one⟩)
  norm_num [bias, neither, opposed] at this

/-- **Bias is not antitone in the knowledge order**: adding support raises it. -/
theorem bias_not_antitone : ¬ Antitone (bias : PBit R → R) := by
  intro anti
  have := anti (show (neither : PBit R) ≤ supported from ⟨zero_le_one, le_rfl⟩)
  norm_num [bias, neither, supported] at this

/-- Material implication `v ⇒ₘ w = N v ∨ₜ w`. -/
def materialImpl (v w : PBit R) : PBit R := truthOr (neg v) w

/-- **`T ⇒ₘ F = F`**, not `B` as the source example states. -/
theorem materialImpl_supported_opposed : materialImpl (supported : PBit R) opposed = opposed := by
  ext <;> simp [materialImpl, truthOr, neg, supported, opposed]

/-- Designated values: full support. -/
def Designated (v : PBit R) : Prop := v.support = 1

/-- **Modus ponens fails** for material implication with support-one
designation: `B` and `B ⇒ₘ F` are designated, `F` is not. -/
theorem modus_ponens_fails :
    Designated (both : PBit R) ∧ Designated (materialImpl (both : PBit R) opposed) ∧
      ¬ Designated (opposed : PBit R) := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp [Designated, materialImpl, truthOr, neg, both, opposed]

/-- **Non-explosion**: `A = B` makes `A` and `N A` designated, but not `F`. -/
theorem not_explosive :
    Designated (both : PBit R) ∧ Designated (neg (both : PBit R)) ∧
      ¬ Designated (opposed : PBit R) := by
  refine ⟨rfl, rfl, ?_⟩
  simp [Designated, opposed]

/-- The gain product `(k₊ l₊, k₋ l₋)`, the tensor of the canonical p-bit
quantale (a channel gain, not an assertion). -/
def gain (v w : PBit R) : PBit R :=
  ⟨v.support * w.support, v.opposition * w.opposition,
    mul_nonneg v.support_nonneg w.support_nonneg,
    mul_le_one₀ v.support_le_one w.support_nonneg w.support_le_one,
    mul_nonneg v.opposition_nonneg w.opposition_nonneg,
    mul_le_one₀ v.opposition_le_one w.opposition_nonneg w.opposition_le_one⟩

/-! ### The real evidence square inside the library's evidence quantale -/

open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit (pTrue pFalse pBoth pNeither)

/-- A real p-bit as library evidence: both coordinates as extended
nonnegative reals. -/
noncomputable def toBinaryEvidence (v : PBit ℝ) : BinaryEvidence :=
  ⟨ENNReal.ofReal v.support, ENNReal.ofReal v.opposition⟩

/-- The knowledge order is the evidence order. -/
theorem toBinaryEvidence_le_iff {v w : PBit ℝ} :
    v.toBinaryEvidence ≤ w.toBinaryEvidence ↔ v ≤ w := by
  rw [BinaryEvidence.le_def, le_def]
  simp only [toBinaryEvidence, ENNReal.ofReal_le_ofReal_iff w.support_nonneg,
    ENNReal.ofReal_le_ofReal_iff w.opposition_nonneg]

theorem toBinaryEvidence_injective : Function.Injective (toBinaryEvidence) := fun _ _ h =>
  le_antisymm (toBinaryEvidence_le_iff.mp h.le) (toBinaryEvidence_le_iff.mp h.ge)

/-- Evidence accumulation is the evidence join. -/
theorem toBinaryEvidence_sup (v w : PBit ℝ) :
    (v ⊔ w).toBinaryEvidence = v.toBinaryEvidence ⊔ w.toBinaryEvidence := by
  apply BinaryEvidence.ext'
  · exact ENNReal.ofReal_mono.map_max
  · exact ENNReal.ofReal_mono.map_max

/-- Negation is the evidence swap. -/
theorem toBinaryEvidence_neg (v : PBit ℝ) :
    v.neg.toBinaryEvidence = BinaryEvidence.swap v.toBinaryEvidence := rfl

/-- The gain product is the evidence tensor. -/
theorem toBinaryEvidence_gain (v w : PBit ℝ) :
    (gain v w).toBinaryEvidence = v.toBinaryEvidence * w.toBinaryEvidence := by
  rw [BinaryEvidence.tensor_def]
  apply BinaryEvidence.ext'
  · exact ENNReal.ofReal_mul v.support_nonneg
  · exact ENNReal.ofReal_mul v.opposition_nonneg

/-- The four corners are the library's four corners. -/
theorem toBinaryEvidence_corners :
    (supported : PBit ℝ).toBinaryEvidence = pTrue ∧ (opposed : PBit ℝ).toBinaryEvidence = pFalse ∧
      (both : PBit ℝ).toBinaryEvidence = pBoth ∧ (neither : PBit ℝ).toBinaryEvidence = pNeither := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BinaryEvidence.ext' <;>
    simp [toBinaryEvidence, supported, opposed, both, neither, pTrue, pFalse, pBoth, pNeither]

/-- **One pair, two roles**: the unit gain `(1, 1)` of the quantale is the
assertion corner `Both`. -/
theorem unit_gain_is_both :
    (both : PBit ℝ).toBinaryEvidence = BinaryEvidence.one ∧ BinaryEvidence.one = pBoth ∧
      ∀ v : PBit ℝ, gain v both = v := by
  refine ⟨?_, rfl, fun v => ?_⟩
  · apply BinaryEvidence.ext' <;> simp [toBinaryEvidence, both, BinaryEvidence.one]
  · ext <;> simp [gain, both]

/-! ### Half the squared distance of two p-bits -/

/-- `‖v − w‖² / 2`, the square of the one-probe report distance. -/
def distSq (v w : PBit R) : R :=
  ((v.support - w.support) ^ 2 + (v.opposition - w.opposition) ^ 2) / 2

theorem distSq_nonneg (v w : PBit R) : 0 ≤ v.distSq w := by
  unfold distSq
  positivity

theorem sq_sub_le_one {a b : R} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (a - b) ^ 2 ≤ 1 := by
  nlinarith [mul_nonneg ha hb, mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hb1)]

theorem distSq_le_one (v w : PBit R) : v.distSq w ≤ 1 := by
  have := sq_sub_le_one v.support_nonneg v.support_le_one w.support_nonneg w.support_le_one
  have := sq_sub_le_one v.opposition_nonneg v.opposition_le_one w.opposition_nonneg
    w.opposition_le_one
  unfold distSq
  linarith

theorem distSq_comm (v w : PBit R) : v.distSq w = w.distSq v := by
  unfold distSq
  ring

@[simp] theorem distSq_self (v : PBit R) : v.distSq v = 0 := by simp [distSq]

theorem distSq_eq_zero_iff {v w : PBit R} : v.distSq w = 0 ↔ v = w := by
  constructor
  · intro zero
    have hp : (v.support - w.support) ^ 2 = 0 := by
      unfold distSq at zero
      nlinarith [sq_nonneg (v.support - w.support), sq_nonneg (v.opposition - w.opposition)]
    have hn : (v.opposition - w.opposition) ^ 2 = 0 := by
      unfold distSq at zero
      nlinarith [sq_nonneg (v.support - w.support), sq_nonneg (v.opposition - w.opposition)]
    exact PBit.ext (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hp))
      (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hn))
  · rintro rfl
    simp

/-- The coordinates of a p-bit, support first. -/
def coord (v : PBit R) : Bool → R
  | true => v.support
  | false => v.opposition

end PBit

/-! ## Contexts and the report geometry -/

/-- **A context record** (`HS3.Context`): `C = (X, μ, α; Q, ρ, e)`, a sampling
measure and an observer on a finite token carrier, and reports `e(x, q)` on
finitely many weighted probes. A raw context keeps an observer unrelated to its
reports; a report-generated one uses `reportTolerance`. -/
structure Context (X : Type u) (Q : Type v) [Fintype X] [Fintype Q] (R : Type := ℚ) [Field R]
    [LinearOrder R] [IsStrictOrderedRing R] where
  mass : Distribution X R
  observer : Tolerance X R
  probes : Distribution Q R
  report : X → Q → PBit R

section ReportSquares

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {X : Type u} {Q : Type v} [Fintype Q]

/-- **The squared report distance** (`HS3.ReportDistance`, before its root):
`½ Σ_q ρ(q) [(p_x(q) − p_y(q))² + (n_x(q) − n_y(q))²]`. Rational on rational
reports. -/
def reportDistSq (ρ : Distribution Q R) (e : X → Q → PBit R) (x y : X) : R :=
  ∑ q, ρ.weight q * (e x q).distSq (e y q)

variable (ρ : Distribution Q R) (e : X → Q → PBit R)

theorem reportDistSq_nonneg (x y : X) : 0 ≤ reportDistSq ρ e x y :=
  Finset.sum_nonneg fun q _ => mul_nonneg (ρ.nonnegative q) (PBit.distSq_nonneg _ _)

theorem reportDistSq_le_one (x y : X) : reportDistSq ρ e x y ≤ 1 := by
  calc reportDistSq ρ e x y ≤ ∑ q, ρ.weight q * 1 :=
        Finset.sum_le_sum fun q _ =>
          mul_le_mul_of_nonneg_left (PBit.distSq_le_one _ _) (ρ.nonnegative q)
    _ = 1 := by simp [ρ.normalized]

theorem reportDistSq_comm (x y : X) : reportDistSq ρ e x y = reportDistSq ρ e y x := by
  simp only [reportDistSq, PBit.distSq_comm]

@[simp] theorem reportDistSq_self (x : X) : reportDistSq ρ e x x = 0 := by
  simp [reportDistSq]

/-- Zero squared report distance is equality of the reports at every probe of
positive weight. -/
theorem reportDistSq_eq_zero_iff (x y : X) :
    reportDistSq ρ e x y = 0 ↔ ∀ q, 0 < ρ.weight q → e x q = e y q := by
  rw [reportDistSq, Finset.sum_eq_zero_iff_of_nonneg fun q _ =>
    mul_nonneg (ρ.nonnegative q) (PBit.distSq_nonneg _ _)]
  constructor
  · intro zero q positive
    have := zero q (Finset.mem_univ q)
    exact PBit.distSq_eq_zero_iff.mp ((mul_eq_zero.mp this).resolve_left positive.ne')
  · intro same q _
    by_cases positive : 0 < ρ.weight q
    · simp [same q positive]
    · simp [le_antisymm (not_lt.mp positive) (ρ.nonnegative q)]

/-- Equality of reports at every probe of positive weight. -/
def reportSetoid : Setoid X where
  r x y := ∀ q, 0 < ρ.weight q → e x q = e y q
  iseqv := ⟨fun _ _ _ => rfl, fun h q hq => (h q hq).symm,
    fun h k q hq => (h q hq).trans (k q hq)⟩

/-- The tolerance `1 − d²` of the squared report distance. It is a tolerance;
it is **not** a metric observer in general (`squaredReport_not_metric`). -/
def squaredReportTolerance : Tolerance X R where
  similarity x y := 1 - reportDistSq ρ e x y
  nonnegative x y := sub_nonneg.mpr (reportDistSq_le_one ρ e x y)
  bounded x y := sub_le_self _ (reportDistSq_nonneg ρ e x y)
  reflexive x := by simp
  symmetric x y := by rw [reportDistSq_comm]

end ReportSquares

section ReportDistance

variable {X : Type u} {Q : Type v} [Fintype Q]
variable (ρ : Distribution Q ℝ) (e : X → Q → PBit ℝ)

/-- **The report distance** (`HS3.ReportDistance`): the root of
`reportDistSq`. -/
noncomputable def reportDistance (x y : X) : ℝ := √(reportDistSq ρ e x y)

/-- The weighted embedding `x ↦ (√(ρ(q)/2) p_x(q), √(ρ(q)/2) n_x(q))_q`. -/
noncomputable def reportVector (x : X) : EuclideanSpace ℝ (Q × Bool) :=
  WithLp.toLp 2 fun i => √(ρ.weight i.1 / 2) * (e x i.1).coord i.2

/-- The distance of two embedded profiles, possibly of different reports. -/
theorem dist_reportVector_cross (e' : X → Q → PBit ℝ) (x y : X) :
    dist (reportVector ρ e x) (reportVector ρ e' y) =
      √(∑ q, ρ.weight q * (e x q).distSq (e' y q)) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  have half : 0 ≤ ρ.weight q / 2 := div_nonneg (ρ.nonnegative q) zero_le_two
  rw [Fintype.sum_bool]
  simp only [reportVector, PiLp.toLp_apply, Real.dist_eq, sq_abs, PBit.coord, PBit.distSq]
  rw [← mul_sub, ← mul_sub, mul_pow, mul_pow, Real.sq_sqrt half]
  ring

/-- **The report distance is a Euclidean distance** (proof of `HS3.01`). -/
theorem dist_reportVector (x y : X) :
    dist (reportVector ρ e x) (reportVector ρ e y) = reportDistance ρ e x y :=
  dist_reportVector_cross ρ e e x y

theorem reportDistance_nonneg (x y : X) : 0 ≤ reportDistance ρ e x y := Real.sqrt_nonneg _

theorem reportDistance_le_one (x y : X) : reportDistance ρ e x y ≤ 1 := by
  rw [reportDistance, Real.sqrt_le_one]
  exact reportDistSq_le_one ρ e x y

theorem reportDistance_comm (x y : X) : reportDistance ρ e x y = reportDistance ρ e y x := by
  rw [reportDistance, reportDistSq_comm]
  rfl

@[simp] theorem reportDistance_self (x : X) : reportDistance ρ e x x = 0 := by
  simp [reportDistance]

theorem reportDistance_sq (x y : X) : reportDistance ρ e x y ^ 2 = reportDistSq ρ e x y :=
  Real.sq_sqrt (reportDistSq_nonneg ρ e x y)

/-- Zero report distance is equality of reports at every positive-weight probe. -/
theorem reportDistance_eq_zero_iff (x y : X) :
    reportDistance ρ e x y = 0 ↔ ∀ q, 0 < ρ.weight q → e x q = e y q := by
  rw [reportDistance, Real.sqrt_eq_zero (reportDistSq_nonneg ρ e x y)]
  exact reportDistSq_eq_zero_iff ρ e x y

/-- The report-generated observer `α_e = 1 − d_e`. -/
noncomputable def reportTolerance : Tolerance X ℝ where
  similarity x y := 1 - reportDistance ρ e x y
  nonnegative x y := sub_nonneg.mpr (reportDistance_le_one ρ e x y)
  bounded x y := sub_le_self _ (reportDistance_nonneg ρ e x y)
  reflexive x := by simp
  symmetric x y := by rw [reportDistance_comm]

@[simp] theorem reportTolerance_distance (x y : X) :
    (reportTolerance ρ e).distance x y = reportDistance ρ e x y := by
  simp [Tolerance.distance, reportTolerance]

/-- **Reports generate a metric observer** (`HS3.01`): the report distance obeys
the triangle inequality. -/
theorem reportTolerance_metric : (reportTolerance ρ e).Metric := by
  intro x y z
  simp only [reportTolerance_distance, ← dist_reportVector]
  exact dist_triangle _ _ _

/-- Equal reports are exactly the zero kernel of the report observer. -/
theorem reportSetoid_eq_zeroSetoid :
    reportSetoid ρ e = (reportTolerance ρ e).zeroSetoid (reportTolerance_metric ρ e) := by
  ext x y
  change _ ↔ (reportTolerance ρ e).distance x y = 0
  rw [reportTolerance_distance, reportDistance_eq_zero_iff]
  rfl

theorem reportSetoid_iff (x y : X) :
    reportSetoid ρ e x y ↔ ∀ q, 0 < ρ.weight q → e x q = e y q := Iff.rfl

theorem reportVector_eq_iff (x y : X) :
    reportVector ρ e x = reportVector ρ e y ↔ reportSetoid ρ e x y := by
  rw [← dist_eq_zero, dist_reportVector, reportSetoid_iff, reportDistance_eq_zero_iff]

/-- The tokens up to equal reports. -/
def ReportQuotient : Type u := Quotient (reportSetoid ρ e)

/-- The class of a token in the report quotient. -/
noncomputable def ReportQuotient.mk (x : X) : ReportQuotient ρ e := Quotient.mk _ x

/-- The embedding of the report quotient. -/
noncomputable def ReportQuotient.vector : ReportQuotient ρ e → EuclideanSpace ℝ (Q × Bool) :=
  Quotient.lift (reportVector ρ e) fun x y related => (reportVector_eq_iff ρ e x y).mpr related

theorem ReportQuotient.vector_injective : Function.Injective (ReportQuotient.vector ρ e) := by
  intro a b same
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  exact Quotient.sound ((reportVector_eq_iff ρ e _ _).mp same)

/-- **The report quotient is a metric space** (`HS3.01`). -/
noncomputable instance : MetricSpace (ReportQuotient ρ e) :=
  MetricSpace.induced (ReportQuotient.vector ρ e) (ReportQuotient.vector_injective ρ e)
    inferInstance

theorem ReportQuotient.dist_mk (x y : X) :
    dist (ReportQuotient.mk ρ e x) (ReportQuotient.mk ρ e y) = reportDistance ρ e x y :=
  dist_reportVector ρ e x y

/-- Two tokens have the same class exactly when their reports agree at every
probe of positive weight. -/
theorem ReportQuotient.mk_eq_mk_iff (x y : X) :
    ReportQuotient.mk ρ e x = ReportQuotient.mk ρ e y ↔ ∀ q, 0 < ρ.weight q → e x q = e y q :=
  Quotient.eq.trans (reportSetoid_iff ρ e x y)

/-! ### Report edits (`HS3.02`) -/

/-- The movement `ε_x = (½ Σ_q ρ(q) ‖e'(x, q) − e(x, q)‖²)^{1/2}` of the reports
of `x`. -/
noncomputable def reportMovement (e' : X → Q → PBit ℝ) (x : X) : ℝ :=
  √(∑ q, ρ.weight q * (e' x q).distSq (e x q))

theorem reportMovement_eq_dist (e' : X → Q → PBit ℝ) (x : X) :
    reportMovement ρ e e' x = dist (reportVector ρ e' x) (reportVector ρ e x) :=
  (dist_reportVector_cross ρ e' e x x).symm

/-- **Report-edit bound** (`HS3.02`): `|d_{e'}(x, y) − d_e(x, y)| ≤ ε_x + ε_y`. -/
theorem report_edit_bound (e' : X → Q → PBit ℝ) (x y : X) :
    |reportDistance ρ e' x y - reportDistance ρ e x y| ≤
      reportMovement ρ e e' x + reportMovement ρ e e' y := by
  rw [← dist_reportVector, ← dist_reportVector, reportMovement_eq_dist, reportMovement_eq_dist,
    ← Real.dist_eq]
  exact dist_dist_dist_le _ _ _ _

/-- The sup form of `HS3.02`: a uniform movement bound `m` moves every
similarity by at most `2 m`. -/
theorem report_edit_sup_bound (e' : X → Q → PBit ℝ) {m : ℝ}
    (moves : ∀ x, reportMovement ρ e e' x ≤ m) (x y : X) :
    |(reportTolerance ρ e').similarity x y - (reportTolerance ρ e).similarity x y| ≤ 2 * m := by
  have bound := report_edit_bound ρ e e' x y
  have hx := moves x
  have hy := moves y
  simp only [reportTolerance]
  rw [show 1 - reportDistance ρ e' x y - (1 - reportDistance ρ e x y) =
      -(reportDistance ρ e' x y - reportDistance ρ e x y) by ring, abs_neg]
  linarith

end ReportDistance

/-! ## The bracket -/

namespace Distribution

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type u} [Fintype V]

/-- A kernel that adds a row term and a column term averages to twice the
expectation of the term. -/
theorem pairAverage_add_rows (p : Distribution V R) (g : V → R) :
    p.pairAverage (fun x y => g x + g y) = 2 * ∑ x, p.weight x * g x := by
  have hs : ∑ y, p.weight y = 1 := p.normalized
  simp only [pairAverage, mul_add, Finset.sum_add_distrib]
  have first : ∑ x, ∑ y, p.weight x * p.weight y * g x = ∑ x, p.weight x * g x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (fun y => p.weight x * p.weight y * g x) = fun y => p.weight y * (p.weight x * g x)
      from funext fun y => by ring, ← Finset.sum_mul, hs, one_mul]
  have second : ∑ x, ∑ y, p.weight x * p.weight y * g y = ∑ y, p.weight y * g y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show (fun x => p.weight x * p.weight y * g y) = fun x => p.weight x * (p.weight y * g y)
      from funext fun x => by ring, ← Finset.sum_mul, hs, one_mul]
  rw [first, second]
  ring

/-- The bracket of a kernel is bounded by the bracket of its absolute value. -/
theorem abs_pairAverage_le (p : Distribution V R) (f : V → V → R) :
    |p.pairAverage f| ≤ p.pairAverage fun x y => |f x y| := by
  unfold pairAverage
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (mul_nonneg (p.nonnegative x) (p.nonnegative y))]

/-- Logical entropy, the expected distinction, is antitone in the observer. -/
theorem distinction_anti (p : Distribution V R) {a b : Tolerance V R} (coarser : a.Extends b) :
    p.distinction b ≤ p.distinction a := by
  rw [distinction_eq_one_sub, distinction_eq_one_sub]
  linarith [p.closure_increases_graphtropy coarser]

end Distribution

/-- The bracket form of `HS3.02`: `|⟨μ|α_{e'} − α_e|μ⟩| ≤ 2 Σ_x μ(x) ε_x`. -/
theorem report_edit_bracket_bound {X : Type u} {Q : Type v} [Fintype X] [Fintype Q]
    (μ : Distribution X ℝ) (ρ : Distribution Q ℝ) (e e' : X → Q → PBit ℝ) :
    |μ.graphtropy (reportTolerance ρ e') - μ.graphtropy (reportTolerance ρ e)| ≤
      2 * ∑ x, μ.weight x * reportMovement ρ e e' x := by
  rw [Distribution.graphtropy, Distribution.graphtropy, ← Distribution.pairAverage_sub,
    ← Distribution.pairAverage_add_rows]
  refine (μ.abs_pairAverage_le _).trans (μ.pairAverage_mono fun x y => ?_)
  have bound := report_edit_bound ρ e e' x y
  simp only [reportTolerance]
  rw [show 1 - reportDistance ρ e' x y - (1 - reportDistance ρ e x y) =
      -(reportDistance ρ e' x y - reportDistance ρ e x y) by ring, abs_neg]
  exact bound

/-! ## Metric closure (`HS3.03`, `HS3.04`) -/

section Closure

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Metric closure is monotone** (`HS3.03`). -/
theorem shortestTolerance_mono {a b : Tolerance V R} (coarser : a.Extends b) :
    (shortestTolerance a).Extends (shortestTolerance b) :=
  (shortestTolerance_is_least a).2.2 _
    (fun x y => (coarser x y).trans (shortestTolerance_extends b x y))
    (shortestTolerance_metric b)

/-- **Metric closure is idempotent** (`HS3.03`). -/
theorem shortestTolerance_idem (a : Tolerance V R) :
    (shortestTolerance (shortestTolerance a)).similarity = (shortestTolerance a).similarity :=
  leastMetricExtension_unique (shortestTolerance_is_least _)
    (metric_leastMetricExtension _ (shortestTolerance_metric a))

/-- **Metric closure** (`HS3.03`): `α♭` is the least metric tolerance above `α`
(so `d♭` is the greatest pseudometric below `d`), monotone and idempotent. -/
theorem metric_closure (a : Tolerance V R) :
    LeastMetricExtension a (shortestTolerance a) ∧
      (∀ b : Tolerance V R, a.Extends b →
        (shortestTolerance a).Extends (shortestTolerance b)) ∧
      (shortestTolerance (shortestTolerance a)).similarity = (shortestTolerance a).similarity :=
  ⟨shortestTolerance_is_least a, fun _ coarser => shortestTolerance_mono coarser,
    shortestTolerance_idem a⟩

/-- **The cost of closure** (`HS3.04`): `g(μ, α♭) − g(μ, α) = ⟨μ|σ|μ⟩ ≥ 0` with
`σ = α♭ − α`. -/
theorem closure_cost (p : Distribution V R) (a : Tolerance V R) :
    p.graphtropy (shortestTolerance a) - p.graphtropy a =
        p.pairAverage (fun x y => (shortestTolerance a).similarity x y - a.similarity x y) ∧
      0 ≤ p.pairAverage (fun x y => (shortestTolerance a).similarity x y - a.similarity x y) :=
  ⟨(p.pairAverage_sub _ _).symm,
    p.pairAverage_nonnegative fun x y => sub_nonneg.mpr (shortestTolerance_extends a x y)⟩

end Closure

/-- **A verified report bound survives closure** (`HS3.03` with `HS3.01`): if
the report distance lies below a raw distinction kernel, it lies below the
closure. -/
theorem report_bound_survives_closure {X : Type u} {Q : Type v} [Fintype X] [DecidableEq X]
    [Fintype Q] (ρ : Distribution Q ℝ) (e : X → Q → PBit ℝ) {a : Tolerance X ℝ}
    (below : a.Extends (reportTolerance ρ e)) :
    (shortestTolerance a).Extends (reportTolerance ρ e) :=
  (shortestTolerance_is_least a).2.2 _ below (reportTolerance_metric ρ e)

/-! ## The carrier bridge -/

section Bridge

variable {R S : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Field S] [LinearOrder S] [IsStrictOrderedRing S]
variable {V : Type u}

/-- A tolerance carried along an order-preserving ring map of fields. -/
def Tolerance.mapValues (f : R →+* S) (mono : Monotone f) (a : Tolerance V R) : Tolerance V S where
  similarity x y := f (a.similarity x y)
  nonnegative x y := by simpa using mono (a.nonnegative x y)
  bounded x y := by simpa using mono (a.bounded x y)
  reflexive x := by simp [a.reflexive]
  symmetric x y := by rw [a.symmetric]

theorem Tolerance.distance_mapValues (f : R →+* S) (mono : Monotone f) (a : Tolerance V R)
    (x y : V) : (a.mapValues f mono).distance x y = f (a.distance x y) := by
  simp [Tolerance.distance, Tolerance.mapValues]

/-- Metric coherence is preserved and reflected. -/
theorem Tolerance.metric_mapValues_iff (f : R →+* S) (mono : Monotone f) (a : Tolerance V R) :
    (a.mapValues f mono).Metric ↔ a.Metric := by
  have strict : StrictMono f := mono.strictMono_of_injective f.injective
  simp only [Tolerance.Metric, Tolerance.distance_mapValues, ← map_add, strict.le_iff_le]

/-- A measure carried along an order-preserving ring map of fields. -/
def Distribution.mapValues [Fintype V] (f : R →+* S) (mono : Monotone f)
    (p : Distribution V R) : Distribution V S where
  weight x := f (p.weight x)
  nonnegative x := by simpa using mono (p.nonnegative x)
  normalized := by rw [← map_sum, p.normalized, map_one]

/-- Expected indistinction commutes with the carrier map. -/
theorem Distribution.graphtropy_mapValues [Fintype V] (f : R →+* S) (mono : Monotone f)
    (p : Distribution V R) (a : Tolerance V R) :
    (p.mapValues f mono).graphtropy (a.mapValues f mono) = f (p.graphtropy a) := by
  simp [Distribution.graphtropy, Distribution.pairAverage, Distribution.mapValues,
    Tolerance.mapValues, map_sum, map_mul]

theorem pathCost_mapValues [DecidableEq V] (f : R →+* S) (mono : Monotone f)
    (a : Tolerance V R) : ∀ p : List V, pathCost (a.mapValues f mono) p = f (pathCost a p)
  | [] => by simp [pathCost]
  | [_] => by simp [pathCost]
  | x :: y :: rest => by
      rw [pathCost, pathCost, pathCost_mapValues f mono a (y :: rest), combine, combine,
        mono.map_min, map_one, map_add, Tolerance.distance_mapValues]

/-- **The closure commutes with the carrier map**: a rational closure is also
the real closure. -/
theorem shortestTolerance_mapValues [Fintype V] [DecidableEq V] (f : R →+* S)
    (mono : Monotone f) (a : Tolerance V R) :
    (shortestTolerance (a.mapValues f mono)).similarity =
      ((shortestTolerance a).mapValues f mono).similarity := by
  funext x y
  have distance : shortestDistance (a.mapValues f mono) x y = f (shortestDistance a x y) := by
    rw [shortestDistance, shortestDistance,
      Finset.apply_inf'_eq_inf'_comp _ f fun r s => mono.map_min]
    exact Finset.inf'_congr _ rfl fun p _ => pathCost_mapValues f mono a p
  change 1 - shortestDistance (a.mapValues f mono) x y = f (1 - shortestDistance a x y)
  rw [distance, map_sub, map_one]

/-- The rational-to-real carrier map. -/
noncomputable abbrev ratToReal : ℚ →+* ℝ := Rat.castHom ℝ

theorem ratToReal_mono : Monotone ratToReal := fun _ _ h => Rat.cast_le.mpr h

end Bridge

/-! ## Path laws and finite propagation closure (`HS3.Accumulate`, `HS3.08`) -/

/-- **A path law** on `[0, 1]`: how a gain composes with the signal it
transmits. It is associative, has unit gain `1`, is monotone and never
amplifies. Max-product transmission, max-min bottlenecks and max-Łukasiewicz
metric composition are path laws (`productLaw`, `bottleneckLaw`,
`lukasiewiczLaw`). -/
structure PathLaw (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] where
  op : R → R → R
  op_assoc : ∀ {a b c : R}, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 ≤ c → c ≤ 1 →
    op (op a b) c = op a (op b c)
  op_one : ∀ {a : R}, 0 ≤ a → a ≤ 1 → op a 1 = a
  one_op : ∀ {x : R}, 0 ≤ x → x ≤ 1 → op 1 x = x
  zero_op : ∀ {x : R}, 0 ≤ x → x ≤ 1 → op 0 x = 0
  op_mono : ∀ {a a' x x' : R}, 0 ≤ a → 0 ≤ x → a ≤ a' → x ≤ x' → op a x ≤ op a' x'
  op_le : ∀ {a x : R}, a ≤ 1 → 0 ≤ x → op a x ≤ x
  op_nonneg : ∀ {a x : R}, 0 ≤ a → 0 ≤ x → 0 ≤ op a x

/-- Gains between channels, target first, each in `[0, 1]`. -/
structure GainMatrix (Γ : Type u) (R : Type := ℚ) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] where
  gain : Γ → Γ → R
  gain_nonneg : ∀ γ δ, 0 ≤ gain γ δ
  gain_le_one : ∀ γ δ, gain γ δ ≤ 1

namespace PathLaw

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Max-product transmission. -/
def productLaw : PathLaw R where
  op a x := a * x
  op_assoc _ _ _ _ _ _ := mul_assoc _ _ _
  op_one _ _ := mul_one _
  one_op _ _ := one_mul _
  zero_op _ _ := zero_mul _
  op_mono ha hx haa hxx := mul_le_mul haa hxx hx (ha.trans haa)
  op_le ha hx := mul_le_of_le_one_left hx ha
  op_nonneg ha hx := mul_nonneg ha hx

/-- Max-min bottleneck transmission. -/
def bottleneckLaw : PathLaw R where
  op a x := min a x
  op_assoc _ _ _ _ _ _ := min_assoc _ _ _
  op_one _ ha := min_eq_left ha
  one_op _ hx := min_eq_right hx
  zero_op hx _ := min_eq_left hx
  op_mono _ _ haa hxx := min_le_min haa hxx
  op_le _ _ := min_le_right _ _
  op_nonneg ha hx := le_min ha hx

/-- Max-Łukasiewicz composition `max 0 (a + x − 1)`, the similarity form of
adding distances. -/
def lukasiewiczLaw : PathLaw R where
  op a x := max 0 (a + x - 1)
  op_assoc {a b c} ha ha1 hb hb1 hc hc1 := by
    simp only [max_def]
    split_ifs <;> linarith
  op_one ha _ := by simp [ha]
  one_op hx _ := by simp [hx]
  zero_op _ hx := by simp [hx]
  op_mono _ _ haa hxx := max_le_max le_rfl (by linarith)
  op_le ha hx := max_le hx (by linarith)
  op_nonneg _ _ := le_max_left _ _

end PathLaw

section Propagation

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {Γ : Type u} (L : PathLaw R) (A : GainMatrix Γ R)

/-- The signal delivered to the first channel of a walk `γ₀ ← γ₁ ← ⋯ ← γₖ`
(target first) from the value at its last channel. -/
def walkSignal (u : Γ → R) : List Γ → R
  | [] => 0
  | [γ] => u γ
  | γ :: δ :: rest => L.op (A.gain γ δ) (walkSignal u (δ :: rest))

/-- Values in the unit cube. -/
def InCube (u : Γ → R) : Prop := ∀ γ, 0 ≤ u γ ∧ u γ ≤ 1

variable {L A}

theorem walkSignal_mem {u : Γ → R} (hu : InCube u) :
    ∀ p : List Γ, 0 ≤ walkSignal L A u p ∧ walkSignal L A u p ≤ 1
  | [] => ⟨le_rfl, zero_le_one⟩
  | [γ] => hu γ
  | γ :: δ :: rest => by
      have ih := walkSignal_mem hu (δ :: rest)
      exact ⟨L.op_nonneg (A.gain_nonneg γ δ) ih.1,
        (L.op_le (A.gain_le_one γ δ) ih.1).trans ih.2⟩

theorem walkSignal_cons_cons (u : Γ → R) (γ δ : Γ) (rest : List Γ) :
    walkSignal L A u (γ :: δ :: rest) = L.op (A.gain γ δ) (walkSignal L A u (δ :: rest)) := rfl

/-- A prefix transmits monotonically. -/
theorem walkSignal_prefix_mono {u : Γ → R} (hu : InCube u) (x : Γ) (t₁ t₂ : List Γ)
    (le : walkSignal L A u (x :: t₁) ≤ walkSignal L A u (x :: t₂)) :
    ∀ pre : List Γ, walkSignal L A u (pre ++ x :: t₁) ≤ walkSignal L A u (pre ++ x :: t₂)
  | [] => le
  | [p] => L.op_mono (A.gain_nonneg p x) (walkSignal_mem hu _).1 le_rfl le
  | p :: q :: pre => L.op_mono (A.gain_nonneg p q) (walkSignal_mem hu _).1 le_rfl
      (walkSignal_prefix_mono hu x t₁ t₂ le (q :: pre))

/-- A loop never strengthens what it returns to. -/
theorem walkSignal_loop_le {u : Γ → R} (hu : InCube u) (x : Γ) (post : List Γ) :
    ∀ (mid : List Γ) (y : Γ), walkSignal L A u (y :: (mid ++ x :: post)) ≤
      walkSignal L A u (x :: post)
  | [], y => L.op_le (A.gain_le_one y x) (walkSignal_mem hu _).1
  | m :: mid, y => (L.op_le (A.gain_le_one y m) (walkSignal_mem hu _).1).trans
      (walkSignal_loop_le hu x post mid m)

theorem walkSignal_drop_cycle {u : Γ → R} (hu : InCube u) (pre mid post : List Γ) (x : Γ) :
    walkSignal L A u (pre ++ x :: mid ++ x :: post) ≤ walkSignal L A u (pre ++ x :: post) := by
  have shape : pre ++ x :: mid ++ x :: post = pre ++ x :: (mid ++ x :: post) := by
    simp [List.append_assoc]
  rw [shape]
  exact walkSignal_prefix_mono hu x _ _ (walkSignal_loop_le hu x post mid x) pre

/-- **Cycle removal**: every walk is dominated by a simple walk with the same
ends. -/
theorem exists_simple_walk_ge [DecidableEq Γ] {u : Γ → R} (hu : InCube u) (p : List Γ) :
    ∃ q, q.Nodup ∧ q.head? = p.head? ∧ q.getLast? = p.getLast? ∧
      walkSignal L A u p ≤ walkSignal L A u q ∧ (p ≠ [] → q ≠ []) := by
  generalize hlen : p.length = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
      subst hlen
      by_cases hnd : p.Nodup
      · exact ⟨p, hnd, rfl, rfl, le_rfl, id⟩
      · obtain ⟨x, pre, mid, post, hp⟩ := exists_double_occurrence hnd
        set p' := pre ++ x :: post
        have hlt : p'.length < p.length := by
          rw [hp]
          simp [p', List.length_append]
        obtain ⟨q, hqNodup, hqHead, hqLast, hqSig, hqNe⟩ := ih p'.length hlt p' rfl
        refine ⟨q, hqNodup, ?_, ?_, ?_, fun _ => hqNe (by simp [p'])⟩
        · rw [hqHead, hp]; exact head?_drop_cycle pre mid post x
        · rw [hqLast, hp]; exact getLast?_drop_cycle pre mid post x
        · rw [hp]
          exact (walkSignal_drop_cycle hu pre mid post x).trans hqSig

/-- Under a vector closed under transmission, every walk delivers at most the
vector's value at its first channel. -/
theorem walkSignal_le_of_closed {u v : Γ → R} (hu : InCube u) (above : ∀ γ, u γ ≤ v γ)
    (closed : ∀ γ δ, L.op (A.gain γ δ) (v δ) ≤ v γ) :
    ∀ (γ : Γ) (rest : List Γ), walkSignal L A u (γ :: rest) ≤ v γ
  | γ, [] => above γ
  | γ, δ :: rest => (L.op_mono (A.gain_nonneg γ δ) (walkSignal_mem hu _).1 le_rfl
      (walkSignal_le_of_closed hu above closed δ rest)).trans (closed γ δ)

variable (L A)
variable [Fintype Γ] [Nonempty Γ]

/-- **Fixed-gain accumulation** (`HS3.Accumulate`): the retained update
`F_A(u) = u ∨ (A ⊙ u)`, with `⊙` the maximum over sources of the path law. -/
def accumulate (u : Γ → R) (γ : Γ) : R :=
  max (u γ) (Finset.univ.sup' Finset.univ_nonempty fun δ => L.op (A.gain γ δ) (u δ))

variable {L A}

theorem accumulate_apply (u : Γ → R) (γ : Γ) : accumulate L A u γ =
    max (u γ) (Finset.univ.sup' Finset.univ_nonempty fun δ => L.op (A.gain γ δ) (u δ)) := rfl

/-- The update is inflationary. -/
theorem le_accumulate (u : Γ → R) (γ : Γ) : u γ ≤ accumulate L A u γ := le_max_left _ _

/-- The update keeps the unit cube. -/
theorem accumulate_mem {u : Γ → R} (hu : InCube u) : InCube (accumulate L A u) := by
  intro γ
  refine ⟨(hu γ).1.trans (le_accumulate u γ), max_le (hu γ).2 ?_⟩
  exact Finset.sup'_le _ _ fun δ _ => (L.op_le (A.gain_le_one γ δ) (hu δ).1).trans (hu δ).2

/-- The update is monotone in the knowledge order. -/
theorem accumulate_mono {u v : Γ → R} (hu : InCube u) (le : ∀ γ, u γ ≤ v γ) (γ : Γ) :
    accumulate L A u γ ≤ accumulate L A v γ :=
  max_le_max (le γ) (Finset.sup'_le _ _ fun δ _ =>
    (L.op_mono (A.gain_nonneg γ δ) (hu δ).1 le_rfl (le δ)).trans
      (Finset.le_sup' (fun δ => L.op (A.gain γ δ) (v δ)) (Finset.mem_univ δ)))

theorem iterate_mem {u : Γ → R} (hu : InCube u) (t : ℕ) : InCube ((accumulate L A)^[t] u) := by
  induction t with
  | zero => exact hu
  | succ t ih => rw [Function.iterate_succ_apply']; exact accumulate_mem ih

theorem le_iterate (u : Γ → R) (t : ℕ) (γ : Γ) : u γ ≤ (accumulate L A)^[t] u γ := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (le_accumulate _ γ)

theorem iterate_mono_steps {u : Γ → R} {s t : ℕ} (le : s ≤ t) (γ : Γ) :
    (accumulate L A)^[s] u γ ≤ (accumulate L A)^[t] u γ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact le_iterate _ k γ

/-- Every walk with at most `t` steps delivers at most the `t`-th iterate. -/
theorem walkSignal_le_iterate {u : Γ → R} (hu : InCube u) :
    ∀ (t : ℕ) (γ : Γ) (rest : List Γ), rest.length ≤ t →
      walkSignal L A u (γ :: rest) ≤ (accumulate L A)^[t] u γ
  | 0, γ, [], _ => le_rfl
  | t + 1, γ, [], _ => le_iterate u (t + 1) γ
  | t + 1, γ, δ :: rest, short => by
      rw [Function.iterate_succ_apply', walkSignal_cons_cons]
      refine le_max_of_le_right ?_
      refine le_trans ?_ (Finset.le_sup' (fun δ => L.op (A.gain γ δ)
        ((accumulate L A)^[t] u δ)) (Finset.mem_univ δ))
      exact L.op_mono (A.gain_nonneg γ δ) (walkSignal_mem hu _).1 le_rfl
        (walkSignal_le_iterate hu t δ rest (Nat.le_of_succ_le_succ short))

/-- The `t`-th iterate is delivered by a walk with at most `t` steps. -/
theorem iterate_eq_walkSignal (u : Γ → R) :
    ∀ (t : ℕ) (γ : Γ), ∃ rest : List Γ, rest.length ≤ t ∧
      (accumulate L A)^[t] u γ = walkSignal L A u (γ :: rest)
  | 0, γ => ⟨[], le_rfl, rfl⟩
  | t + 1, γ => by
      rw [Function.iterate_succ_apply', accumulate_apply]
      rcases le_total ((accumulate L A)^[t] u γ)
          (Finset.univ.sup' Finset.univ_nonempty fun δ =>
            L.op (A.gain γ δ) ((accumulate L A)^[t] u δ)) with first | second
      · rw [max_eq_right first]
        obtain ⟨δ, -, attained⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
          fun δ => L.op (A.gain γ δ) ((accumulate L A)^[t] u δ)
        obtain ⟨rest, short, eq⟩ := iterate_eq_walkSignal u t δ
        refine ⟨δ :: rest, Nat.succ_le_succ short, ?_⟩
        rw [attained, walkSignal_cons_cons, eq]
      · rw [max_eq_left second]
        obtain ⟨rest, short, eq⟩ := iterate_eq_walkSignal u t γ
        exact ⟨rest, short.trans (Nat.le_succ t), eq⟩

variable (L A) in
/-- **The propagation closure** `u* = A* ⊙ u⁰`: the iterate after `|Γ| − 1`
rounds. -/
def propagationClosure (u : Γ → R) : Γ → R := (accumulate L A)^[Fintype.card Γ - 1] u

/-- Every walk, of any length, delivers at most the closure. -/
theorem walkSignal_le_closure [DecidableEq Γ] {u : Γ → R} (hu : InCube u) (γ : Γ)
    (rest : List Γ) : walkSignal L A u (γ :: rest) ≤ propagationClosure L A u γ := by
  obtain ⟨q, nodup, head, -, ge, nonempty⟩ := exists_simple_walk_ge (L := L) (A := A) hu
    (γ :: rest)
  obtain ⟨γ', rest', rfl⟩ := List.exists_cons_of_ne_nil (nonempty (List.cons_ne_nil γ rest))
  simp only [List.head?_cons, Option.some.injEq] at head
  subst head
  have length : rest'.length ≤ Fintype.card Γ - 1 := by
    have := nodup.length_le_card
    simp only [List.length_cons] at this
    omega
  exact ge.trans (walkSignal_le_iterate hu _ γ' rest' length)

/-- **Finite propagation closure** (`HS3.08`): iteration stabilizes after
`|Γ| − 1` rounds. -/
theorem iterate_stable [DecidableEq Γ] {u : Γ → R} (hu : InCube u) {t : ℕ}
    (late : Fintype.card Γ - 1 ≤ t) : (accumulate L A)^[t] u = propagationClosure L A u := by
  funext γ
  refine le_antisymm ?_ (iterate_mono_steps late γ)
  obtain ⟨rest, -, eq⟩ := iterate_eq_walkSignal (L := L) (A := A) u t γ
  rw [eq]
  exact walkSignal_le_closure hu γ rest

theorem le_propagationClosure (u : Γ → R) (γ : Γ) : u γ ≤ propagationClosure L A u γ :=
  le_iterate u _ γ

/-- The closure is a fixed point of the update. -/
theorem accumulate_propagationClosure [DecidableEq Γ] {u : Γ → R} (hu : InCube u) :
    accumulate L A (propagationClosure L A u) = propagationClosure L A u := by
  rw [propagationClosure, ← Function.iterate_succ_apply' (accumulate L A)]
  exact iterate_stable hu (Nat.le_succ _)

/-- **Leastness** (`HS3.08`): the closure lies below every `v ≥ u⁰` closed under
transmission, `A ⊙ v ≤ v`. -/
theorem propagationClosure_le {u v : Γ → R} (hu : InCube u) (above : ∀ γ, u γ ≤ v γ)
    (closed : ∀ γ δ, L.op (A.gain γ δ) (v δ) ≤ v γ) (γ : Γ) :
    propagationClosure L A u γ ≤ v γ := by
  obtain ⟨rest, -, eq⟩ := iterate_eq_walkSignal (L := L) (A := A) u (Fintype.card Γ - 1) γ
  rw [propagationClosure, eq]
  exact walkSignal_le_of_closed hu above closed γ rest

/-- The closure is the least fixed point of the update above `u⁰`. -/
theorem propagationClosure_least_fixed {u v : Γ → R} (hu : InCube u) (above : ∀ γ, u γ ≤ v γ)
    (fixed : accumulate L A v = v) (γ : Γ) : propagationClosure L A u γ ≤ v γ := by
  refine propagationClosure_le hu above (fun γ δ => ?_) γ
  calc L.op (A.gain γ δ) (v δ)
      ≤ Finset.univ.sup' Finset.univ_nonempty (fun δ => L.op (A.gain γ δ) (v δ)) :=
        Finset.le_sup' (fun δ => L.op (A.gain γ δ) (v δ)) (Finset.mem_univ δ)
    _ ≤ accumulate L A v γ := le_max_right _ _
    _ = v γ := by rw [fixed]

end Propagation

/-! ## The bracket for signed vectors, attention moves and task costs -/

section Bracket

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **The bracket** `⟨μ|K|ν⟩ = Σ_{x,y} μ(x) K(x, y) ν(y)` (`HS3.Bracket`), for
signed vectors. `Distribution.pairAverage` is its diagonal case on a probability
vector. -/
def bracket {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] (μ : X → R) (K : X → Y → R)
    (ν : Y → R) : R :=
  ∑ x, ∑ y, μ x * K x y * ν y

variable {V : Type u} [Fintype V]

theorem pairAverage_eq_bracket (p : Distribution V R) (f : V → V → R) :
    p.pairAverage f = bracket p.weight f p.weight :=
  Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem bracket_comm (μ ν : V → R) (K : V → V → R) (symm : ∀ x y, K x y = K y x) :
    bracket μ K ν = bracket ν K μ := by
  unfold bracket
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [symm]
  ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The bracket is linear in the kernel: `g(μ, α + tK) = g(μ, α) + t ⟨μ|K|μ⟩`, so
the observer derivative is `⟨μ|K|μ⟩`. -/
theorem bracket_kernel_add (μ ν : V → R) (α K : V → V → R) (t : R) :
    bracket μ (fun x y => α x y + t * K x y) ν = bracket μ α ν + t * bracket μ K ν := by
  unfold bracket
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **A finite attention step** keeps its quadratic term: for a symmetric kernel,
`g(μ + η) − g(μ) = 2⟨η|α|μ⟩ + ⟨η|α|η⟩`. -/
theorem bracket_add_sub (μ η : V → R) (K : V → V → R) (symm : ∀ x y, K x y = K y x) :
    bracket (μ + η) K (μ + η) - bracket μ K μ = 2 * bracket η K μ + bracket η K η := by
  have split : bracket (μ + η) K (μ + η) =
      bracket μ K μ + bracket μ K η + bracket η K μ + bracket η K η := by
    unfold bracket
    simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  rw [split, bracket_comm μ η K symm]
  ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The attention derivative: `g(μ + tη) = g(μ) + 2t⟨η|α|μ⟩ + t²⟨η|α|η⟩`. -/
theorem bracket_add_smul (μ η : V → R) (K : V → V → R) (symm : ∀ x y, K x y = K y x) (t : R) :
    bracket (μ + t • η) K (μ + t • η) =
      bracket μ K μ + t * (2 * bracket η K μ) + t ^ 2 * bracket η K η := by
  have step := bracket_add_sub μ (t • η) K symm
  have scale₁ : bracket (t • η) K μ = t * bracket η K μ := by
    unfold bracket
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  have scale₂ : bracket (t • η) K (t • η) = t ^ 2 * bracket η K η := by
    unfold bracket
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [scale₁, scale₂] at step
  linear_combination step

/-- The derivative of expected indistinction along an attention direction is
`2⟨η|α|μ⟩`. -/
theorem hasDerivAt_bracket_attention (μ η : V → ℝ) (K : V → V → ℝ)
    (symm : ∀ x y, K x y = K y x) :
    HasDerivAt (fun t : ℝ => bracket (μ + t • η) K (μ + t • η)) (2 * bracket η K μ) 0 := by
  have expand : (fun t : ℝ => bracket (μ + t • η) K (μ + t • η)) =
      fun t => bracket μ K μ + t * (2 * bracket η K μ) + t ^ 2 * bracket η K η :=
    funext fun t => bracket_add_smul μ η K symm t
  rw [expand]
  have linear : HasDerivAt (fun t : ℝ => t * (2 * bracket η K μ)) (1 * (2 * bracket η K μ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).mul_const _
  have affine : HasDerivAt (fun t : ℝ => bracket μ K μ + t * (2 * bracket η K μ))
      (1 * (2 * bracket η K μ)) 0 := HasDerivAt.const_add _ linear
  have square : HasDerivAt (fun t : ℝ => t ^ 2 * bracket η K η)
      ((2 : ℕ) * (0 : ℝ) ^ (2 - 1) * bracket η K η) 0 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const _
  exact HasDerivAt.congr_deriv (HasDerivAt.add affine square) (by norm_num)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **The hive bracket** (ch. 3, §5.2): sampling a context with weight `λ_i` and
then a token with `μ_i`, expected indistinction splits into local (`i = j`) and
cross-context (`i ≠ j`) brackets. -/
theorem hive_bracket {κ : Type v} [Fintype κ] {X : κ → Type w} [∀ i, Fintype (X i)]
    (weight : κ → R) (μ : ∀ i, X i → R) (K : (Σ i, X i) → (Σ i, X i) → R) :
    bracket (fun z => weight z.1 * μ z.1 z.2) K (fun z => weight z.1 * μ z.1 z.2) =
      ∑ i, ∑ j, weight i * weight j * bracket (μ i) (fun x y => K ⟨i, x⟩ ⟨j, y⟩) (μ j) := by
  unfold bracket
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Two samples are drawn with replacement: `g ≥ Σ_x μ(x)²`. -/
theorem sum_sq_le_graphtropy (p : Distribution V R) (a : Tolerance V R) :
    ∑ x, p.weight x ^ 2 ≤ p.graphtropy a := by
  unfold Distribution.graphtropy Distribution.pairAverage
  refine Finset.sum_le_sum fun x _ => ?_
  have single := Finset.single_le_sum (f := fun y => p.weight x * p.weight y * a.similarity x y)
    (fun y _ => mul_nonneg (mul_nonneg (p.nonnegative x) (p.nonnegative y)) (a.nonnegative x y))
    (Finset.mem_univ x)
  simpa [a.reflexive, sq] using single

/-- The finest observer attains the diagonal baseline. -/
theorem graphtropy_discrete [DecidableEq V] (p : Distribution V R) :
    p.graphtropy (Tolerance.ofReport id R) = ∑ x, p.weight x ^ 2 := by
  simp [Distribution.graphtropy, Distribution.pairAverage, Tolerance.ofReport, sq]

/-- Task blindness `B = ⟨μ| d_* (1 − d_C) |μ⟩`: task-relevant distinctions the
observer discounts. -/
def taskBlindness (p : Distribution V R) (task observer : Tolerance V R) : R :=
  p.pairAverage fun x y => task.distance x y * observer.similarity x y

/-- Unnecessary detail `U = ⟨μ| d_C (1 − d_*) |μ⟩`: distinctions the observer
keeps where the task discounts them. -/
def unnecessaryDetail (p : Distribution V R) (task observer : Tolerance V R) : R :=
  p.pairAverage fun x y => observer.distance x y * task.similarity x y

/-- **`B − U = h_* − h_C`** exactly. -/
theorem taskBlindness_sub_unnecessaryDetail (p : Distribution V R) (task observer : Tolerance V R) :
    taskBlindness p task observer - unnecessaryDetail p task observer =
      p.distinction task - p.distinction observer := by
  unfold taskBlindness unnecessaryDetail Distribution.distinction
  rw [← p.pairAverage_sub, ← p.pairAverage_sub]
  congr 1
  funext x y
  simp only [Tolerance.distance]
  ring

end Bracket

/-! ## Translations: pullback against pushforward (`HS3.05`) -/

namespace Distribution

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type u} {W : Type v} {X : Type w} [Fintype V] [Fintype W] [DecidableEq W]

/-- The pushforward `f_# μ`. -/
def pushforward (p : Distribution V R) (f : V → W) : Distribution W R where
  weight y := ∑ x with f x = y, p.weight x
  nonnegative _ := Finset.sum_nonneg fun x _ => p.nonnegative x
  normalized := by rw [Finset.sum_fiberwise]; exact p.normalized

theorem sum_comp_eq_pushforward (p : Distribution V R) (f : V → W) (g : W → R) :
    ∑ x, p.weight x * g (f x) = ∑ y, (p.pushforward f).weight y * g y := by
  rw [← Finset.sum_fiberwise Finset.univ f fun x => p.weight x * g (f x)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [pushforward, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]

/-- **Pullback against pushforward** (the chapter's accounting identity):
`⟨μ|f*β|μ⟩ = ⟨f_#μ|β|f_#μ⟩`. -/
theorem pairAverage_comp (p : Distribution V R) (f : V → W) (K : W → W → R) :
    p.pairAverage (fun x x' => K (f x) (f x')) = (p.pushforward f).pairAverage K := by
  unfold pairAverage
  calc ∑ x, ∑ x', p.weight x * p.weight x' * K (f x) (f x')
      = ∑ x, p.weight x * ∑ y', (p.pushforward f).weight y' * K (f x) y' := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← sum_comp_eq_pushforward p f fun y' => K (f x) y', Finset.mul_sum]
        exact Finset.sum_congr rfl fun x' _ => by ring
    _ = ∑ y, (p.pushforward f).weight y * ∑ y', (p.pushforward f).weight y' * K y y' :=
        sum_comp_eq_pushforward p f fun y => ∑ y', (p.pushforward f).weight y' * K y y'
    _ = ∑ y, ∑ y', (p.pushforward f).weight y * (p.pushforward f).weight y' * K y y' := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y' _ => by ring

theorem graphtropy_pullback (p : Distribution V R) (b : Tolerance W R) (f : V → W) :
    p.graphtropy (b.pullback f) = (p.pushforward f).graphtropy b :=
  p.pairAverage_comp f b.similarity

/-- **Weighted distortion composes with the transported measure** (`HS3.05`):
`Δ_μ(g ∘ f) ≤ Δ_μ(f) + Δ_{f_# μ}(g)`. -/
theorem distortion_comp_pushforward (p : Distribution V R) (a : Tolerance V R) (b : Tolerance W R)
    (c : Tolerance X R) (f : V → W) (g : W → X) :
    p.distortion a c (g ∘ f) ≤ p.distortion a b f + (p.pushforward f).distortion b c g := by
  have bound := p.distortion_comp_le a b c f g
  rwa [p.pairAverage_comp f fun y y' => |c.similarity (g y) (g y') - b.similarity y y'|] at bound

/-- **A translation moves expected indistinction by at most its weighted
distortion** (`HS3.05`): `|g(μ, α_C) − g(f_# μ, α_D)| ≤ Δ_μ(f)`. -/
theorem abs_graphtropy_sub_le_distortion (p : Distribution V R) (a : Tolerance V R)
    (b : Tolerance W R) (f : V → W) :
    |p.graphtropy a - (p.pushforward f).graphtropy b| ≤ p.distortion a b f := by
  rw [← graphtropy_pullback, abs_sub_comm, graphtropy, graphtropy, ← pairAverage_sub]
  exact p.abs_pairAverage_le _

end Distribution

/-- **The pointwise defect composes** (`HS3.05`): `δ_{g f} ≤ δ_f + f* δ_g`. -/
theorem pointDefect_comp {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {V : Type u} {W : Type v} {X : Type w} (a : Tolerance V R) (b : Tolerance W R)
    (c : Tolerance X R) (f : V → W) (g : W → X) (x x' : V) :
    |c.similarity (g (f x)) (g (f x')) - a.similarity x x'| ≤
      |b.similarity (f x) (f x') - a.similarity x x'| +
        |c.similarity (g (f x)) (g (f x')) - b.similarity (f x) (f x')| := by
  have := abs_sub_le (c.similarity (g (f x)) (g (f x'))) (b.similarity (f x) (f x'))
    (a.similarity x x')
  linarith

/-- **Report preservation certifies geometry** (`HS3.05`): when two contexts
share probes, a translation that moves each report by at most `ε_x` moves each
pair similarity by at most `ε_x + ε_{x'}`. -/
theorem translation_report_bound {X : Type u} {Y : Type v} {Q : Type w} [Fintype Q]
    (ρ : Distribution Q ℝ) (source : X → Q → PBit ℝ) (target : Y → Q → PBit ℝ) (f : X → Y)
    (x x' : X) :
    |(reportTolerance ρ target).similarity (f x) (f x') - (reportTolerance ρ source).similarity x x'| ≤
      reportMovement ρ source (fun x => target (f x)) x +
        reportMovement ρ source (fun x => target (f x)) x' := by
  have bound := report_edit_bound ρ source (fun x => target (f x)) x x'
  simp only [reportTolerance]
  rw [show 1 - reportDistance ρ target (f x) (f x') - (1 - reportDistance ρ source x x') =
      -(reportDistance ρ (fun x => target (f x)) x x' - reportDistance ρ source x x') from by
    simp only [reportDistance, reportDistSq]; ring, abs_neg]
  exact bound

/-! ## What changes when a context changes (`HS3.10`) -/

section Dynamics

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Exact balance** (`HS3.10`): with `μ' = T_# μ`,
`g(μ', α') − g(μ, α) = P − L`, where `P = ⟨μ|T*α − α|μ⟩` is the movement term
and `L = ⟨μ'|α − α'|μ'⟩` the observer edit. -/
theorem balance (p : Distribution V R) (T : V → V) (old new : Tolerance V R) :
    (p.pushforward T).graphtropy new - p.graphtropy old =
      p.pairAverage (fun x y => old.similarity (T x) (T y) - old.similarity x y) -
        (p.pushforward T).pairAverage (fun x y => old.similarity x y - new.similarity x y) := by
  rw [← p.pairAverage_comp T fun x y => old.similarity x y - new.similarity x y,
    Distribution.graphtropy, ← p.pairAverage_comp T new.similarity, Distribution.graphtropy,
    p.pairAverage_sub, p.pairAverage_sub]
  ring

/-- A pointwise refinement `α' ≤ α` makes the observer term nonnegative. -/
theorem observerEdit_nonneg_of_refines (p : Distribution V R) (T : V → V) {old new : Tolerance V R}
    (refines : new.Extends old) :
    0 ≤ (p.pushforward T).pairAverage (fun x y => old.similarity x y - new.similarity x y) :=
  (p.pushforward T).pairAverage_nonnegative fun x y => sub_nonneg.mpr (refines x y)

omit [DecidableEq V] in
/-- **Movement bound** (`HS3.10`): for a metric observer,
`|P| ≤ ⟨μ| |π_T| |μ⟩ ≤ 2 Σ_x μ(x) d(x, T x)`. -/
theorem movement_bound (p : Distribution V R) (T : V → V) (a : Tolerance V R) (metric : a.Metric) :
    |p.pairAverage (fun x y => a.similarity (T x) (T y) - a.similarity x y)| ≤
        p.pairAverage (fun x y => |a.similarity (T x) (T y) - a.similarity x y|) ∧
      p.pairAverage (fun x y => |a.similarity (T x) (T y) - a.similarity x y|) ≤
        2 * ∑ x, p.weight x * a.distance x (T x) := by
  refine ⟨p.abs_pairAverage_le _, ?_⟩
  rw [← p.pairAverage_add_rows]
  refine p.pairAverage_mono fun x y => ?_
  have t₁ := metric (T x) x (T y)
  have t₂ := metric x y (T y)
  have t₃ := metric x (T x) y
  have t₄ := metric (T x) (T y) y
  have s₁ := a.distance_symm (T x) x
  have s₂ := a.distance_symm (T y) y
  simp only [Tolerance.distance] at *
  rw [abs_le]
  constructor <;> linarith

end Dynamics

/-- **The combined bound** (`HS3.10`): for report observers before and after an
edit, `|g(μ', α_{e'}) − g(μ, α_e)| ≤ 2 Σ μ(x) d_e(x, T x) + 2 Σ μ'(x) ε_x`. -/
theorem combined_speed_bound {X : Type u} {Q : Type v} [Fintype X] [DecidableEq X] [Fintype Q]
    (μ : Distribution X ℝ) (T : X → X) (ρ : Distribution Q ℝ) (e e' : X → Q → PBit ℝ) :
    |(μ.pushforward T).graphtropy (reportTolerance ρ e') - μ.graphtropy (reportTolerance ρ e)| ≤
      2 * ∑ x, μ.weight x * reportDistance ρ e x (T x) +
        2 * ∑ x, (μ.pushforward T).weight x * reportMovement ρ e e' x := by
  have stay := balance μ T (reportTolerance ρ e) (reportTolerance ρ e)
  simp only [sub_self, Distribution.pairAverage_const, sub_zero] at stay
  have move := movement_bound μ T (reportTolerance ρ e) (reportTolerance_metric ρ e)
  simp only [reportTolerance_distance] at move
  have edit := report_edit_bracket_bound (μ.pushforward T) ρ e e'
  calc |(μ.pushforward T).graphtropy (reportTolerance ρ e') - μ.graphtropy (reportTolerance ρ e)|
      = |((μ.pushforward T).graphtropy (reportTolerance ρ e') -
            (μ.pushforward T).graphtropy (reportTolerance ρ e)) +
          ((μ.pushforward T).graphtropy (reportTolerance ρ e) -
            μ.graphtropy (reportTolerance ρ e))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by rw [stay]; linarith [move.1.trans move.2])

/-! ## Resonance expressed through distinctions -/

namespace PBit

section Embedding

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **The resonance embedding** `z(p, n) = (p − n, p + n − 1)`: the source's
complex amplitude `b + i c` in real coordinates. -/
def embed (v : PBit R) : R × R := (v.support - v.opposition, v.support + v.opposition - 1)

/-- No information is lost: `p = (1 + b + c)/2`, `n = (1 − b + c)/2`. -/
theorem decode_embed (v : PBit R) :
    v.support = (1 + v.embed.1 + v.embed.2) / 2 ∧
      v.opposition = (1 - v.embed.1 + v.embed.2) / 2 := by
  constructor <;> simp only [embed] <;> ring

theorem embed_injective : Function.Injective (embed : PBit R → R × R) := fun v w same =>
  PBit.ext (by rw [(decode_embed v).1, (decode_embed w).1, same])
    (by rw [(decode_embed v).2, (decode_embed w).2, same])

/-- The image lies in the diamond `|b| + |c| ≤ 1`. -/
theorem embed_mem_diamond (v : PBit R) : |v.embed.1| + |v.embed.2| ≤ 1 := by
  have := v.support_nonneg
  have := v.support_le_one
  have := v.opposition_nonneg
  have := v.opposition_le_one
  simp only [embed]
  rcases abs_cases (v.support - v.opposition) with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;>
    rcases abs_cases (v.support + v.opposition - 1) with ⟨h₂, _⟩ | ⟨h₂, _⟩ <;>
    linarith

/-- Every point of the diamond is the image of a p-bit. -/
theorem exists_embed_eq {b c : R} (diamond : |b| + |c| ≤ 1) : ∃ v : PBit R, v.embed = (b, c) := by
  have bounds : -1 ≤ b + c ∧ b + c ≤ 1 ∧ -1 ≤ c - b ∧ c - b ≤ 1 := by
    rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;> rcases abs_cases c with ⟨hc, _⟩ | ⟨hc, _⟩ <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨h₁, h₂, h₃, h₄⟩ := bounds
  refine ⟨⟨(1 + b + c) / 2, (1 - b + c) / 2, by linarith, by linarith, by linarith,
    by linarith⟩, ?_⟩
  simp only [embed, Prod.mk.injEq]
  constructor <;> ring

/-- The four corners go to the four vertices of the diamond. -/
theorem embed_corners :
    (supported : PBit R).embed = (1, 0) ∧ (opposed : PBit R).embed = (-1, 0) ∧
      (both : PBit R).embed = (0, 1) ∧ (neither : PBit R).embed = (0, -1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [embed, supported, opposed, both, neither]

/-- The central p-bit `(½, ½)`. -/
def central : PBit R := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The second coordinate is total evidence minus one, not conflict**: `T`
and the central p-bit share `c = 0` but differ in conflict. -/
theorem embed_second_not_conflict :
    (supported : PBit R).embed.2 = (central : PBit R).embed.2 ∧
      (supported : PBit R).conflict ≠ (central : PBit R).conflict := by
  constructor
  · norm_num [embed, supported, central]
  · norm_num [conflict, supported, central]

/-- The antipodal map `J(p, n) = (1 − p, 1 − n)`: phase opposition. -/
def antipode (v : PBit R) : PBit R :=
  ⟨1 - v.support, 1 - v.opposition, sub_nonneg.mpr v.support_le_one,
    sub_le_self _ v.support_nonneg, sub_nonneg.mpr v.opposition_le_one,
    sub_le_self _ v.opposition_nonneg⟩

/-- Negation reflects the embedding: `z(N v) = (−b, c)`. -/
theorem embed_neg (v : PBit R) : v.neg.embed = (-v.embed.1, v.embed.2) := by
  simp only [embed, neg, Prod.mk.injEq]
  constructor <;> ring

/-- The antipode is the antipodal map: `z(J v) = (−b, −c)`. -/
theorem embed_antipode (v : PBit R) : v.antipode.embed = (-v.embed.1, -v.embed.2) := by
  simp only [embed, antipode, Prod.mk.injEq]
  constructor <;> ring

/-- **Logical reversal is not phase opposition**: `N` fixes `B` and `N`, while
`J` exchanges them. -/
theorem neg_fixes_antipode_swaps :
    neg (both : PBit R) = both ∧ neg (neither : PBit R) = neither ∧
      antipode (both : PBit R) = neither ∧ antipode (neither : PBit R) = both := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp [neg, antipode, both, neither]

/-- **The embedding scales distance** (`HS3.06`):
`‖z v − z w‖² = 2 ‖v − w‖² = 4 d_P(v, w)²`. -/
theorem embed_sq_dist (v w : PBit R) :
    (v.embed.1 - w.embed.1) ^ 2 + (v.embed.2 - w.embed.2) ^ 2 =
        2 * ((v.support - w.support) ^ 2 + (v.opposition - w.opposition) ^ 2) ∧
      (v.embed.1 - w.embed.1) ^ 2 + (v.embed.2 - w.embed.2) ^ 2 = 4 * v.distSq w := by
  constructor <;> simp only [embed, distSq] <;> ring

/-- Every embedded p-bit has squared norm at most one. -/
theorem embed_sq_norm_le_one (v : PBit R) : v.embed.1 ^ 2 + v.embed.2 ^ 2 ≤ 1 := by
  have diamond := v.embed_mem_diamond
  nlinarith [abs_nonneg v.embed.1, abs_nonneg v.embed.2, sq_abs v.embed.1, sq_abs v.embed.2,
    mul_nonneg (abs_nonneg v.embed.1) (abs_nonneg v.embed.2)]

/-- The coordinates of the embedding, first coordinate first. -/
def embedCoord (v : PBit R) : Bool → R
  | true => v.embed.1
  | false => v.embed.2

/-- The dot product of embedded p-bits. -/
def dot (v w : PBit R) : R := v.embed.1 * w.embed.1 + v.embed.2 * w.embed.2

end Embedding

/-! ### Alignment on real p-bits -/

/-- The magnitude `r_v = ‖z(v)‖`. -/
noncomputable def magnitude (v : PBit ℝ) : ℝ := √(v.embed.1 ^ 2 + v.embed.2 ^ 2)

/-- **Alignment** `z(v)·z(w)/(r_v r_w)`, zero when either vector vanishes: the
real part of the source's conjugate product. -/
noncomputable def align (v w : PBit ℝ) : ℝ :=
  if v.magnitude * w.magnitude = 0 then 0 else v.dot w / (v.magnitude * w.magnitude)

theorem abs_dot_le (v w : PBit ℝ) : |v.dot w| ≤ v.magnitude * w.magnitude := by
  rw [magnitude, magnitude, ← Real.sqrt_mul (by positivity)]
  apply Real.abs_le_sqrt
  simp only [dot]
  nlinarith [sq_nonneg (v.embed.1 * w.embed.2 - v.embed.2 * w.embed.1)]

/-- Alignment lies in `[−1, 1]` (Cauchy–Schwarz). -/
theorem align_mem (v w : PBit ℝ) : -1 ≤ align v w ∧ align v w ≤ 1 := by
  unfold align
  split_ifs with zero
  · norm_num
  · have pos : 0 < v.magnitude * w.magnitude :=
      lt_of_le_of_ne (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Ne.symm zero)
    rw [← abs_le, abs_div, abs_of_pos pos, div_le_one pos]
    exact abs_dot_le v w

/-- **Distance from magnitudes and alignment**:
`4 d_P(v, w)² = r_v² + r_w² − 2 r_v r_w align(v, w)` for nonzero vectors. -/
theorem four_distSq_eq (v w : PBit ℝ) (nonzero : v.magnitude * w.magnitude ≠ 0) :
    4 * v.distSq w =
      v.magnitude ^ 2 + w.magnitude ^ 2 - 2 * (v.magnitude * w.magnitude) * align v w := by
  have hv : v.magnitude ^ 2 = v.embed.1 ^ 2 + v.embed.2 ^ 2 := Real.sq_sqrt (by positivity)
  have hw : w.magnitude ^ 2 = w.embed.1 ^ 2 + w.embed.2 ^ 2 := Real.sq_sqrt (by positivity)
  have cancel : v.magnitude * w.magnitude * (v.dot w / (v.magnitude * w.magnitude)) = v.dot w := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ nonzero]
  rw [align, if_neg nonzero, hv, hw, ← (embed_sq_dist v w).2, mul_assoc, cancel]
  simp only [dot]
  ring

/-- The tempting cosine observer `(1 + align)/2`. -/
noncomputable def cosineSimilarity (v w : PBit ℝ) : ℝ := (1 + align v w) / 2

/-- **The cosine observer is not a tolerance**: its diagonal at the central
p-bit is `½`. -/
theorem cosineSimilarity_central : cosineSimilarity (central : PBit ℝ) central = 1 / 2 := by
  have zero : (central : PBit ℝ).magnitude = 0 := by
    norm_num [magnitude, embed, central]
  simp [cosineSimilarity, align, zero]

/-- The p-bit `(1, ½)`. -/
noncomputable def halfOpposed : PBit ℝ := ⟨1, 1 / 2, zero_le_one, le_rfl, by norm_num, by norm_num⟩

/-- **The cosine complement violates the triangle inequality**: from `T` to `B`
through `(1, ½)` costs `1 − 1/√2 < ½`. -/
theorem cosine_not_metric :
    (1 - cosineSimilarity supported halfOpposed) + (1 - cosineSimilarity halfOpposed both) <
      1 - cosineSimilarity supported both := by
  set s := √(1 / 2 : ℝ) with hs_def
  have hs : s ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have spos : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have m₁ : (supported : PBit ℝ).magnitude = 1 := by norm_num [magnitude, embed, supported]
  have m₂ : (both : PBit ℝ).magnitude = 1 := by norm_num [magnitude, embed, both]
  have m₃ : halfOpposed.magnitude = s := by
    rw [magnitude, hs_def]
    congr 1
    norm_num [embed, halfOpposed]
  have sq_div : (1 / 2 : ℝ) / s = s := by
    rw [div_eq_iff spos.ne', ← hs]
    ring
  have a₁ : align supported halfOpposed = s := by
    have d : (supported : PBit ℝ).dot halfOpposed = 1 / 2 := by
      norm_num [dot, embed, supported, halfOpposed]
    rw [align, m₁, m₃, one_mul, if_neg spos.ne', d, sq_div]
  have a₂ : align halfOpposed both = s := by
    have d : halfOpposed.dot (both : PBit ℝ) = 1 / 2 := by
      norm_num [dot, embed, both, halfOpposed]
    rw [align, m₂, m₃, mul_one, if_neg spos.ne', d, sq_div]
  have a₃ : align (supported : PBit ℝ) both = 0 := by
    have d : (supported : PBit ℝ).dot both = 0 := by norm_num [dot, embed, supported, both]
    rw [align, m₁, m₂, if_neg (by norm_num), d, zero_div]
  simp only [cosineSimilarity, a₁, a₂, a₃]
  nlinarith

/-- The regularized alignment `a_ε` of a stable gate policy. -/
noncomputable def regularizedAlign (ε : ℝ) (v w : PBit ℝ) : ℝ :=
  v.dot w / (√(v.magnitude ^ 2 + ε ^ 2) * √(w.magnitude ^ 2 + ε ^ 2))

/-- `a_ε` lies in `[−1, 1]` for `ε > 0`. -/
theorem regularizedAlign_mem {ε : ℝ} (hε : 0 < ε) (v w : PBit ℝ) :
    -1 ≤ regularizedAlign ε v w ∧ regularizedAlign ε v w ≤ 1 := by
  have pv : 0 < √(v.magnitude ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have pw : 0 < √(w.magnitude ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have lv : v.magnitude ≤ √(v.magnitude ^ 2 + ε ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have lw : w.magnitude ≤ √(w.magnitude ^ 2 + ε ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have bound : |v.dot w| ≤ √(v.magnitude ^ 2 + ε ^ 2) * √(w.magnitude ^ 2 + ε ^ 2) :=
    (abs_dot_le v w).trans (mul_le_mul lv lw (Real.sqrt_nonneg _) pv.le)
  rw [regularizedAlign, ← abs_le, abs_div, abs_of_pos (mul_pos pv pw), div_le_one (mul_pos pv pw)]
  exact bound

end PBit

section Profiles

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {X : Type u} {Q : Type v} [Fintype Q] (ρ : Distribution Q R) (e : X → Q → PBit R)

/-- The squared norm `Σ_q ρ(q) ‖z(e(x, q))‖²` of an embedded report profile. -/
def profileSqNorm (x : X) : R := ∑ q, ρ.weight q * ((e x q).embed.1 ^ 2 + (e x q).embed.2 ^ 2)

/-- `‖z_x‖ ≤ 1` (`HS3.06`), squared. -/
theorem profileSqNorm_le_one (x : X) : profileSqNorm ρ e x ≤ 1 := by
  calc profileSqNorm ρ e x ≤ ∑ q, ρ.weight q * 1 :=
        Finset.sum_le_sum fun q _ =>
          mul_le_mul_of_nonneg_left (PBit.embed_sq_norm_le_one _) (ρ.nonnegative q)
    _ = 1 := by simp [ρ.normalized]

/-- **Embedded profiles realize twice the report distance** (`HS3.06`), squared:
`‖z_x − z_y‖² = 4 d_e(x, y)²`. -/
theorem profile_sq_dist (x y : X) :
    ∑ q, ρ.weight q * (((e x q).embed.1 - (e y q).embed.1) ^ 2 +
        ((e x q).embed.2 - (e y q).embed.2) ^ 2) = 4 * reportDistSq ρ e x y := by
  rw [reportDistSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [(PBit.embed_sq_dist _ _).2]
  ring

end Profiles

/-- `‖z_x − z_y‖ = 2 d_e(x, y)` (`HS3.06`). -/
theorem profile_dist {X : Type u} {Q : Type v} [Fintype Q] (ρ : Distribution Q ℝ)
    (e : X → Q → PBit ℝ) (x y : X) :
    √(∑ q, ρ.weight q * (((e x q).embed.1 - (e y q).embed.1) ^ 2 +
        ((e x q).embed.2 - (e y q).embed.2) ^ 2)) = 2 * reportDistance ρ e x y := by
  rw [profile_sq_dist, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), reportDistance,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-! ## Interference is a magnitude term minus a distinction bracket (`HS3.07`) -/

section Interference

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {ι : Type u} {K : Type v} [Fintype ι] [Fintype K] (w : K → R)

/-- A weighted dot product `Σ_k w(k) x(k) y(k)` on coordinate vectors. -/
def wdot (x y : K → R) : R := ∑ k, w k * x k * y k

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem wdot_sub_self (x y : K → R) :
    wdot w (x - y) (x - y) = wdot w x x + wdot w y y - 2 * wdot w x y := by
  unfold wdot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by simp only [Pi.sub_apply]; ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem wdot_smul (c : R) (x : K → R) : wdot w (c • x) (c • x) = c ^ 2 * wdot w x x := by
  unfold wdot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem wdot_sum_sum (a b : ι → R) (z : ι → K → R) :
    wdot w (∑ i, a i • z i) (∑ j, b j • z j) = ∑ i, ∑ j, a i * b j * wdot w (z i) (z j) := by
  unfold wdot
  calc ∑ k, w k * (∑ i, a i • z i) k * (∑ j, b j • z j) k
      = ∑ k, ∑ i, ∑ j, a i * b j * (w k * z i k * z j k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [mul_assoc, Finset.sum_mul_sum]
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, ∑ k, ∑ j, a i * b j * (w k * z i k * z j k) := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, a i * b j * (w k * z i k * z j k) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ j, a i * b j * ∑ k, w k * z i k * z j k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm

/-- The magnitude term `A = Σ_i m_i ‖z_i‖²`. -/
def magnitudeTerm (m : ι → R) (z : ι → K → R) : R := ∑ i, m i * wdot w (z i) (z i)

/-- The squared-distinction bracket `H₂ = Σ_{i,j} m_i m_j d_ij²` with
`d_ij = ‖z_i − z_j‖ / 2`. Squaring is pointwise; `d²` is an energy, not a
pseudometric. -/
def distinctionEnergy (m : ι → R) (z : ι → K → R) : R :=
  ∑ i, ∑ j, m i * m j * (wdot w (z i - z j) (z i - z j) / 4)

/-- The interference functional `‖Σ a_i z_i‖² − Σ a_i² ‖z_i‖²`. -/
def interference (a : ι → R) (z : ι → K → R) : R :=
  wdot w (∑ i, a i • z i) (∑ i, a i • z i) - ∑ i, a i ^ 2 * wdot w (z i) (z i)

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem double_sum_left (m : ι → R) (hm : ∑ i, m i = 1) (f : ι → R) :
    ∑ i, ∑ j, m i * m j * f i = ∑ i, m i * f i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑ j, m i * m j * f i = (∑ j, m j) * (m i * f i) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = m i * f i := by rw [hm, one_mul]

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem double_sum_right (m : ι → R) (hm : ∑ i, m i = 1) (f : ι → R) :
    ∑ i, ∑ j, m i * m j * f j = ∑ j, m j * f j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ i, m i * m j * f j = (∑ i, m i) * (m j * f j) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = m j * f j := by rw [hm, one_mul]

/-- **The variance identity** (`HS3.07`): for weights summing to one,
`‖Σ m_i z_i‖² = A − 2 H₂`. -/
theorem wdot_mean (m : ι → R) (hm : ∑ i, m i = 1) (z : ι → K → R) :
    wdot w (∑ i, m i • z i) (∑ i, m i • z i) = magnitudeTerm w m z - 2 * distinctionEnergy w m z := by
  have hA : magnitudeTerm w m z =
      (∑ i, ∑ j, m i * m j * wdot w (z i) (z i)) / 2 +
        (∑ i, ∑ j, m i * m j * wdot w (z j) (z j)) / 2 := by
    rw [double_sum_left m hm, double_sum_right m hm, magnitudeTerm]
    ring
  rw [hA, distinctionEnergy, wdot_sum_sum, Finset.sum_div, Finset.sum_div, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wdot_sub_self]
  ring

/-- **The interference identity** (`HS3.07`): with `S = Σ a_i ≠ 0` and
`m_i = a_i / S`, `I = S² (A − 2 H₂) − Σ a_i² ‖z_i‖²`. -/
theorem interference_eq (a : ι → R) (z : ι → K → R) (hS : ∑ i, a i ≠ 0) :
    interference w a z =
      (∑ i, a i) ^ 2 * (magnitudeTerm w (fun i => a i / ∑ i, a i) z -
          2 * distinctionEnergy w (fun i => a i / ∑ i, a i) z) -
        ∑ i, a i ^ 2 * wdot w (z i) (z i) := by
  have hm : ∑ i, a i / ∑ i, a i = 1 := by rw [← Finset.sum_div, div_self hS]
  have scale : ∑ i, a i • z i = (∑ i, a i) • ∑ i, (a i / ∑ i, a i) • z i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    field_simp
  rw [interference, scale, wdot_smul, wdot_mean w _ hm]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The pair form: `2 I = Σ_{i ≠ j} a_i a_j (‖z_i‖² + ‖z_j‖² − 4 d_ij²)`. -/
theorem two_interference_eq [DecidableEq ι] (a : ι → R) (z : ι → K → R) :
    2 * interference w a z = ∑ i, ∑ j, if i = j then 0 else
      a i * a j * (wdot w (z i) (z i) + wdot w (z j) (z j) - wdot w (z i - z j) (z i - z j)) := by
  have diag : ∀ i, ∑ j, (if i = j then 0 else
      a i * a j * (wdot w (z i) (z i) + wdot w (z j) (z j) - wdot w (z i - z j) (z i - z j))) =
      2 * ∑ j, a i * a j * wdot w (z i) (z j) - 2 * (a i ^ 2 * wdot w (z i) (z i)) := by
    intro i
    have each : ∀ j, (if i = j then 0 else
        a i * a j * (wdot w (z i) (z i) + wdot w (z j) (z j) - wdot w (z i - z j) (z i - z j))) =
        2 * (a i * a j * wdot w (z i) (z j)) -
          if i = j then 2 * (a i ^ 2 * wdot w (z i) (z i)) else 0 := by
      intro j
      split_ifs with same
      · subst same
        ring
      · rw [wdot_sub_self]
        ring
    rw [Finset.sum_congr rfl fun j _ => each j, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq Finset.univ i, if_pos (Finset.mem_univ i)]
  rw [Finset.sum_congr rfl fun i _ => diag i, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, interference, wdot_sum_sum]
  ring

end Interference

/-- The bracket is linear in a constant factor of the kernel. -/
theorem Distribution.pairAverage_mul_left {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {V : Type u} [Fintype V] (p : Distribution V R) (c : R)
    (f : V → V → R) : p.pairAverage (fun x y => c * f x y) = c * p.pairAverage f := by
  unfold Distribution.pairAverage
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- The Chapter 3 bounds `h² ≤ H₂ ≤ h` hold for every kernel in `[0, 1]`:
the bracket of a square dominates the square of the bracket (Jensen). -/
theorem Distribution.pairAverage_sq_le {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {V : Type u} [Fintype V] (p : Distribution V R) (d : V → V → R) :
    p.pairAverage d ^ 2 ≤ p.pairAverage fun x y => d x y ^ 2 := by
  set h := p.pairAverage d with hh
  have scale : p.pairAverage (fun x y => 2 * h * d x y) = 2 * h * h := by
    rw [p.pairAverage_mul_left, hh]
  have expand : p.pairAverage (fun x y => (d x y - h) ^ 2) =
      p.pairAverage (fun x y => d x y ^ 2) - (2 * h * h - h ^ 2) := by
    have shape : (fun x y => (d x y - h) ^ 2) =
        fun x y => d x y ^ 2 - (2 * h * d x y - h ^ 2) := by
      funext x y
      ring
    rw [shape, p.pairAverage_sub, p.pairAverage_sub, scale, p.pairAverage_const]
  have nonneg := p.pairAverage_nonnegative (f := fun x y => (d x y - h) ^ 2) fun _ _ => sq_nonneg _
  linarith

theorem Distribution.pairAverage_sq_le_self {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {V : Type u} [Fintype V] (p : Distribution V R) {d : V → V → R}
    (bounds : ∀ x y, 0 ≤ d x y ∧ d x y ≤ 1) :
    (p.pairAverage fun x y => d x y ^ 2) ≤ p.pairAverage d :=
  p.pairAverage_mono fun x y => by nlinarith [bounds x y]

section ReportInterference

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {X : Type u} {Q : Type v} [Fintype Q] (ρ : Distribution Q R) (e : X → Q → PBit R)

/-- The embedded profile `z_x` of a token, as a coordinate vector. -/
def profile (x : X) : Q × Bool → R := fun i => (e x i.1).embedCoord i.2

/-- The probe weights on profile coordinates. -/
def profileWeight : Q × Bool → R := fun i => ρ.weight i.1

theorem wdot_profile_sub (x y : X) :
    wdot (profileWeight ρ) (profile e x - profile e y) (profile e x - profile e y) =
      4 * reportDistSq ρ e x y := by
  rw [← profile_sq_dist, wdot, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_bool]
  simp only [profileWeight, profile, Pi.sub_apply, PBit.embedCoord]
  ring

theorem wdot_profile_self (x : X) :
    wdot (profileWeight ρ) (profile e x) (profile e x) = profileSqNorm ρ e x := by
  rw [wdot, profileSqNorm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_bool]
  simp only [profileWeight, profile, PBit.embedCoord]
  ring

/-- For report profiles, `H₂` is the bracket of the squared report distance. -/
theorem distinctionEnergy_profile {ι : Type w} [Fintype ι] (m : ι → R) (xs : ι → X) :
    distinctionEnergy (profileWeight ρ) m (fun i => profile e (xs i)) =
      ∑ i, ∑ j, m i * m j * reportDistSq ρ e (xs i) (xs j) := by
  unfold distinctionEnergy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [wdot_profile_sub]
  ring

/-- **`0 ≤ H₂ ≤ A/2 ≤ ½`** for report profiles under a probability vector. -/
theorem distinctionEnergy_profile_bounds {ι : Type w} [Fintype ι] (m : Distribution ι R)
    (xs : ι → X) :
    0 ≤ distinctionEnergy (profileWeight ρ) m.weight (fun i => profile e (xs i)) ∧
      2 * distinctionEnergy (profileWeight ρ) m.weight (fun i => profile e (xs i)) ≤
        magnitudeTerm (profileWeight ρ) m.weight (fun i => profile e (xs i)) ∧
      magnitudeTerm (profileWeight ρ) m.weight (fun i => profile e (xs i)) ≤ 1 := by
  have wnonneg : ∀ x : Q × Bool → R, 0 ≤ wdot (profileWeight ρ) x x := fun x =>
    Finset.sum_nonneg fun k _ => by
      rw [mul_assoc]; exact mul_nonneg (ρ.nonnegative k.1) (mul_self_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · rw [distinctionEnergy_profile]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (m.nonnegative i) (m.nonnegative j)) (reportDistSq_nonneg ρ e _ _)
  · have mean := wdot_mean (profileWeight ρ) m.weight m.normalized (fun i => profile e (xs i))
    have := wnonneg (∑ i, m.weight i • profile e (xs i))
    linarith
  · unfold magnitudeTerm
    calc ∑ i, m.weight i * wdot (profileWeight ρ) (profile e (xs i)) (profile e (xs i))
        ≤ ∑ i, m.weight i * 1 := Finset.sum_le_sum fun i _ => by
          rw [wdot_profile_self]
          exact mul_le_mul_of_nonneg_left (profileSqNorm_le_one ρ e _) (m.nonnegative i)
      _ = 1 := by simp [m.normalized]

end ReportInterference

/-- **`h² ≤ H₂ ≤ h`** (`HS3.07`) for report profiles: with `h` the ordinary
distinction bracket and `H₂` the squared one. -/
theorem report_energy_between {X : Type u} {Q : Type v} {ι : Type w} [Fintype Q] [Fintype ι]
    (ρ : Distribution Q ℝ) (e : X → Q → PBit ℝ) (m : Distribution ι ℝ) (xs : ι → X) :
    (m.pairAverage fun i j => reportDistance ρ e (xs i) (xs j)) ^ 2 ≤
        m.pairAverage (fun i j => reportDistance ρ e (xs i) (xs j) ^ 2) ∧
      m.pairAverage (fun i j => reportDistance ρ e (xs i) (xs j) ^ 2) ≤
        m.pairAverage fun i j => reportDistance ρ e (xs i) (xs j) :=
  ⟨m.pairAverage_sq_le _, m.pairAverage_sq_le_self fun _ _ =>
    ⟨reportDistance_nonneg ρ e _ _, reportDistance_le_one ρ e _ _⟩⟩

/-! ## Polarity channels -/

section Channels

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [Field R] [IsStrictOrderedRing R] in
theorem sup'_univ_bool (f : Bool → R) :
    Finset.univ.sup' Finset.univ_nonempty f = max (f true) (f false) :=
  le_antisymm (Finset.sup'_le _ _ fun b _ => by cases b <;> simp)
    (max_le (Finset.le_sup' f (Finset.mem_univ true)) (Finset.le_sup' f (Finset.mem_univ false)))

/-- Max-product composition of gain matrices, target first:
`(A ⊙ B)_{γδ} = max_η A_{γη} B_{ηδ}`. -/
def GainMatrix.comp {Γ : Type u} [Fintype Γ] [Nonempty Γ] (A B : GainMatrix Γ R) : GainMatrix Γ R where
  gain γ δ := Finset.univ.sup' Finset.univ_nonempty fun η => A.gain γ η * B.gain η δ
  gain_nonneg γ δ := (mul_nonneg (A.gain_nonneg γ (Classical.arbitrary Γ))
      (B.gain_nonneg _ δ)).trans (Finset.le_sup' (fun η => A.gain γ η * B.gain η δ)
        (Finset.mem_univ _))
  gain_le_one γ δ := Finset.sup'_le _ _ fun η _ =>
    mul_le_one₀ (A.gain_le_one γ η) (B.gain_nonneg η δ) (B.gain_le_one η δ)

/-- Entrywise maximum of gain matrices (parallel channels). -/
def GainMatrix.sup {Γ : Type u} (A B : GainMatrix Γ R) : GainMatrix Γ R where
  gain γ δ := max (A.gain γ δ) (B.gain γ δ)
  gain_nonneg γ δ := le_max_of_le_left (A.gain_nonneg γ δ)
  gain_le_one γ δ := max_le (A.gain_le_one γ δ) (B.gain_le_one γ δ)

/-- The identity: unit diagonal, zero elsewhere. -/
def GainMatrix.id (Γ : Type u) [DecidableEq Γ] (R : Type) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] : GainMatrix Γ R where
  gain γ δ := if γ = δ then 1 else 0
  gain_nonneg γ δ := by split_ifs <;> norm_num
  gain_le_one γ δ := by split_ifs <;> norm_num

/-- **The canonical p-bit quantale as diagonal channel operators**: a gain
`(k₊, k₋)` acts as `diag(k₊, k₋)` on the support and opposition channels. -/
def diagonalGain (k : PBit R) : GainMatrix Bool R where
  gain γ δ := if γ = δ then k.coord γ else 0
  gain_nonneg γ δ := by
    split_ifs
    · cases γ
      · exact k.opposition_nonneg
      · exact k.support_nonneg
    · exact le_rfl
  gain_le_one γ δ := by
    split_ifs
    · cases γ
      · exact k.opposition_le_one
      · exact k.support_le_one
    · exact zero_le_one

/-- Logical negation as the channel swap `S`. -/
def swapGain : GainMatrix Bool R where
  gain γ δ := if γ = δ then 0 else 1
  gain_nonneg γ δ := by split_ifs <;> norm_num
  gain_le_one γ δ := by split_ifs <;> norm_num

/-- **The embedding of the canonical quantale** (ch. 3, §6.2): joins go to joins,
the gain product to max-product composition, and the unit `(1, 1)` to the
identity. -/
theorem diagonalGain_hom (k l : PBit R) :
    (diagonalGain (k ⊔ l)).gain = ((diagonalGain k).sup (diagonalGain l)).gain ∧
      (diagonalGain (PBit.gain k l)).gain = ((diagonalGain k).comp (diagonalGain l)).gain ∧
      (diagonalGain (PBit.both : PBit R)).gain = (GainMatrix.id Bool R).gain := by
  refine ⟨?_, ?_, ?_⟩ <;> funext γ δ <;> cases γ <;> cases δ <;>
    simp [diagonalGain, GainMatrix.sup, GainMatrix.comp, GainMatrix.id, PBit.coord, PBit.gain,
      PBit.both, mul_nonneg k.support_nonneg l.support_nonneg,
      mul_nonneg k.opposition_nonneg l.opposition_nonneg]

/-- **Two polarity reversals cancel**: `S ⊙ S = I`. -/
theorem swapGain_comp_swapGain :
    ((swapGain : GainMatrix Bool R).comp swapGain).gain = (GainMatrix.id Bool R).gain := by
  funext γ δ
  cases γ <;> cases δ <;> simp [swapGain, GainMatrix.comp, GainMatrix.id]

variable {Γ : Type u} [Fintype Γ] [Nonempty Γ]

/-- A fixed-source exposure `G_K(v) = v ∨ (K ⊙ s)`. -/
def exposure (K : GainMatrix Γ R) (source target : Γ → R) (γ : Γ) : R :=
  max (target γ) (Finset.univ.sup' Finset.univ_nonempty fun δ => K.gain γ δ * source δ)

/-- **Parallel accumulation** (ch. 3, §6.3): exposures through `K` then `L` are one
exposure through `K ∨ L`; so repeating an exposure changes nothing. -/
theorem exposure_exposure (K L : GainMatrix Γ R) {source : Γ → R} (hs : ∀ δ, 0 ≤ source δ)
    (target : Γ → R) :
    exposure L source (exposure K source target) = exposure (K.sup L) source target := by
  funext γ
  have split : (Finset.univ.sup' Finset.univ_nonempty fun δ => (K.sup L).gain γ δ * source δ) =
      max (Finset.univ.sup' Finset.univ_nonempty fun δ => K.gain γ δ * source δ)
        (Finset.univ.sup' Finset.univ_nonempty fun δ => L.gain γ δ * source δ) := by
    refine le_antisymm (Finset.sup'_le _ _ fun δ _ => ?_) (max_le ?_ ?_)
    · rw [GainMatrix.sup, max_mul_of_nonneg _ _ (hs δ)]
      exact max_le_max (Finset.le_sup' (fun δ => K.gain γ δ * source δ) (Finset.mem_univ δ))
        (Finset.le_sup' (fun δ => L.gain γ δ * source δ) (Finset.mem_univ δ))
    · exact Finset.sup'_le _ _ fun δ _ => (mul_le_mul_of_nonneg_right (le_max_left _ _) (hs δ)).trans
        (Finset.le_sup' (fun δ => (K.sup L).gain γ δ * source δ) (Finset.mem_univ δ))
    · exact Finset.sup'_le _ _ fun δ _ => (mul_le_mul_of_nonneg_right (le_max_right _ _) (hs δ)).trans
        (Finset.le_sup' (fun δ => (K.sup L).gain γ δ * source δ) (Finset.mem_univ δ))
  simp only [exposure, split, max_assoc]

theorem exposure_idem (K : GainMatrix Γ R) {source : Γ → R} (hs : ∀ δ, 0 ≤ source δ)
    (target : Γ → R) :
    exposure K source (exposure K source target) = exposure K source target := by
  rw [exposure_exposure K K hs]
  congr 1
  cases K
  simp [GainMatrix.sup]

end Channels

/-! ## Polarity loops and stabilized conflict (`HS3.09`) -/

section Crisp

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {Γ : Type u} [Fintype Γ] [Nonempty Γ] [DecidableEq Γ]

/-- A crisp channel link: unit gain. -/
def Linked (A : GainMatrix Γ R) (γ δ : Γ) : Prop := A.gain γ δ = 1

/-- Under unit gains every channel reachable along links delivers its value. -/
theorem reach_le_closure (A : GainMatrix Γ R) {u : Γ → R} (hu : InCube u) {γ δ : Γ}
    (reach : Relation.ReflTransGen (Linked A) γ δ) :
    u δ ≤ propagationClosure PathLaw.productLaw A u γ := by
  have walk : ∃ rest : List Γ, walkSignal PathLaw.productLaw A u (γ :: rest) = u δ := by
    induction reach using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], rfl⟩
    | head link _ ih =>
        obtain ⟨rest, eq⟩ := ih
        rename_i η _
        refine ⟨η :: rest, ?_⟩
        rw [walkSignal_cons_cons, eq]
        show A.gain _ η * u δ = u δ
        rw [link, one_mul]
  obtain ⟨rest, eq⟩ := walk
  rw [← eq]
  exact walkSignal_le_closure hu γ rest

omit [DecidableEq Γ] in
/-- With gains in `{0, 1}`, the closure is delivered by a reachable channel. -/
theorem closure_le_reach (A : GainMatrix Γ R) (crisp : ∀ γ δ, A.gain γ δ = 0 ∨ A.gain γ δ = 1)
    {u : Γ → R} (hu : InCube u) (γ : Γ) :
    ∃ δ, Relation.ReflTransGen (Linked A) γ δ ∧ propagationClosure PathLaw.productLaw A u γ ≤ u δ := by
  have walks : ∀ (γ : Γ) (rest : List Γ), ∃ δ, Relation.ReflTransGen (Linked A) γ δ ∧
      walkSignal PathLaw.productLaw A u (γ :: rest) ≤ u δ := by
    intro γ rest
    induction rest generalizing γ with
    | nil => exact ⟨γ, Relation.ReflTransGen.refl, le_rfl⟩
    | cons η rest ih =>
        obtain ⟨δ, reach, le⟩ := ih η
        rw [walkSignal_cons_cons]
        rcases crisp γ η with zero | one
        · refine ⟨γ, Relation.ReflTransGen.refl, ?_⟩
          show A.gain γ η * _ ≤ u γ
          rw [zero, zero_mul]
          exact (hu γ).1
        · refine ⟨δ, Relation.ReflTransGen.head one reach, ?_⟩
          show A.gain γ η * _ ≤ u δ
          rw [one, one_mul]
          exact le
  obtain ⟨rest, -, eq⟩ := iterate_eq_walkSignal (L := PathLaw.productLaw) (A := A) u
    (Fintype.card Γ - 1) γ
  rw [propagationClosure, eq]
  exact walks γ rest

end Crisp

/-- A register graph with a polarity on each edge: `none` means no edge,
`some false` preserves the two channels and `some true` swaps them. -/
structure PolarityGraph (J : Type u) where
  polarity : J → J → Option Bool
  symm : ∀ i j, polarity i j = polarity j i

namespace PolarityGraph

variable {J : Type u} (G : PolarityGraph J)

/-- The unit-gain channel lift on `J × {+, −}`: `(i, c) ← (j, c')` exactly when
`i — j` is an edge whose polarity is `c xor c'`. -/
def liftGain (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq J] :
    GainMatrix (J × Bool) R where
  gain γ δ := if G.polarity γ.1 δ.1 = some (xor γ.2 δ.2) then 1 else 0
  gain_nonneg γ δ := by split_ifs <;> norm_num
  gain_le_one γ δ := by split_ifs <;> norm_num

/-- Walks in the register graph with their total polarity. -/
inductive Walk : J → J → Bool → Prop
  | nil (i : J) : Walk i i false
  | cons {i k j : J} {s σ : Bool} : G.polarity i k = some s → Walk k j σ → Walk i j (xor s σ)

/-- Every register reaches every other. -/
def Connected : Prop := ∀ i j, ∃ σ, G.Walk i j σ

/-- Some closed walk has odd total polarity. -/
def HasOddCycle : Prop := ∃ k, G.Walk k k true

/-- **Balanced** labels: every edge polarity is `τ_i xor τ_j`. -/
def Balanced (τ : J → Bool) : Prop := ∀ i j s, G.polarity i j = some s → s = xor (τ i) (τ j)

variable {G}
variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq J]

/-- A walk of polarity `σ` lifts to a channel path that applies `σ`. -/
theorem Walk.lift {i j : J} {σ : Bool} (walk : G.Walk i j σ) (c : Bool) :
    Relation.ReflTransGen (Linked (G.liftGain R)) (i, c) (j, xor c σ) := by
  induction walk generalizing c with
  | nil i => simpa using Relation.ReflTransGen.refl
  | @cons i k j s σ edge _ ih =>
      have link : Linked (G.liftGain R) (i, c) (k, xor c s) := by
        have : xor c (xor c s) = s := by cases c <;> cases s <;> rfl
        simp [Linked, liftGain, this, edge]
      have assoc : xor (xor c s) σ = xor c (xor s σ) := by cases c <;> cases s <;> cases σ <;> rfl
      exact Relation.ReflTransGen.head link (assoc ▸ ih (xor c s))

theorem liftGain_crisp (γ δ : J × Bool) :
    (G.liftGain R).gain γ δ = 0 ∨ (G.liftGain R).gain γ δ = 1 := by
  simp only [liftGain]
  split_ifs <;> simp

/-- Balanced labels are an invariant of channel paths. -/
theorem Balanced.reach_invariant {τ : J → Bool} (balanced : G.Balanced τ) {γ δ : J × Bool}
    (reach : Relation.ReflTransGen (Linked (G.liftGain R)) γ δ) :
    xor δ.2 (τ δ.1) = xor γ.2 (τ γ.1) := by
  induction reach with
  | refl => rfl
  | tail _ link ih =>
      rename_i η ζ _
      have edge : G.polarity η.1 ζ.1 = some (xor η.2 ζ.2) := by
        by_contra absent
        simp [Linked, liftGain, absent] at link
      have := balanced _ _ _ edge
      rw [← ih]
      revert this
      cases η.2 <;> cases ζ.2 <;> cases τ η.1 <;> cases τ ζ.1 <;> simp

variable [Fintype J] [Nonempty J]

/-- **Odd polarity loops spread both channels** (`HS3.09`): on a connected graph
with an odd cycle, every channel converges to the global maximum
`M = max_i {p_i⁰, n_i⁰}`. -/
theorem closure_of_odd (connected : G.Connected) (odd : G.HasOddCycle) {u : J × Bool → R}
    (hu : InCube u) (γ : J × Bool) :
    propagationClosure PathLaw.productLaw (G.liftGain R) u γ =
      Finset.univ.sup' Finset.univ_nonempty u := by
  obtain ⟨k, loop⟩ := odd
  have reachAll : ∀ δ : J × Bool, Relation.ReflTransGen (Linked (G.liftGain R)) γ δ := by
    intro δ
    obtain ⟨σ₁, toK⟩ := connected γ.1 k
    obtain ⟨σ₂, toJ⟩ := connected k δ.1
    have first := toK.lift (R := R) γ.2
    have around := loop.lift (R := R) (xor γ.2 σ₁)
    have bothK : ∀ b, Relation.ReflTransGen (Linked (G.liftGain R)) γ (k, b) := by
      intro b
      by_cases same : b = xor γ.2 σ₁
      · exact same ▸ first
      · have : b = xor (xor γ.2 σ₁) true := by
          revert same
          generalize xor γ.2 σ₁ = x
          cases b <;> cases x <;> decide
        exact this ▸ first.trans around
    have final := (bothK (xor δ.2 σ₂)).trans (toJ.lift (R := R) (xor δ.2 σ₂))
    have : xor (xor δ.2 σ₂) σ₂ = δ.2 := by cases δ.2 <;> cases σ₂ <;> rfl
    rw [this] at final
    exact final
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun δ _ => reach_le_closure _ hu (reachAll δ))
  obtain ⟨δ, -, le⟩ := closure_le_reach _ liftGain_crisp hu γ
  exact le.trans (Finset.le_sup' u (Finset.mem_univ δ))

/-- **Balanced graphs keep two relabelled channels** (`HS3.09`): on a connected
balanced graph, after relabelling register `i` by `N^{τ_i}`, all registers share
the p-bit of coordinatewise maxima of the relabelled initial reports. -/
theorem closure_of_balanced (connected : G.Connected) {τ : J → Bool} (balanced : G.Balanced τ)
    {u : J × Bool → R} (hu : InCube u) (i : J) (c : Bool) :
    propagationClosure PathLaw.productLaw (G.liftGain R) u (i, c) =
      Finset.univ.sup' Finset.univ_nonempty fun j => u (j, xor (xor c (τ i)) (τ j)) := by
  have reach : ∀ j, Relation.ReflTransGen (Linked (G.liftGain R)) (i, c)
      (j, xor (xor c (τ i)) (τ j)) := by
    intro j
    obtain ⟨σ, walk⟩ := connected i j
    have path := walk.lift (R := R) c
    have invariant := balanced.reach_invariant path
    have : xor c σ = xor (xor c (τ i)) (τ j) := by
      simp only at invariant
      revert invariant
      cases c <;> cases σ <;> cases τ i <;> cases τ j <;> simp
    exact this ▸ path
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun j _ => reach_le_closure _ hu (reach j))
  obtain ⟨δ, reachδ, le⟩ := closure_le_reach _ liftGain_crisp hu (i, c)
  have invariant := balanced.reach_invariant reachδ
  have channel : δ.2 = xor (xor c (τ i)) (τ δ.1) := by
    simp only at invariant
    revert invariant
    cases δ.2 <;> cases c <;> cases τ i <;> cases τ δ.1 <;> simp
  refine le.trans ?_
  rw [show δ = (δ.1, xor (xor c (τ i)) (τ δ.1)) from Prod.ext rfl channel]
  exact Finset.le_sup' (fun j => u (j, xor (xor c (τ i)) (τ j))) (Finset.mem_univ δ.1)

end PolarityGraph

/-! ## Uniform measures -/

/-- The uniform probability vector on a finite nonempty carrier. -/
def Distribution.uniform (V : Type u) [Fintype V] [Nonempty V] (R : Type := ℚ) [Field R]
    [LinearOrder R] [IsStrictOrderedRing R] : Distribution V R where
  weight _ := 1 / Fintype.card V
  nonnegative _ := by positivity
  normalized := by
    have card : (Fintype.card V : R) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel card]

/-! ## Examples (ch. 3, §§3, 5, 8) -/

namespace EvidenceExamples

open PBit

section Generic

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- One probe of unit weight. -/
abbrev oneProbe (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] : Distribution Unit R :=
  Distribution.uniform Unit R

theorem reportDistSq_oneProbe {X : Type u} (e : X → Unit → PBit R) (x y : X) :
    reportDistSq (oneProbe R) e x y = (e x ()).distSq (e y ()) := by
  simp [reportDistSq, Distribution.uniform]

theorem uniform_three_pairAverage (f : Fin 3 → Fin 3 → R) :
    (Distribution.uniform (Fin 3) R).pairAverage f =
      (f 0 0 + f 0 1 + f 0 2 + f 1 0 + f 1 1 + f 1 2 + f 2 0 + f 2 1 + f 2 2) / 9 := by
  simp [Distribution.pairAverage, Distribution.uniform, Fin.sum_univ_succ]
  ring

theorem uniform_bool_pairAverage (f : Bool → Bool → R) :
    (Distribution.uniform Bool R).pairAverage f =
      (f true true + f true false + f false true + f false false) / 4 := by
  simp [Distribution.pairAverage, Distribution.uniform]
  ring

/-- The rising reports `(0, 0)`, `(½, ½)`, `(1, 1)` on one probe. -/
def risingReports : Fin 3 → Unit → PBit R
  | 0, _ => neither
  | 1, _ => central
  | 2, _ => both

/-- **A rejected copy of `HS3.01`**: without the root, the squared report
distance is not a pseudometric; `d²(a, c) = 1 > ¼ + ¼`. -/
theorem squaredReport_not_metric :
    ¬ (squaredReportTolerance (oneProbe R) (risingReports (R := R))).Metric := by
  intro metric
  have bound := metric 0 1 2
  simp only [Tolerance.distance, squaredReportTolerance, sub_sub_cancel, reportDistSq_oneProbe]
    at bound
  norm_num [risingReports, distSq, neither, central, both] at bound

/-- The p-bit reports of three contexts answering different probes; `none` is
an unobserved entry. -/
def hiveReports : Fin 3 → Fin 3 → Option (PBit R)
  | 0, 0 => some neither
  | 0, 2 => some neither
  | 1, 0 => some neither
  | 1, 1 => some neither
  | 2, 1 => some neither
  | 2, 2 => some both
  | _, _ => none

/-- The squared distance on the first probe two tokens share (each pair below
shares exactly one). -/
def sharedDistSq (e : Fin 3 → Fin 3 → Option (PBit R)) (x y : Fin 3) : R :=
  match e x 0, e y 0, e x 1, e y 1, e x 2, e y 2 with
  | some a, some b, _, _, _, _ => a.distSq b
  | _, _, some a, some b, _, _ => a.distSq b
  | _, _, _, _, some a, some b => a.distSq b
  | _, _, _, _, _, _ => 0

/-- **Comparing on different shared probes breaks the triangle inequality**
(ch. 3, §5.2): `d(a, b) = d(b, c) = 0` but `d(a, c) = 1`. -/
theorem shared_probe_comparison_not_metric :
    sharedDistSq (hiveReports (R := R)) 0 1 = 0 ∧ sharedDistSq (hiveReports (R := R)) 1 2 = 0 ∧
      sharedDistSq (hiveReports (R := R)) 0 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [sharedDistSq, hiveReports, distSq, neither, both]

end Generic

/-! ### Reports generate a metric observer: positive and negative examples -/

/-- Two names with the same report. -/
noncomputable def sameReports : Bool → Unit → PBit ℝ := fun _ _ => neither

/-- **Equal reports need not be equal tokens** (`HS3.01`): two names with the
same report are one point of the report quotient. -/
theorem equal_reports_distinct_tokens :
    true ≠ false ∧ reportDistance (oneProbe ℝ) sameReports true false = 0 ∧
      ReportQuotient.mk (oneProbe ℝ) sameReports true =
        ReportQuotient.mk (oneProbe ℝ) sameReports false := by
  refine ⟨Bool.noConfusion, by simp [reportDistance, reportDistSq_oneProbe, sameReports], ?_⟩
  rw [ReportQuotient.mk_eq_mk_iff]
  intro q _
  rfl

theorem sqrt_quarter : √(1 / 4 : ℝ) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem risingReports_distance :
    reportDistance (oneProbe ℝ) risingReports 0 1 = 1 / 2 ∧
      reportDistance (oneProbe ℝ) risingReports 1 2 = 1 / 2 ∧
      reportDistance (oneProbe ℝ) risingReports 0 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [reportDistance, reportDistSq_oneProbe, risingReports, distSq, neither, central, both] <;>
    norm_num [sqrt_quarter]

/-- **A positive threshold is not an equivalence** (ch. 3, §3.3): `d ≤ ½` relates
`a` to `b` and `b` to `c`, not `a` to `c`. -/
theorem threshold_not_transitive :
    reportDistance (oneProbe ℝ) risingReports 0 1 ≤ 1 / 2 ∧
      reportDistance (oneProbe ℝ) risingReports 1 2 ≤ 1 / 2 ∧
      ¬ reportDistance (oneProbe ℝ) risingReports 0 2 ≤ 1 / 2 := by
  obtain ⟨h₁, h₂, h₃⟩ := risingReports_distance
  rw [h₁, h₂, h₃]
  norm_num

/-! ### Three reports: distinction, resonance and a lossy translation (§8.1) -/

/-- The reports `T`, `(½, ½)`, `F` on one unit-weight probe. -/
def threeReports {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    Fin 3 → Unit → PBit R
  | 0, _ => supported
  | 1, _ => central
  | 2, _ => opposed

/-- The table of a symmetric kernel on three tokens with zero diagonal. -/
def table {R : Type} [Field R] (ab bc ac : R) (i j : Fin 3) : R :=
  if i = j then 0 else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then ac
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then ab else bc

theorem threeReports_distSq {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (i j : Fin 3) :
    reportDistSq (oneProbe R) threeReports i j = table (1 / 4) (1 / 4) 1 i j := by
  rw [reportDistSq_oneProbe]
  fin_cases i <;> fin_cases j <;>
    norm_num [table, threeReports, distSq, supported, central, opposed, Fin.ext_iff]

theorem threeReports_distance (i j : Fin 3) :
    reportDistance (oneProbe ℝ) threeReports i j = table (1 / 2) (1 / 2) 1 i j := by
  rw [reportDistance, threeReports_distSq]
  fin_cases i <;> fin_cases j <;> norm_num [table, sqrt_quarter, Fin.ext_iff]

theorem threeReports_similarity (i j : Fin 3) :
    (reportTolerance (oneProbe ℝ) threeReports).similarity i j = 1 - table (1 / 2) (1 / 2) 1 i j := by
  simp only [reportTolerance, threeReports_distance]

/-- `g = 5/9` and `h = 4/9` for the three reports. -/
theorem threeReports_graphtropy :
    (Distribution.uniform (Fin 3) ℝ).graphtropy (reportTolerance (oneProbe ℝ) threeReports) =
        5 / 9 ∧
      (Distribution.uniform (Fin 3) ℝ).distinction (reportTolerance (oneProbe ℝ) threeReports) =
        4 / 9 := by
  have g : (Distribution.uniform (Fin 3) ℝ).graphtropy
      (reportTolerance (oneProbe ℝ) threeReports) = 5 / 9 := by
    rw [Distribution.graphtropy, uniform_three_pairAverage]
    simp only [threeReports_similarity]
    norm_num [table, Fin.ext_iff]
  refine ⟨g, ?_⟩
  rw [Distribution.distinction_eq_one_sub, g]
  norm_num

/-- `H₂ = 1/3`, `A = 2/3`, and with unit weights the interference is `−2`. -/
theorem threeReports_energy {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    distinctionEnergy (profileWeight (oneProbe R))
        (Distribution.uniform (Fin 3) R).weight (fun i => profile threeReports i) = 1 / 3 ∧
      magnitudeTerm (profileWeight (oneProbe R))
        (Distribution.uniform (Fin 3) R).weight (fun i => profile threeReports i) = 2 / 3 ∧
      interference (profileWeight (oneProbe R)) (fun _ : Fin 3 => (1 : R))
        (fun i => profile threeReports i) = -2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [distinctionEnergy_profile]
    simp only [threeReports_distSq]
    simp [Fin.sum_univ_succ, Distribution.uniform, table]
    norm_num
  · simp only [magnitudeTerm, wdot_profile_self, profileSqNorm, Fin.sum_univ_succ]
    simp [Distribution.uniform, threeReports, embed, supported, central, opposed]
    norm_num
  · simp only [interference, wdot, profile, profileWeight, Fintype.sum_prod_type, Fintype.sum_bool,
      Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp [Distribution.uniform, threeReports, embedCoord, embed, supported, central, opposed]
    norm_num

/-- The lossy translation merging `a, b` into `r` and sending `c` to `s`. -/
def lossyMap : Fin 3 → Bool
  | 0 => false
  | 1 => false
  | 2 => true

/-- The crisp identity observer on `{r, s}`. -/
noncomputable def outputObserver : Tolerance Bool ℝ := Tolerance.ofReport id ℝ

theorem outputObserver_pullback (i j : Fin 3) :
    outputObserver.similarity (lossyMap i) (lossyMap j) = 1 - table 0 1 1 i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [outputObserver, Tolerance.ofReport, lossyMap, table, Fin.ext_iff]

/-- **Equal entropy, unequal geometry** (§8.1): output graphtropy is also `5/9`,
yet `Δ_∞(f) = ½` and `Δ_μ(f) = 2/9`; task blindness and unnecessary detail
are both `1/9`. -/
theorem lossy_translation :
    ((Distribution.uniform (Fin 3) ℝ).pushforward lossyMap).graphtropy outputObserver = 5 / 9 ∧
      (∀ x y, |outputObserver.similarity (lossyMap x) (lossyMap y) -
        (reportTolerance (oneProbe ℝ) threeReports).similarity x y| ≤ 1 / 2) ∧
      |outputObserver.similarity (lossyMap 0) (lossyMap 1) -
        (reportTolerance (oneProbe ℝ) threeReports).similarity 0 1| = 1 / 2 ∧
      (Distribution.uniform (Fin 3) ℝ).distortion (reportTolerance (oneProbe ℝ) threeReports)
        outputObserver lossyMap = 2 / 9 ∧
      taskBlindness (Distribution.uniform (Fin 3) ℝ) (reportTolerance (oneProbe ℝ) threeReports)
        (outputObserver.pullback lossyMap) = 1 / 9 ∧
      unnecessaryDetail (Distribution.uniform (Fin 3) ℝ) (reportTolerance (oneProbe ℝ) threeReports)
        (outputObserver.pullback lossyMap) = 1 / 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Distribution.graphtropy_pullback, Distribution.graphtropy, uniform_three_pairAverage]
    simp only [Tolerance.pullback, outputObserver_pullback]
    norm_num [table, Fin.ext_iff]
  · intro x y
    rw [threeReports_similarity, outputObserver_pullback]
    fin_cases x <;> fin_cases y <;> norm_num [table, abs_le, Fin.ext_iff]
  · rw [threeReports_similarity, outputObserver_pullback]
    norm_num [table, Fin.ext_iff]
  · rw [Distribution.distortion, uniform_three_pairAverage]
    simp only [threeReports_similarity, outputObserver_pullback]
    norm_num [table, Fin.ext_iff]
  · rw [taskBlindness, uniform_three_pairAverage]
    simp only [Tolerance.distance, Tolerance.pullback, threeReports_similarity,
      outputObserver_pullback]
    norm_num [table, Fin.ext_iff]
  · rw [unnecessaryDetail, uniform_three_pairAverage]
    simp only [Tolerance.distance, Tolerance.pullback, threeReports_similarity,
      outputObserver_pullback]
    norm_num [table, Fin.ext_iff]

/-- Two reports of one kind, on one probe. -/
def twin {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (v : PBit R) :
    Bool → Unit → PBit R := fun _ _ => v

/-- **Same geometry, different magnitudes** (§7.4): two central reports
interfere with `I = 0`, two `T` reports with `I = 2`; two `N` reports are
aligned and also interfere with `I = 2`. -/
theorem magnitude_matters :
    interference (profileWeight (oneProbe ℚ)) (fun _ : Bool => (1 : ℚ))
        (fun b => profile (twin central) b) = 0 ∧
      interference (profileWeight (oneProbe ℚ)) (fun _ : Bool => (1 : ℚ))
        (fun b => profile (twin supported) b) = 2 ∧
      interference (profileWeight (oneProbe ℚ)) (fun _ : Bool => (1 : ℚ))
        (fun b => profile (twin neither) b) = 2 ∧
      align (neither : PBit ℝ) neither = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [interference, wdot, profile, profileWeight, Fintype.sum_prod_type, Distribution.uniform,
      twin, embedCoord, embed, central]
    norm_num
  · simp [interference, wdot, profile, profileWeight, Fintype.sum_prod_type, Distribution.uniform,
      twin, embedCoord, embed, supported]
    norm_num
  · simp [interference, wdot, profile, profileWeight, Fintype.sum_prod_type, Distribution.uniform,
      twin, embedCoord, embed, neither]
    norm_num
  · have m : (neither : PBit ℝ).magnitude = 1 := by norm_num [magnitude, embed, neither]
    rw [align, m, mul_one, if_neg one_ne_zero]
    norm_num [dot, embed, neither]

/-! ### A raw sorites and its exact closure cost (§8.2) -/

/-- Raw distances `d(a, b) = d(b, c) = 1/5`, `d(a, c) = 9/10`. -/
def soritesRaw : Tolerance (Fin 3) where
  similarity x y := if x = y then 1 else if x = 1 ∨ y = 1 then 4 / 5 else 1 / 10
  nonnegative x y := by split_ifs <;> norm_num
  bounded x y := by split_ifs <;> norm_num
  reflexive x := by simp
  symmetric x y := by fin_cases x <;> fin_cases y <;> norm_num

/-- The closure: only `d(a, c)` drops, to `2/5`. -/
def soritesClosed : Tolerance (Fin 3) where
  similarity x y := if x = y then 1 else if x = 1 ∨ y = 1 then 4 / 5 else 3 / 5
  nonnegative x y := by split_ifs <;> norm_num
  bounded x y := by split_ifs <;> norm_num
  reflexive x := by simp
  symmetric x y := by fin_cases x <;> fin_cases y <;> norm_num

theorem sorites_checked :
    completionCheck soritesRaw soritesClosed Examples.gradedPaths = true := by
  simp only [completionCheck, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;> norm_num [soritesRaw, soritesClosed, Fin.ext_iff]
  · intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      norm_num [Tolerance.distance, soritesClosed, Fin.ext_iff]
  · intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [check, Examples.gradedPaths, Examples.throughMiddle, infer, soritesRaw,
        soritesClosed, Tolerance.distance, Fin.ext_iff]

/-- The checked candidate is the shortest-path closure. -/
theorem sorites_closure :
    soritesClosed.similarity = (shortestTolerance soritesRaw).similarity :=
  leastMetricExtension_unique (completionCheck_sound sorites_checked)
    (shortestTolerance_is_least soritesRaw)

/-- **The exact closure cost** (§8.2, `HS3.04`): `g` rises from `32/45` to
`37/45`, by `⟨μ|σ|μ⟩ = 1/9`. -/
theorem sorites_cost :
    Examples.uniformThree.graphtropy soritesRaw = 32 / 45 ∧
      Examples.uniformThree.graphtropy soritesClosed = 37 / 45 ∧
      Examples.uniformThree.pairAverage
        (fun x y => soritesClosed.similarity x y - soritesRaw.similarity x y) = 1 / 9 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Distribution.graphtropy, Examples.uniformThree_average] <;>
    norm_num [soritesRaw, soritesClosed, Fin.ext_iff]

/-! ### The source's two-context update (§8.3) -/

/-- The source report `v₁ = (0.9, 0.8)`. -/
def sourceReport {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : PBit R :=
  ⟨9 / 10, 4 / 5, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The receiver report `v₂ = (0.2, 0.1)`. -/
def receiverReport {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : PBit R :=
  ⟨1 / 5, 1 / 10, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Gain `½` on both channels. -/
def halfGain {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : PBit R :=
  ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The updated receiver `(0.45, 0.4)`. -/
def updatedReport {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : PBit R :=
  ⟨9 / 20, 2 / 5, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The exposure gives `(0.45, 0.4)`, and a second exposure changes nothing.** -/
theorem two_context_update {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    receiverReport ⊔ gain halfGain sourceReport = (updatedReport : PBit R) ∧
      (receiverReport ⊔ gain halfGain sourceReport) ⊔ gain halfGain sourceReport =
        (updatedReport : PBit R) := by
  have first : receiverReport ⊔ gain halfGain sourceReport = (updatedReport : PBit R) := by
    ext <;> norm_num [receiverReport, gain, halfGain, sourceReport, updatedReport]
  exact ⟨first, by rw [sup_assoc, sup_idem, first]⟩

/-- The two context reports before the exposure. -/
noncomputable def beforeReports : Bool → Unit → PBit ℝ := fun b _ =>
  if b then sourceReport else receiverReport

/-- The two context reports after the exposure. -/
noncomputable def afterReports : Bool → Unit → PBit ℝ := fun b _ =>
  if b then sourceReport else updatedReport

theorem graphtropy_two_tokens (e : Bool → Unit → PBit ℝ) :
    (Distribution.uniform Bool ℝ).graphtropy (reportTolerance (oneProbe ℝ) e) =
      1 - reportDistance (oneProbe ℝ) e true false / 2 := by
  rw [Distribution.graphtropy, uniform_bool_pairAverage]
  simp only [reportTolerance, reportDistance_self, reportDistance_comm (oneProbe ℝ) e false true]
  ring

/-- **The reports move closer**: `d_P(v₁, v₂) = 0.7` and
`d_P(v₁, v₂') = √(29/160)`; two equally weighted tokens have `g = 1 − d/2`. -/
theorem two_context_geometry :
    reportDistance (oneProbe ℝ) beforeReports true false = 7 / 10 ∧
      reportDistance (oneProbe ℝ) afterReports true false = √(29 / 160) ∧
      (Distribution.uniform Bool ℝ).graphtropy (reportTolerance (oneProbe ℝ) beforeReports) =
        13 / 20 ∧
      (Distribution.uniform Bool ℝ).graphtropy (reportTolerance (oneProbe ℝ) afterReports) =
        1 - √(29 / 160) / 2 := by
  have d₁ : reportDistance (oneProbe ℝ) beforeReports true false = 7 / 10 := by
    rw [reportDistance, reportDistSq_oneProbe]
    rw [show (beforeReports true ()).distSq (beforeReports false ()) = (7 / 10) ^ 2 by
      norm_num [beforeReports, distSq, sourceReport, receiverReport]]
    exact Real.sqrt_sq (by norm_num)
  have d₂ : reportDistance (oneProbe ℝ) afterReports true false = √(29 / 160) := by
    rw [reportDistance, reportDistSq_oneProbe]
    congr 1
    norm_num [afterReports, distSq, sourceReport, updatedReport]
  refine ⟨d₁, d₂, ?_, ?_⟩
  · rw [graphtropy_two_tokens, d₁]
    norm_num
  · rw [graphtropy_two_tokens, d₂]

/-- **Supplied gain, not alignment** (§8.3): the initial embedded reports
`(0.1, 0.7)` and `(0.1, −0.7)` have alignment `−0.96`. -/
theorem two_context_alignment : align (sourceReport : PBit ℝ) receiverReport = -24 / 25 := by
  have m₁ : (sourceReport : PBit ℝ).magnitude = √(1 / 2) := by
    rw [magnitude]; congr 1; norm_num [embed, sourceReport]
  have m₂ : (receiverReport : PBit ℝ).magnitude = √(1 / 2) := by
    rw [magnitude]; congr 1; norm_num [embed, receiverReport]
  have half : √(1 / 2 : ℝ) * √(1 / 2) = 1 / 2 := Real.mul_self_sqrt (by norm_num)
  rw [align, m₁, m₂, half, if_neg (by norm_num)]
  norm_num [dot, embed, sourceReport, receiverReport]

/-! ### A polarity triangle generates a stable conflicted report (§8.4) -/

/-- Registers `A, B, C`; `A — B` and `B — C` preserve polarity, `C — A` reverses it. -/
def triangle : PolarityGraph (Fin 3) where
  polarity i j := if i = j then none else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then some true
    else some false
  symm i j := by fin_cases i <;> fin_cases j <;> rfl

/-- The initial state: `A = T`, `B = C = N`. -/
def round₀ : Fin 3 × Bool → ℚ := fun γ => if γ = (0, true) then 1 else 0

/-- Round 1: `A = (1, 0)`, `B = (1, 0)`, `C = (0, 1)`. -/
def round₁ : Fin 3 × Bool → ℚ := fun γ =>
  if γ = (0, true) ∨ γ = (1, true) ∨ γ = (2, false) then 1 else 0

/-- Round 2: `A = (1, 0)`, `B = C = (1, 1)`. -/
def round₂ : Fin 3 × Bool → ℚ := fun γ => if γ = (0, false) then 0 else 1

/-- **The trajectory of the polarity triangle** (§8.4): three rounds, then
stable. -/
theorem triangle_rounds :
    accumulate PathLaw.productLaw (triangle.liftGain ℚ) round₀ = round₁ ∧
      accumulate PathLaw.productLaw (triangle.liftGain ℚ) round₁ = round₂ ∧
      accumulate PathLaw.productLaw (triangle.liftGain ℚ) round₂ = (fun _ => 1) ∧
      accumulate PathLaw.productLaw (triangle.liftGain ℚ) (fun _ => 1) = (fun _ => 1) := by
  decide +kernel

theorem triangle_connected : triangle.Connected := by
  intro i j
  by_cases same : i = j
  · subst same
    exact ⟨false, .nil i⟩
  · by_cases flip : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)
    · exact ⟨xor true false, .cons (by simp [triangle, same, flip]) (.nil j)⟩
    · exact ⟨xor false false, .cons (by simp [triangle, same, flip]) (.nil j)⟩

/-- The cycle `A → B → C → A` has odd polarity. -/
theorem triangle_odd : triangle.HasOddCycle :=
  ⟨0, .cons (k := 1) (s := false) (by decide) (.cons (k := 2) (s := false) (by decide)
    (.cons (k := 0) (s := true) (by decide) (.nil 0)))⟩

/-- **Stabilized conflict** (§8.4, `HS3.09`): every channel ends at the global
maximum `1`, so every register reports `B = (1, 1)`. -/
theorem triangle_final (γ : Fin 3 × Bool) :
    propagationClosure PathLaw.productLaw (triangle.liftGain ℚ) round₀ γ = 1 := by
  rw [PolarityGraph.closure_of_odd triangle_connected triangle_odd (fun γ => by
    unfold round₀; split_ifs <;> norm_num) γ]
  refine le_antisymm (Finset.sup'_le _ _ fun δ _ => by unfold round₀; split_ifs <;> norm_num) ?_
  exact Finset.le_sup'_of_le round₀ (Finset.mem_univ (0, true)) (by simp [round₀])

end EvidenceExamples

end Mettapedia.Cybernetics.DistinctionCalculus
