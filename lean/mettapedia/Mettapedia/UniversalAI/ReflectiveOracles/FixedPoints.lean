import Mettapedia.UniversalAI.ReflectiveOracles.Basic
import Mettapedia.Topology.BrouwerCube
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.ProjIcc

/-!
# Reflective oracles exist

For finitely many queries, an oracle that is reflective on them is a fixed
point of a continuous map of a cube into itself: move each answer up by the
distance to the set where the answer `1` is not forced, and down by the
distance to the set where the answer `0` is not forced. At a fixed point every
forced answer has been reached.

So the existence of reflective oracles follows from Brouwer's fixed-point
theorem for cubes (`Topology/BrouwerCube.lean`) together with the reduction to
finitely many queries (`ReflectiveOracles/Basic.lean`). The original proof
(Fallenstein, Taylor and Christiano 2015, Appendix B) applies the fixed-point
theorem of Kakutani, Fan and Glicksberg to a set-valued map on an
infinite-dimensional cube; the single-valued map here needs neither.

## Main statements

* `reflectiveOn_extend_of_fixed`: a fixed point of `adjust` gives an oracle
  that is reflective on the finite set.
* `exists_reflectiveOn`: for every set `R` of queries and every oracle there
  is an oracle that is reflective on `R` and agrees with the given one outside
  `R` (Theorem 2.1(ii) of Fallenstein, Taylor and Christiano).
* `exists_reflective`: **a reflective oracle exists** (Theorem 2.1(i) there;
  Theorem 4 of Leike, Taylor and Fallenstein; Theorem 7.5 of Leike's thesis).

Both need the output probabilities to be lower semicontinuous in the oracle.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.ReflectiveOracles

open Set Metric
open scoped unitInterval

universe u

/-! ## A continuous function that is positive exactly on an open set -/

section Margin

variable {X : Type*} [PseudoMetricSpace X]

open Classical in
/-- The distance to the complement of `U`, and `1` when `U` is everything. -/
noncomputable def margin (U : Set X) (x : X) : ℝ :=
  if Uᶜ.Nonempty then infDist x Uᶜ else 1

theorem continuous_margin (U : Set X) : Continuous (margin U) := by
  classical
  unfold margin
  by_cases nonempty : Uᶜ.Nonempty
  · simpa [nonempty] using continuous_infDist_pt Uᶜ
  · simpa [nonempty] using (continuous_const : Continuous fun _ : X => (1 : ℝ))

theorem margin_nonneg (U : Set X) (x : X) : 0 ≤ margin U x := by
  classical
  unfold margin
  split_ifs
  · exact infDist_nonneg
  · exact zero_le_one

theorem margin_pos {U : Set X} (isOpen : IsOpen U) {x : X} (member : x ∈ U) :
    0 < margin U x := by
  classical
  unfold margin
  split_ifs with nonempty
  · exact (isOpen.isClosed_compl.notMem_iff_infDist_pos nonempty).mp (fun inCompl => inCompl member)
  · exact zero_lt_one

theorem margin_eq_zero {U : Set X} {x : X} (notMember : x ∉ U) : margin U x = 0 := by
  classical
  unfold margin
  have nonempty : Uᶜ.Nonempty := ⟨x, notMember⟩
  rw [if_pos nonempty]
  exact infDist_zero_of_mem notMember

end Margin

/-! ## One step towards the forced answers -/

/-- Moving a point of the unit interval up by a positive amount and clamping
leaves it fixed only at `1`. -/
theorem eq_one_of_projIcc_add_eq {t : I} {amount : ℝ} (positive : 0 < amount)
    (fixed : projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) + amount) = t) : t = 1 := by
  have value := congrArg (Subtype.val) fixed
  rw [coe_projIcc] at value
  have upper := t.2.2
  have lower := t.2.1
  apply Subtype.ext
  rw [Set.Icc.coe_one]
  by_contra notOne
  have below : (t : ℝ) < 1 := lt_of_le_of_ne upper notOne
  have minimum : (t : ℝ) < min 1 ((t : ℝ) + amount) := lt_min below (by linarith)
  have maximum : (t : ℝ) < max 0 (min 1 ((t : ℝ) + amount)) := lt_max_of_lt_right minimum
  linarith

/-- Moving a point of the unit interval down by a positive amount and clamping
leaves it fixed only at `0`. -/
theorem eq_zero_of_projIcc_sub_eq {t : I} {amount : ℝ} (positive : 0 < amount)
    (fixed : projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) - amount) = t) : t = 0 := by
  have value := congrArg (Subtype.val) fixed
  rw [coe_projIcc] at value
  have lower := t.2.1
  apply Subtype.ext
  rw [Set.Icc.coe_zero]
  by_contra notZero
  have above : 0 < (t : ℝ) := lt_of_le_of_ne lower (Ne.symm notZero)
  have minimum : min 1 ((t : ℝ) - amount) < (t : ℝ) := min_lt_of_right_lt (by linarith)
  have maximum : max 0 (min 1 ((t : ℝ) - amount)) < (t : ℝ) := max_lt above minimum
  linarith

namespace QuerySystem

variable {Q : Type u} (S : QuerySystem Q) (F : Finset Q) (base : Oracle Q)

open Classical in
/-- The oracle with the answers `x` on `F` and those of `base` elsewhere. -/
noncomputable def extend (x : F → I) : Oracle Q :=
  fun q => if member : q ∈ F then x ⟨q, member⟩ else base q

theorem extend_apply_mem (x : F → I) (q : F) : extend F base x q = x q := by
  classical
  simp [extend, q.2]

theorem extend_apply_notMem (x : F → I) {q : Q} (notMember : q ∉ F) :
    extend F base x q = base q := by
  classical
  simp [extend, notMember]

theorem continuous_extend : Continuous (extend F base) := by
  classical
  refine continuous_pi fun q => ?_
  by_cases member : q ∈ F
  · have : (fun x : F → I => extend F base x q) = fun x => x ⟨q, member⟩ := by
      funext x
      simp [extend, member]
    rw [this]
    exact continuous_apply _
  · have : (fun x : F → I => extend F base x q) = fun _ => base q := by
      funext x
      simp [extend, member]
    rw [this]
    exact continuous_const

/-- The answers on `F` for which the answer `1` at `q` is forced. -/
def oneForced (q : F) : Set (F → I) :=
  {x | S.threshold q < S.outputOne q (extend F base x)}

/-- The answers on `F` for which the answer `0` at `q` is forced. -/
def zeroForced (q : F) : Set (F → I) :=
  {x | 1 - S.threshold q < S.outputZero q (extend F base x)}

variable {S}

theorem isOpen_oneForced (semicontinuous : S.OutputsLowerSemicontinuous) (q : F) :
    IsOpen (S.oneForced F base q) :=
  ((semicontinuous q).1.isOpen_preimage (S.threshold q)).preimage (continuous_extend F base)

theorem isOpen_zeroForced (semicontinuous : S.OutputsLowerSemicontinuous) (q : F) :
    IsOpen (S.zeroForced F base q) :=
  ((semicontinuous q).2.isOpen_preimage (1 - S.threshold q)).preimage (continuous_extend F base)

theorem disjoint_forced (q : F) : Disjoint (S.oneForced F base q) (S.zeroForced F base q) :=
  Set.disjoint_left.mpr fun x one zero => S.not_forced_both (extend F base x) q ⟨one, zero⟩

variable (S)

/-- Move each answer up by the margin of the set where `1` is forced, and
down by the margin of the set where `0` is forced. -/
noncomputable def adjust (x : F → I) : F → I :=
  fun q => projIcc (0 : ℝ) 1 zero_le_one
    ((x q : ℝ) + margin (S.oneForced F base q) x - margin (S.zeroForced F base q) x)

theorem continuous_adjust : Continuous (S.adjust F base) :=
  continuous_pi fun q => continuous_projIcc.comp
    (((continuous_subtype_val.comp (continuous_apply q)).add (continuous_margin _)).sub
      (continuous_margin _))

variable {S}

/-- **A fixed point of the adjustment is reflective on the finite set.** -/
theorem reflectiveOn_extend_of_fixed (semicontinuous : S.OutputsLowerSemicontinuous)
    (x : F → I) (fixed : S.adjust F base x = x) :
    S.ReflectiveOn ↑F (extend F base x) := by
  intro q member
  have fixedAt := congrFun fixed ⟨q, member⟩
  unfold adjust at fixedAt
  have answer : extend F base x q = x ⟨q, member⟩ := extend_apply_mem F base x ⟨q, member⟩
  refine ⟨fun above => ?_, fun above => ?_⟩
  · rw [answer]
    have inOne : x ∈ S.oneForced F base ⟨q, member⟩ := above
    have notZero : x ∉ S.zeroForced F base ⟨q, member⟩ := fun inZero =>
      Set.disjoint_left.mp (disjoint_forced F base ⟨q, member⟩) inOne inZero
    rw [margin_eq_zero notZero, sub_zero] at fixedAt
    exact eq_one_of_projIcc_add_eq
      (margin_pos (isOpen_oneForced F base semicontinuous _) inOne) fixedAt
  · rw [answer]
    have inZero : x ∈ S.zeroForced F base ⟨q, member⟩ := above
    have notOne : x ∉ S.oneForced F base ⟨q, member⟩ := fun inOne =>
      Set.disjoint_left.mp (disjoint_forced F base ⟨q, member⟩) inOne inZero
    rw [margin_eq_zero notOne, add_zero] at fixedAt
    exact eq_zero_of_projIcc_sub_eq
      (margin_pos (isOpen_zeroForced F base semicontinuous _) inZero) fixedAt

/-- Some oracle is reflective on the finite set `F` and agrees with `base`
elsewhere. -/
theorem exists_reflectiveOn_finset (semicontinuous : S.OutputsLowerSemicontinuous) :
    ∃ O, S.ReflectiveOn ↑F O ∧ ∀ q, q ∉ F → O q = base q := by
  obtain ⟨x, fixed⟩ :=
    Mettapedia.Topology.brouwer_cube_fintype (S.adjust F base) (S.continuous_adjust F base)
  exact ⟨extend F base x, reflectiveOn_extend_of_fixed F base semicontinuous x fixed,
    fun q notMember => extend_apply_notMem F base x notMember⟩

/-- **For every set `R` of queries and every oracle there is an oracle that is
reflective on `R` and agrees with the given one outside `R`.** -/
theorem exists_reflectiveOn (semicontinuous : S.OutputsLowerSemicontinuous)
    (R : Set Q) (base : Oracle Q) :
    ∃ O, S.ReflectiveOn R O ∧ ∀ q, q ∉ R → O q = base q := by
  refine exists_reflectiveOn_of_finite semicontinuous R base fun F subset => ?_
  obtain ⟨O, reflective, agrees⟩ := exists_reflectiveOn_finset F base semicontinuous
  exact ⟨O, reflective, fun q notInR => agrees q fun inF => notInR (subset inF)⟩

/-- **A reflective oracle exists.** -/
theorem exists_reflective (semicontinuous : S.OutputsLowerSemicontinuous) :
    ∃ O, S.Reflective O := by
  obtain ⟨O, reflective, _⟩ := exists_reflectiveOn semicontinuous univ (fun _ => 0)
  exact ⟨O, (S.reflective_iff_reflectiveOn_univ O).mpr reflective⟩

end QuerySystem

end Mettapedia.UniversalAI.ReflectiveOracles
