import Mettapedia.GSLT.Distinction.Constructive.Transport
import Mettapedia.GSLT.Distinction.Isometry
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The classical bridge from depth bounds to the real-valued profile

**This module is classical.**  Its theorems use real suprema and the classical
behavioural metric of `BehaviouralMetric`, and their axioms include
`Classical.choice`.  It states where the classical profile and the
constructive layer meet, and where the classical step enters.

A **realization** (`Realization`) reads a value scale into the reals: an
additive order embedding taking `one` to `1` and the discount to
multiplication by a real discount.  A presented system then has a classical
graded system (`PresentedSystem.toGraded`) with the same dynamics, its readings
read as reals and that discount.

* Formula values agree (`eval_toGraded`): the classical supremum over the
  successor set is the finite supremum over the authored enumeration.
* **The classical distance is the supremum of the depth bounds**
  (`logicalDistance_eq_iSup_depthBound`), and their limit
  (`tendsto_depthBound_logicalDistance`).  Under the authored cover the
  behavioural distance is the same supremum
  (`behaviouralDistance_eq_iSup_depthBound`).
* **The rate**: with a real discount `c < 1`, the classical distance exceeds
  the depth-`n` bound by at most `c ^ n / (1 - c)`
  (`logicalDistance_le_depthBound_add`).  This is the constructive tail bound
  of `DepthBound` read into the reals.
* **Zero-distance reflection, classically**
  (`gradedBisimilar_iff_forall_depthBound_eq_zero`): with a positive real
  discount, agreement at every finite depth is graded bisimilarity.  This is
  the step that `Controls` shows to imply LLPO when required of every
  presented system constructively.
* **Isometry compatibility**: an exact observation map is a classical
  `ObservationBisimulation` (`toObservationBisimulation`), and with a supplied
  section, rather than `Function.surjInv`, classical logical distances agree on
  mapped pairs (`logicalDistance_map_of_section`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Constructive

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction
open Filter Topology

universe uS uT uA uL uO uA' uL' uO' uV

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

/-- **A realization** of a value scale in the reals. -/
structure Realization (K : Scale V) where
  toReal : V → ℝ
  toReal_add : ∀ first second, toReal (first + second) = toReal first + toReal second
  toReal_le_iff : ∀ {first second : V}, toReal first ≤ toReal second ↔ first ≤ second
  toReal_one : toReal K.one = 1
  /-- The real discount. -/
  discount : ℝ
  toReal_discount : ∀ value, toReal (K.discount value) = discount * toReal value

namespace Realization

variable {K : Scale V} (ρ : Realization K)

theorem toReal_zero : ρ.toReal 0 = 0 := by
  have doubled := ρ.toReal_add 0 0
  rw [add_zero] at doubled
  linarith

theorem toReal_neg (value : V) : ρ.toReal (-value) = -ρ.toReal value := by
  have sum := ρ.toReal_add (-value) value
  rw [neg_add_cancel, ρ.toReal_zero] at sum
  linarith

theorem toReal_sub (first second : V) :
    ρ.toReal (first - second) = ρ.toReal first - ρ.toReal second := by
  rw [sub_eq_add_neg, ρ.toReal_add, ρ.toReal_neg, ← sub_eq_add_neg]

theorem toReal_mono {first second : V} (le : first ≤ second) : ρ.toReal first ≤ ρ.toReal second :=
  ρ.toReal_le_iff.mpr le

theorem toReal_injective {first second : V} (same : ρ.toReal first = ρ.toReal second) :
    first = second :=
  le_antisymm (ρ.toReal_le_iff.mp same.le) (ρ.toReal_le_iff.mp same.ge)

theorem toReal_nonneg {value : V} (nonneg : 0 ≤ value) : 0 ≤ ρ.toReal value := by
  rw [← ρ.toReal_zero]
  exact ρ.toReal_mono nonneg

theorem toReal_max (first second : V) :
    ρ.toReal (max first second) = max (ρ.toReal first) (ρ.toReal second) := by
  rcases le_total first second with le | le
  · rw [max_eq_right le, max_eq_right (ρ.toReal_mono le)]
  · rw [max_eq_left le, max_eq_left (ρ.toReal_mono le)]

theorem toReal_min (first second : V) :
    ρ.toReal (min first second) = min (ρ.toReal first) (ρ.toReal second) := by
  rcases le_total first second with le | le
  · rw [min_eq_left le, min_eq_left (ρ.toReal_mono le)]
  · rw [min_eq_right le, min_eq_right (ρ.toReal_mono le)]

theorem toReal_abs (value : V) : ρ.toReal |value| = |ρ.toReal value| := by
  rcases le_total 0 value with nonneg | nonpos
  · rw [abs_of_nonneg nonneg, abs_of_nonneg (ρ.toReal_nonneg nonneg)]
  · have image : ρ.toReal value ≤ 0 := by
      rw [← ρ.toReal_zero]
      exact ρ.toReal_mono nonpos
    rw [abs_of_nonpos nonpos, abs_of_nonpos image, ρ.toReal_neg]

theorem toReal_clamp (value : V) : ρ.toReal (K.clamp value) = clamp (ρ.toReal value) := by
  rw [Scale.clamp, ρ.toReal_max, ρ.toReal_min, ρ.toReal_zero, ρ.toReal_one, clamp]

theorem discount_nonneg : 0 ≤ ρ.discount := by
  have := ρ.toReal_nonneg (K.discount_nonneg K.zero_le_one)
  rwa [ρ.toReal_discount, ρ.toReal_one, mul_one] at this

theorem discount_le_one : ρ.discount ≤ 1 := by
  have := ρ.toReal_mono K.discount_le_one
  rwa [ρ.toReal_discount, ρ.toReal_one, mul_one] at this

theorem toReal_listSup {α : Type uA} (f : α → V) :
    ∀ list : List α, ρ.toReal (listSup f list) = listSup (fun element => ρ.toReal (f element)) list
  | [] => ρ.toReal_zero
  | head :: rest => by rw [listSup_cons, listSup_cons, ρ.toReal_max, toReal_listSup f rest]

theorem toReal_listInf {α : Type uA} (top : V) (f : α → V) :
    ∀ list : List α, ρ.toReal (listInf top f list) =
      listInf (ρ.toReal top) (fun element => ρ.toReal (f element)) list
  | [] => rfl
  | head :: rest => by rw [listInf_cons, listInf_cons, ρ.toReal_min, toReal_listInf top f rest]

theorem toReal_hausdorff {α : Type uA} {β : Type uO} (top : V) (distance : α → β → V)
    (first : List α) (second : List β) :
    ρ.toReal (hausdorff top distance first second) =
      hausdorff (ρ.toReal top) (fun element other => ρ.toReal (distance element other))
        first second := by
  rw [hausdorff, hausdorff, ρ.toReal_max, ρ.toReal_listSup, ρ.toReal_listSup]
  congr 1
  · exact listSup_congr fun element _ => ρ.toReal_listInf top _ second
  · exact listSup_congr fun other _ => ρ.toReal_listInf top _ first

theorem toReal_iterate_discount (steps : ℕ) :
    ρ.toReal (K.discount^[steps] K.one) = ρ.discount ^ steps := by
  induction steps with
  | zero => rw [Function.iterate_zero_apply, ρ.toReal_one, pow_zero]
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply', ρ.toReal_discount, inductionHypothesis, pow_succ, mul_comm]

theorem toReal_tail_mul (start length : ℕ) :
    ρ.toReal (K.tail start length) * (1 - ρ.discount) =
      ρ.discount ^ start * (1 - ρ.discount ^ length) := by
  induction length with
  | zero => rw [Scale.tail, ρ.toReal_zero, pow_zero, sub_self, zero_mul, mul_zero]
  | succ length inductionHypothesis =>
      rw [Scale.tail, ρ.toReal_add, add_mul, inductionHypothesis, ρ.toReal_iterate_discount,
        pow_add, pow_succ]
      ring

theorem toReal_tail_le (below : ρ.discount < 1) (start length : ℕ) :
    ρ.toReal (K.tail start length) ≤ ρ.discount ^ start / (1 - ρ.discount) := by
  have positive : 0 < 1 - ρ.discount := by linarith
  rw [le_div_iff₀ positive, ρ.toReal_tail_mul]
  have powerNonneg : 0 ≤ ρ.discount ^ length := pow_nonneg ρ.discount_nonneg _
  have startNonneg : 0 ≤ ρ.discount ^ start := pow_nonneg ρ.discount_nonneg _
  nlinarith

end Realization

/-- The realization of the integer scale: `k ↦ k / unit`, discount one. -/
noncomputable def Realization.integers (unit : ℤ) (positive : 0 < unit) :
    Realization (Scale.integers unit positive) where
  toReal value := (value : ℝ) / unit
  toReal_add first second := by rw [Int.cast_add, add_div]
  toReal_le_iff := by
    intro first second
    have unitPositive : (0 : ℝ) < unit := Int.cast_pos.mpr positive
    rw [div_le_div_iff_of_pos_right unitPositive, Int.cast_le]
  toReal_one := by
    have unitPositive : (0 : ℝ) < unit := Int.cast_pos.mpr positive
    exact div_self unitPositive.ne'
  discount := 1
  toReal_discount value := by rw [one_mul]; rfl

/-! ## The classical graded system of a presented system -/

namespace PresentedSystem

variable {S : GSLT.{uS}} {K : Scale V}

/-- **The classical profile** of a presented system under a realization. -/
noncomputable abbrev toGraded (Q : PresentedSystem.{uS, uA, uL, uO} S K) (ρ : Realization K) :
    GradedSystem.{uS, uA, uL, uO} S where
  dynamics := Q.dynamics
  observations :=
    { Atom := Q.Obs
      value := fun observation term => ρ.toReal (Q.value observation term)
      value_nonneg := fun observation term => ρ.toReal_nonneg (Q.value_nonneg observation term)
      value_le_one := fun observation term => by
        rw [← ρ.toReal_one]
        exact ρ.toReal_mono (Q.value_le_one observation term)
      value_resp := fun observation _ _ equivalent =>
        congrArg ρ.toReal (Q.value_resp observation equivalent) }
  discount := ρ.discount
  discount_nonneg := ρ.discount_nonneg
  discount_le_one := ρ.discount_le_one

end PresentedSystem

/-- Read a constructive formula as a classical one: thresholds are realized. -/
def ScaledFormula.toGraded {Obs : Type uO} {Label : Type uL} {K : Scale V} (ρ : Realization K) :
    ScaledFormula Obs Label V → GradedFormula Obs Label
  | .top => .top
  | .atom observation => .atom observation
  | .neg inner => .neg (toGraded ρ inner)
  | .conj left right => .conj (toGraded ρ left) (toGraded ρ right)
  | .shift threshold inner => .shift (ρ.toReal threshold) (toGraded ρ inner)
  | .dia label inner => .dia label (toGraded ρ inner)

/-- The modal depth of a classical formula. -/
def gradedDepth {Obs : Type uO} {Label : Type uL} : GradedFormula Obs Label → ℕ
  | .top => 0
  | .atom _ => 0
  | .neg inner => gradedDepth inner
  | .conj left right => max (gradedDepth left) (gradedDepth right)
  | .shift _ inner => gradedDepth inner
  | .dia _ inner => gradedDepth inner + 1

namespace PresentedSystem

variable {S : GSLT.{uS}} {K : Scale V} (Q : PresentedSystem.{uS, uA, uL, uO} S K)
  (ρ : Realization K)

/-- The classical supremum over the successor set is the finite supremum over
the enumeration. -/
theorem sSup_image_successors (label : Q.dynamics.Label) (term : S.Term) (f : S.Term → ℝ)
    (nonneg : ∀ target, 0 ≤ f target)
    (respects : ∀ {first second : S.Term}, S.Equiv first second → f first = f second) :
    sSup (f '' (Q.toGraded ρ).successors label term) = listSup f (Q.successors label term) := by
  have bounded : ∀ value ∈ f '' (Q.toGraded ρ).successors label term,
      value ≤ listSup f (Q.successors label term) := by
    rintro _ ⟨target, step, rfl⟩
    obtain ⟨representative, member, close⟩ := Q.successors_cover step
    rw [respects close]
    exact le_listSup f member
  refine le_antisymm (Real.sSup_le bounded (listSup_nonneg _ _)) ?_
  refine listSup_le f (Real.sSup_nonneg (by rintro _ ⟨target, -, rfl⟩; exact nonneg target))
    fun target member => ?_
  exact le_csSup ⟨_, bounded⟩ ⟨target, Q.successors_act member, rfl⟩

/-- **Formula values agree with the classical profile.** -/
theorem eval_toGraded : ∀ (formula : Q.Formula) (term : S.Term),
    (Q.toGraded ρ).eval (formula.toGraded ρ) term = ρ.toReal (Q.val formula term)
  | .top, _ => ρ.toReal_one.symm
  | .atom _, _ => rfl
  | .neg inner, term => by
      show 1 - (Q.toGraded ρ).eval (inner.toGraded ρ) term = _
      rw [eval_toGraded inner term, val_neg, ρ.toReal_sub, ρ.toReal_one]
  | .conj first second, term => by
      show min ((Q.toGraded ρ).eval (first.toGraded ρ) term)
        ((Q.toGraded ρ).eval (second.toGraded ρ) term) = _
      rw [eval_toGraded first term, eval_toGraded second term, val_conj, ρ.toReal_min]
  | .shift threshold inner, term => by
      show clamp ((Q.toGraded ρ).eval (inner.toGraded ρ) term - ρ.toReal threshold) = _
      rw [eval_toGraded inner term, val_shift, ρ.toReal_clamp, ρ.toReal_sub]
  | .dia label inner, term => by
      show ρ.discount * sSup (((Q.toGraded ρ).eval (inner.toGraded ρ)) ''
        (Q.toGraded ρ).successors label term) = _
      rw [Q.sSup_image_successors ρ label term _ ((Q.toGraded ρ).eval_nonneg _)
          (fun close => (Q.toGraded ρ).eval_resp _ close), val_dia, ρ.toReal_discount,
        ρ.toReal_listSup]
      congr 1
      exact listSup_congr fun target _ => eval_toGraded inner target

theorem gradedDepth_toGraded : ∀ formula : Q.Formula, gradedDepth (formula.toGraded ρ) = formula.depth
  | .top => rfl
  | .atom _ => rfl
  | .neg inner => gradedDepth_toGraded inner
  | .conj left right => by
      simp only [ScaledFormula.toGraded, gradedDepth, ScaledFormula.depth,
        gradedDepth_toGraded left, gradedDepth_toGraded right]
  | .shift _ inner => gradedDepth_toGraded inner
  | .dia _ inner => by
      simp only [ScaledFormula.toGraded, gradedDepth, ScaledFormula.depth, gradedDepth_toGraded inner]

variable (W : Q.Vocabulary)

/-- **Classical adequacy at depth `n`**: every classical formula of modal
depth at most `n`, with arbitrary real thresholds, changes by at most the
realized depth-`n` bound. -/
theorem abs_eval_sub_le_depthBound :
    ∀ (formula : GradedFormula Q.Obs Q.dynamics.Label) (depth : ℕ) (left right : S.Term),
      gradedDepth formula ≤ depth →
        |(Q.toGraded ρ).eval formula left - (Q.toGraded ρ).eval formula right| ≤
          ρ.toReal (Q.depthBound W depth left right)
  | .top, depth, left, right, _ => by
      rw [GradedSystem.eval_top, GradedSystem.eval_top, sub_self, abs_zero]
      exact ρ.toReal_nonneg (Q.depthBound_nonneg W depth left right)
  | .atom observation, depth, left, right, _ => by
      show |ρ.toReal (Q.value observation left) - ρ.toReal (Q.value observation right)| ≤ _
      rw [← ρ.toReal_sub, ← ρ.toReal_abs]
      exact ρ.toReal_mono ((Q.abs_value_sub_le_observationGap W observation left right).trans
        (Q.observationGap_le_depthBound W depth left right))
  | .neg inner, depth, left, right, bounded => by
      rw [GradedSystem.eval_neg, GradedSystem.eval_neg,
        show 1 - (Q.toGraded ρ).eval inner left - (1 - (Q.toGraded ρ).eval inner right) =
          (Q.toGraded ρ).eval inner right - (Q.toGraded ρ).eval inner left by ring, abs_sub_comm]
      exact abs_eval_sub_le_depthBound inner depth left right bounded
  | .conj first second, depth, left, right, bounded => by
      rw [GradedSystem.eval_conj, GradedSystem.eval_conj]
      exact (abs_min_sub_min_le _ _ _ _).trans
        (max_le (abs_eval_sub_le_depthBound first depth left right ((le_max_left _ _).trans bounded))
          (abs_eval_sub_le_depthBound second depth left right ((le_max_right _ _).trans bounded)))
  | .shift threshold inner, depth, left, right, bounded => by
      rw [GradedSystem.eval_shift, GradedSystem.eval_shift]
      refine (abs_clamp_sub_clamp_le _ _).trans ?_
      rw [sub_sub_sub_cancel_right]
      exact abs_eval_sub_le_depthBound inner depth left right bounded
  | .dia _ _, 0, _, _, bounded => absurd bounded (Nat.not_succ_le_zero _)
  | .dia label inner, depth + 1, left, right, bounded => by
      have innerBound : gradedDepth inner ≤ depth := Nat.le_of_succ_le_succ bounded
      have close : ∀ first second : S.Term,
          |(Q.toGraded ρ).eval inner first - (Q.toGraded ρ).eval inner second| ≤
            ρ.toReal (Q.depthBound W depth first second) :=
        fun first second => abs_eval_sub_le_depthBound inner depth first second innerBound
      rw [GradedSystem.eval_dia, GradedSystem.eval_dia,
        Q.sSup_image_successors ρ label left _ ((Q.toGraded ρ).eval_nonneg _)
          (fun close => (Q.toGraded ρ).eval_resp _ close),
        Q.sSup_image_successors ρ label right _ ((Q.toGraded ρ).eval_nonneg _)
          (fun close => (Q.toGraded ρ).eval_resp _ close),
        ← mul_sub, abs_mul, abs_of_nonneg ρ.discount_nonneg]
      have hausdorffBound := abs_listSup_sub_listSup_le_hausdorff (top := (1 : ℝ))
        (distance := fun first second => ρ.toReal (Q.depthBound W depth first second))
        (first := Q.successors label left) (second := Q.successors label right)
        (f := (Q.toGraded ρ).eval inner) (g := (Q.toGraded ρ).eval inner)
        (fun target _ => (Q.toGraded ρ).eval_le_one _ target)
        (fun target _ => (Q.toGraded ρ).eval_le_one _ target)
        (fun first _ second _ => by
          have := (abs_sub_le_iff.mp (close first second)).1
          linarith)
        (fun first _ second _ => by
          have := (abs_sub_le_iff.mp (close first second)).2
          linarith)
      rw [← ρ.toReal_one, ← ρ.toReal_hausdorff] at hausdorffBound
      calc ρ.discount * |listSup ((Q.toGraded ρ).eval inner) (Q.successors label left) -
            listSup ((Q.toGraded ρ).eval inner) (Q.successors label right)|
          ≤ ρ.discount * ρ.toReal (hausdorff K.one (Q.depthBound W depth)
              (Q.successors label left) (Q.successors label right)) :=
            mul_le_mul_of_nonneg_left hausdorffBound ρ.discount_nonneg
        _ = ρ.toReal (K.discount (hausdorff K.one (Q.depthBound W depth)
              (Q.successors label left) (Q.successors label right))) :=
            (ρ.toReal_discount _).symm
        _ ≤ ρ.toReal (Q.depthBound W (depth + 1) left right) := by
            apply ρ.toReal_mono
            rw [depthBound_succ]
            exact (K.discount_mono (le_listSup (fun label => hausdorff K.one (Q.depthBound W depth)
              (Q.successors label left) (Q.successors label right)) (W.labels_complete label))).trans
              (le_max_right _ _)

theorem bddAbove_depthBound (left right : S.Term) :
    BddAbove (Set.range fun depth : ℕ => ρ.toReal (Q.depthBound W depth left right)) :=
  ⟨1, by
    rintro _ ⟨depth, rfl⟩
    rw [← ρ.toReal_one]
    exact ρ.toReal_mono (Q.depthBound_le_one W depth left right)⟩

/-- **The classical distance is the supremum of the depth bounds.** -/
theorem logicalDistance_eq_iSup_depthBound (left right : S.Term) :
    (Q.toGraded ρ).logicalDistance left right =
      ⨆ depth : ℕ, ρ.toReal (Q.depthBound W depth left right) := by
  refine le_antisymm ((Q.toGraded ρ).logicalDistance_le_iff.mpr fun formula => ?_)
    (ciSup_le fun depth => ?_)
  · exact (Q.abs_eval_sub_le_depthBound ρ W formula (gradedDepth formula) left right le_rfl).trans
      (le_ciSup (Q.bddAbove_depthBound ρ W left right) _)
  · obtain ⟨formula, _, attained⟩ := Q.exists_formula_eq_depthBound W depth left right
    rw [← attained, ρ.toReal_sub, ← Q.eval_toGraded ρ, ← Q.eval_toGraded ρ]
    exact (le_abs_self _).trans ((Q.toGraded ρ).abs_eval_sub_le_logicalDistance _ left right)

theorem depthBound_le_logicalDistance (depth : ℕ) (left right : S.Term) :
    ρ.toReal (Q.depthBound W depth left right) ≤ (Q.toGraded ρ).logicalDistance left right := by
  rw [Q.logicalDistance_eq_iSup_depthBound ρ W]
  exact le_ciSup (Q.bddAbove_depthBound ρ W left right) depth

/-- **The classical distance is the limit of the depth bounds.** -/
theorem tendsto_depthBound_logicalDistance (left right : S.Term) :
    Tendsto (fun depth : ℕ => ρ.toReal (Q.depthBound W depth left right)) atTop
      (𝓝 ((Q.toGraded ρ).logicalDistance left right)) := by
  rw [Q.logicalDistance_eq_iSup_depthBound ρ W]
  exact tendsto_atTop_ciSup (fun _ _ le => ρ.toReal_mono (Q.depthBound_mono W le left right))
    (Q.bddAbove_depthBound ρ W left right)

/-- The authored enumeration certifies finite branching modulo the equations. -/
theorem imageFiniteModulo : Q.dynamics.ImageFiniteModulo := fun label term =>
  ⟨{target | target ∈ Q.successors label term}, List.finite_toSet _,
    fun _ step => Q.successors_cover step⟩

/-- **The behavioural distance is the supremum of the depth bounds.** -/
theorem behaviouralDistance_eq_iSup_depthBound (left right : S.Term) :
    (Q.toGraded ρ).behaviouralDistance left right =
      ⨆ depth : ℕ, ρ.toReal (Q.depthBound W depth left right) :=
  ((Q.toGraded ρ).behaviouralDistance_eq_logicalDistance Q.imageFiniteModulo left right).trans
    (Q.logicalDistance_eq_iSup_depthBound ρ W left right)

/-- **The rate.** With a real discount below one, the classical distance
exceeds the depth-`n` bound by at most `c ^ n / (1 - c)`. -/
theorem logicalDistance_le_depthBound_add (below : ρ.discount < 1) (depth : ℕ)
    (left right : S.Term) :
    (Q.toGraded ρ).logicalDistance left right ≤
      ρ.toReal (Q.depthBound W depth left right) + ρ.discount ^ depth / (1 - ρ.discount) := by
  have tailNonneg : 0 ≤ ρ.discount ^ depth / (1 - ρ.discount) :=
    div_nonneg (pow_nonneg ρ.discount_nonneg _) (by linarith)
  rw [Q.logicalDistance_eq_iSup_depthBound ρ W]
  refine ciSup_le fun depth' => ?_
  rcases le_total depth' depth with le | le
  · exact (ρ.toReal_mono (Q.depthBound_mono W le left right)).trans
      (le_add_of_nonneg_right tailNonneg)
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
    calc ρ.toReal (Q.depthBound W (depth + extra) left right)
        ≤ ρ.toReal (Q.depthBound W depth left right + K.tail depth extra) :=
          ρ.toReal_mono (Q.depthBound_add_le W depth extra left right)
      _ = ρ.toReal (Q.depthBound W depth left right) + ρ.toReal (K.tail depth extra) :=
          ρ.toReal_add _ _
      _ ≤ _ := add_le_add le_rfl (ρ.toReal_tail_le below depth extra)

/-- Classical distance zero is agreement at every finite depth. -/
theorem logicalDistance_eq_zero_iff_forall_depthBound (left right : S.Term) :
    (Q.toGraded ρ).logicalDistance left right = 0 ↔ ∀ depth, Q.depthBound W depth left right = 0 := by
  constructor
  · intro zero depth
    have upper := Q.depthBound_le_logicalDistance ρ W depth left right
    rw [zero] at upper
    have lower := ρ.toReal_nonneg (Q.depthBound_nonneg W depth left right)
    exact ρ.toReal_injective ((le_antisymm upper lower).trans ρ.toReal_zero.symm)
  · intro zero
    rw [Q.logicalDistance_eq_iSup_depthBound ρ W]
    simp only [zero, ρ.toReal_zero, ciSup_const]

/-- **Zero-distance reflection, classically.**  With a positive real
discount, agreement at every finite depth is graded bisimilarity.  The proof
goes through the classical quantitative Hennessy–Milner theorem. -/
theorem gradedBisimilar_iff_forall_depthBound_eq_zero (positive : 0 < ρ.discount)
    (left right : S.Term) :
    Q.GradedBisimilar left right ↔ ∀ depth, Q.depthBound W depth left right = 0 := by
  refine ⟨fun bisimilar depth => Q.depthBound_eq_zero_of_gradedBisimilar W bisimilar depth,
    fun zero => ?_⟩
  obtain ⟨relation, ⟨forward, backward, values⟩, related⟩ :=
    ((Q.toGraded ρ).logicalDistance_eq_zero_iff Q.imageFiniteModulo positive left right).mp
      ((Q.logicalDistance_eq_zero_iff_forall_depthBound ρ W left right).mpr zero)
  exact ⟨relation, ⟨forward, backward, fun _ _ related' observation =>
    ρ.toReal_injective (values related' observation)⟩, related⟩

end PresentedSystem

/-! ## Isometry compatibility -/

namespace ObservationMap

variable {S : GSLT.{uS}} {T : GSLT.{uT}} {K : Scale V}
  {Q : PresentedSystem.{uS, uA, uL, uO} S K} {R : PresentedSystem.{uT, uA', uL', uO'} T K}

/-- **An exact observation map is a classical observation-preserving functional
bisimulation** of the classical profiles. -/
def toObservationBisimulation (map : ObservationMap Q R 0) (ρ : Realization K) :
    ObservationBisimulation (Q.toGraded ρ) (R.toGraded ρ) where
  mapTerm := map.mapTerm
  mapEquiv := map.mapEquiv
  atom := map.atom
  label := map.label
  discount_eq := rfl
  value_map observation term :=
    congrArg ρ.toReal (eq_of_abs_sub_nonpos (map.value_close observation term))
  mapAct := map.mapAct
  liftAct := map.liftAct

/-- **Classical logical distances agree on mapped pairs, from a supplied
section** rather than from `Function.surjInv`. -/
theorem logicalDistance_map_of_section {map : ObservationMap Q R 0}
    (section' : map.VocabularySection) (ρ : Realization K) (WQ : Q.Vocabulary)
    (WR : R.Vocabulary) (left right : S.Term) :
    (R.toGraded ρ).logicalDistance (map.mapTerm left) (map.mapTerm right) =
      (Q.toGraded ρ).logicalDistance left right := by
  rw [R.logicalDistance_eq_iSup_depthBound ρ WR, Q.logicalDistance_eq_iSup_depthBound ρ WQ]
  simp only [depthBound_map_eq section' WQ WR]

end ObservationMap

end Mettapedia.GSLT.Distinction.Constructive
