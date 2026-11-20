import Mettapedia.Cybernetics.ApproximateAdequacy.BisimulationMetric
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order

/-!
# Rational chains read in the reals

The finite labelled Markov chains, couplings and coupling bounds of
`Cybernetics.ApproximateAdequacy` are stated over any linearly ordered field; the bisimulation
metric is defined over `ℝ`. A certificate is checked over `ℚ`. This module carries the rational
objects to the real ones, so that the existing real theorems apply to rational certificates
unchanged:

* a rational chain is read as the real chain with the same masses and observations (`realChain`);
  a real chain given separately with those masses is that chain (`eq_realChain`);
* a rational coupling is read as the real coupling with the same weights and the same cost
  (`realCoupling`, `cost_realCoupling`), so a rational coupling bound is a real coupling bound of
  the real chains (`couplingBound_real`);
* a rational expression is read as the real expression with the same connectives
  (`realExpression`), of the same depth and with the same values (`eval_realExpression`).

**Consequences.** A rational coupling bound bounds the real bisimulation metric at every discount
`0 ≤ c` (`bisimulationMetric_le_real`, from `bisimulationMetric_le`). The difference of a rational
expression at two states bounds the iterate of its depth at `0 ≤ c`
(`abs_eval_sub_le_approxMetric_real`, from `abs_eval_sub_le_approxMetric`) and the metric at
`0 ≤ c ≤ 1` (`abs_eval_sub_le_bisimulationMetric_real`, from `abs_eval_sub_le_bisimulationMetric`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates

open Mettapedia.Cybernetics.ApproximateAdequacy
open FunctionalExpression

variable {A Atom S T : Type*} [Fintype S] [Fintype T]

/-! ## Chains -/

/-- **The real chain of a rational chain**: the same masses and observations, read in `ℝ`. -/
noncomputable def realChain (P : LabelledMarkovChain ℚ A Atom S) : LabelledMarkovChain ℝ A Atom S where
  trans a s x := (P.trans a s x : ℝ)
  isDistribution a s :=
    ⟨fun x => Rat.cast_nonneg.mpr ((P.isDistribution a s).nonneg x), by
      have total := (P.isDistribution a s).sum_eq_one
      exact_mod_cast total⟩
  observe i s := (P.observe i s : ℝ)

@[simp] theorem realChain_trans (P : LabelledMarkovChain ℚ A Atom S) (a : A) (s x : S) :
    (realChain P).trans a s x = (P.trans a s x : ℝ) :=
  rfl

@[simp] theorem realChain_observe (P : LabelledMarkovChain ℚ A Atom S) (i : Atom) (s : S) :
    (realChain P).observe i s = (P.observe i s : ℝ) :=
  rfl

/-- **A real chain with the masses and observations of a rational chain is its real chain.** -/
theorem eq_realChain {P : LabelledMarkovChain ℚ A Atom S} {R : LabelledMarkovChain ℝ A Atom S}
    (trans_eq : ∀ a s x, R.trans a s x = (P.trans a s x : ℝ))
    (observe_eq : ∀ i s, R.observe i s = (P.observe i s : ℝ)) : R = realChain P := by
  obtain ⟨trans, isDistribution, observe⟩ := R
  have same_trans : trans = (realChain P).trans :=
    funext fun a => funext fun s => funext fun x => trans_eq a s x
  have same_observe : observe = (realChain P).observe :=
    funext fun i => funext fun s => observe_eq i s
  subst same_trans same_observe
  rfl

/-! ## Couplings and coupling bounds -/

/-- **A rational coupling read in the reals**: the same weights. -/
noncomputable def realCoupling {μ : S → ℚ} {ν : T → ℚ} (ω : Coupling μ ν) :
    Coupling (fun x => (μ x : ℝ)) (fun y => (ν y : ℝ)) where
  weight x y := (ω.weight x y : ℝ)
  nonneg x y := Rat.cast_nonneg.mpr (ω.nonneg x y)
  sum_right x := by
    have row := ω.sum_right x
    exact_mod_cast row
  sum_left y := by
    have column := ω.sum_left y
    exact_mod_cast column

/-- **The cost is the same.** -/
theorem cost_realCoupling {μ : S → ℚ} {ν : T → ℚ} (ω : Coupling μ ν) (m : S → T → ℚ) :
    (realCoupling ω).cost (fun x y => (m x y : ℝ)) = (ω.cost m : ℝ) := by
  simp [Coupling.cost, realCoupling]

/-- **A rational coupling bound is a real coupling bound** of the real chains, at the same discount,
with the same values. -/
theorem couplingBound_real {P : LabelledMarkovChain ℚ A Atom S} {Q : LabelledMarkovChain ℚ A Atom T}
    {c : ℚ} {m : S → T → ℚ} (bound : CouplingBound P Q c m) :
    CouplingBound (realChain P) (realChain Q) (c : ℝ) fun s t => (m s t : ℝ) where
  nonneg s t := Rat.cast_nonneg.mpr (bound.nonneg s t)
  observe_le i s t := by
    have close := bound.observe_le i s t
    change |(P.observe i s : ℝ) - (Q.observe i t : ℝ)| ≤ (m s t : ℝ)
    exact_mod_cast close
  step_le a s t := by
    obtain ⟨ω, le⟩ := bound.step_le a s t
    refine ⟨realCoupling ω, ?_⟩
    have cast_le : ((c * ω.cost m : ℚ) : ℝ) ≤ (m s t : ℝ) := Rat.cast_le.mpr le
    rw [Rat.cast_mul] at cast_le
    calc (c : ℝ) * (realCoupling ω).cost (fun s t => (m s t : ℝ))
        = (c : ℝ) * (ω.cost m : ℝ) := by rw [cost_realCoupling]
      _ ≤ (m s t : ℝ) := cast_le

/-! ## Expressions -/

/-- **A rational expression read in the reals**: the same connectives, the constants cast. -/
noncomputable def realExpression : FunctionalExpression ℚ A Atom → FunctionalExpression ℝ A Atom
  | .one => .one
  | .observe i => .observe i
  | .oneMinus φ => .oneMinus (realExpression φ)
  | .min φ ψ => .min (realExpression φ) (realExpression ψ)
  | .max φ ψ => .max (realExpression φ) (realExpression ψ)
  | .sub φ q => .sub (realExpression φ) (q : ℝ)
  | .next a φ => .next a (realExpression φ)

/-- **The same depth.** -/
theorem depth_realExpression : ∀ φ : FunctionalExpression ℚ A Atom,
    (realExpression φ).depth = φ.depth
  | .one => rfl
  | .observe _ => rfl
  | .oneMinus φ => by simp only [realExpression, depth, depth_realExpression φ]
  | .min φ ψ => by simp only [realExpression, depth, depth_realExpression φ, depth_realExpression ψ]
  | .max φ ψ => by simp only [realExpression, depth, depth_realExpression φ, depth_realExpression ψ]
  | .sub φ _ => by simp only [realExpression, depth, depth_realExpression φ]
  | .next _ φ => by simp only [realExpression, depth, depth_realExpression φ]

/-- **The same values**: the real expression on the real chain at the real discount takes the
values of the rational expression on the rational chain. -/
theorem eval_realExpression (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) :
    ∀ (φ : FunctionalExpression ℚ A Atom) (s : S),
      (realExpression φ).eval (realChain P) (c : ℝ) s = ((φ.eval P c s : ℚ) : ℝ)
  | .one, _ => by simp [realExpression, eval]
  | .observe i, s => by simp [realExpression, eval]
  | .oneMinus φ, s => by simp [realExpression, eval, eval_realExpression P c φ s]
  | .min φ ψ, s => by
      simp [realExpression, eval, eval_realExpression P c φ s, eval_realExpression P c ψ s,
        Rat.cast_min]
  | .max φ ψ, s => by
      simp [realExpression, eval, eval_realExpression P c φ s, eval_realExpression P c ψ s,
        Rat.cast_max]
  | .sub φ q, s => by
      simp [realExpression, eval, eval_realExpression P c φ s, Rat.cast_max]
  | .next a φ, s => by
      have inner : (realExpression φ).eval (realChain P) (c : ℝ) =
          fun x => ((φ.eval P c x : ℚ) : ℝ) :=
        funext fun x => eval_realExpression P c φ x
      simp only [realExpression, eval, inner, expect, realChain_trans]
      push_cast
      rfl

/-! ## The real theorems for rational certificates -/

variable [Fintype A] [Fintype Atom]

/-- **A rational coupling bound bounds the real bisimulation metric**, at every discount `0 ≤ c`
(`bisimulationMetric_le`). -/
theorem bisimulationMetric_le_real {P : LabelledMarkovChain ℚ A Atom S}
    {Q : LabelledMarkovChain ℚ A Atom T} {c : ℚ} {m : S → T → ℚ} (bound : CouplingBound P Q c m)
    (c_nonneg : 0 ≤ c) (s : S) (t : T) :
    bisimulationMetric (realChain P) (realChain Q) (c : ℝ) s t ≤ (m s t : ℝ) :=
  bisimulationMetric_le (couplingBound_real bound) (Rat.cast_nonneg.mpr c_nonneg) s t

/-- **A rational expression bounds the iterate of its depth from below**, at every discount `0 ≤ c`
(`abs_eval_sub_le_approxMetric`). -/
theorem abs_eval_sub_le_approxMetric_real (P : LabelledMarkovChain ℚ A Atom S)
    (Q : LabelledMarkovChain ℚ A Atom T) {c : ℚ} (c_nonneg : 0 ≤ c)
    (φ : FunctionalExpression ℚ A Atom) {n : ℕ} (deep : φ.depth ≤ n) (s : S) (t : T) :
    ((|φ.eval P c s - φ.eval Q c t| : ℚ) : ℝ) ≤
      approxMetric (realChain P) (realChain Q) (c : ℝ) n s t := by
  have bound := abs_eval_sub_le_approxMetric (P := realChain P) (Q := realChain Q)
    (Rat.cast_nonneg.mpr c_nonneg) (realExpression φ) n (by rw [depth_realExpression]; exact deep)
    s t
  rw [eval_realExpression, eval_realExpression] at bound
  push_cast
  exact bound

/-- **A rational expression bounds the real bisimulation metric from below**, at every discount
`0 ≤ c ≤ 1` (`abs_eval_sub_le_bisimulationMetric`). -/
theorem abs_eval_sub_le_bisimulationMetric_real (P : LabelledMarkovChain ℚ A Atom S)
    (Q : LabelledMarkovChain ℚ A Atom T) {c : ℚ} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1)
    (φ : FunctionalExpression ℚ A Atom) (s : S) (t : T) :
    ((|φ.eval P c s - φ.eval Q c t| : ℚ) : ℝ) ≤
      bisimulationMetric (realChain P) (realChain Q) (c : ℝ) s t := by
  have bound := abs_eval_sub_le_bisimulationMetric (P := realChain P) (Q := realChain Q)
    (Rat.cast_nonneg.mpr c_nonneg) (by exact_mod_cast c_le) (realExpression φ) s t
  rw [eval_realExpression, eval_realExpression] at bound
  push_cast
  exact bound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
