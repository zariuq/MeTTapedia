import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ProbabilityCalculus

/-!
# Cox → ProbabilityCalculus (Event-Level Integration)

This file provides the **event-level bridge** from Cox’s derivation to the shared
`ProbabilityCalculus` interface.

We work **after regrading** (Cox’s “reparametrization”), i.e. on the scale where:

* Product rule holds: `P(A ∧ B | C) = P(A|C) · P(B|A ∧ C)`
* Complement rule holds: `P(¬A | C) = 1 - P(A|C)`

These are exactly the standard probability rules on a Boolean lattice of events.
From these two rules we derive **finite additivity** for disjoint events, yielding
an instance of `ProbabilityCalculusClass` (the common interface used across K&S).
-/

namespace Mettapedia.ProbabilityTheory.Cox

open Mettapedia.ProbabilityTheory.KnuthSkilling

/-!
## Cox regraded event model

This structure is the **event-level output** of Cox’s theorem:
after regrading, plausibilities satisfy the standard product and complement rules.
It is intentionally minimal and uses K&S’s shared lattice/valuation machinery.
-/

structure CoxProbabilityModel (α : Type*)
    [PlausibilitySpace α] [ComplementedLattice α] where
  /-- Regraded plausibility `P(A|C)` on events. -/
  P : α → α → ℝ
  /-- Range: nonnegative. -/
  P_nonneg : ∀ a c, 0 ≤ P a c
  /-- Range: ≤ 1. -/
  P_le_one : ∀ a c, P a c ≤ 1
  /-- Normalization: P(⊤|C) = 1. -/
  P_top : ∀ c, P ⊤ c = 1
  /-- Normalization: P(⊥|C) = 0. -/
  P_bot : ∀ c, P ⊥ c = 0
  /-- Unconditional monotonicity. -/
  P_mono_uncond : ∀ {a b}, a ≤ b → P a ⊤ ≤ P b ⊤
  /-- Product rule (regraded): P(A∧B|C) = P(A|C)·P(B|A∧C). -/
  product_rule : ∀ a b c, P (a ⊓ b) c = P a c * P b (a ⊓ c)
  /-- Chosen complement operation (for Cox’s ¬A). -/
  compl : α → α
  /-- The chosen complement is indeed a complement. -/
  compl_isCompl : ∀ a, IsCompl a (compl a)
  /-- Complement rule (regraded): P(¬A|C) = 1 - P(A|C). -/
  complement_rule : ∀ a c, P (compl a) c = 1 - P a c

namespace CoxProbabilityModel

variable {α : Type*} [PlausibilitySpace α] [ComplementedLattice α]

/-! ## Induced valuation -/

noncomputable def valuation (M : CoxProbabilityModel α) : Valuation α where
  val := fun a => M.P a ⊤
  monotone := by
    intro a b hab
    exact M.P_mono_uncond hab
  val_bot := by simpa using (M.P_bot ⊤)
  val_top := by simpa using (M.P_top ⊤)

/-! ## Sum rule for disjoint events -/

theorem sum_rule_disjoint (M : CoxProbabilityModel α) {a b : α} (h : Disjoint a b) :
    (M.valuation).val (a ⊔ b) = (M.valuation).val a + (M.valuation).val b := by
  -- Shorthand
  let P : α → α → ℝ := M.P
  have hprod1 :
      P ((a ⊔ b) ⊓ a) ⊤ = P (a ⊔ b) ⊤ * P a (a ⊔ b) := by
    simpa [inf_top_eq] using (M.product_rule (a ⊔ b) a ⊤)
  have hprod2 :
      P ((a ⊔ b) ⊓ M.compl a) ⊤ = P (a ⊔ b) ⊤ * P (M.compl a) (a ⊔ b) := by
    simpa [inf_top_eq] using (M.product_rule (a ⊔ b) (M.compl a) ⊤)
  have hcomp : P (M.compl a) (a ⊔ b) = 1 - P a (a ⊔ b) := by
    simpa using (M.complement_rule a (a ⊔ b))
  have hsum :
      P ((a ⊔ b) ⊓ a) ⊤ + P ((a ⊔ b) ⊓ M.compl a) ⊤ = P (a ⊔ b) ⊤ := by
    calc
      P ((a ⊔ b) ⊓ a) ⊤ + P ((a ⊔ b) ⊓ M.compl a) ⊤
          = P (a ⊔ b) ⊤ * P a (a ⊔ b) + P (a ⊔ b) ⊤ * P (M.compl a) (a ⊔ b) := by
              -- `simp` rewrites `(a ⊔ b) ⊓ a` to `a`, preventing `hprod1` from firing.
              rw [hprod1, hprod2]
      _ = P (a ⊔ b) ⊤ * (P a (a ⊔ b) + P (M.compl a) (a ⊔ b)) := by ring
      _ = P (a ⊔ b) ⊤ * (P a (a ⊔ b) + (1 - P a (a ⊔ b))) := by
              simp [hcomp]
      _ = P (a ⊔ b) ⊤ := by ring
  have hab_bot : a ⊓ b = ⊥ := by
    simpa [disjoint_iff] using h
  have h_inf1 : (a ⊔ b) ⊓ a = a := by simp
  have hle : b ≤ M.compl a := by
    have h' : Disjoint b a := h.symm
    exact (IsCompl.le_right_iff (M.compl_isCompl a)).2 h'
  have h_inf2 : (a ⊔ b) ⊓ M.compl a = b := by
    calc
      (a ⊔ b) ⊓ M.compl a = (a ⊓ M.compl a) ⊔ (b ⊓ M.compl a) := by
        simpa using (inf_sup_right a b (M.compl a))
      _ = ⊥ ⊔ (b ⊓ M.compl a) := by
        have hbot : a ⊓ M.compl a = ⊥ := (M.compl_isCompl a).inf_eq_bot
        simp [hbot]
      _ = b ⊓ M.compl a := by simp
      _ = b := by
        have hb : b ⊓ M.compl a = b := inf_eq_left.mpr hle
        exact hb
  -- Rewrite hsum using the lattice identities
  have hsum' : P (a ⊔ b) ⊤ = P a ⊤ + P b ⊤ := by
    simpa [h_inf1, h_inf2] using hsum.symm
  simpa [valuation] using hsum'

/-! ## ProbabilityCalculus interface -/

instance (M : CoxProbabilityModel α) :
    Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.ProbabilityCalculus.ProbabilityCalculusClass α
      M.valuation where
  sum_rule' := fun {a b} h => M.sum_rule_disjoint h
  complement_rule' := by
    intro a b h_disj h_top
    have hsum := M.sum_rule_disjoint h_disj
    -- `v(a ⊔ b) = 1` by normalization
    have htop : (M.valuation).val (a ⊔ b) = 1 := by
      -- `a ⊔ b = ⊤`
      simpa [valuation, h_top] using (M.P_top ⊤)
    -- Solve for `v b`
    linarith

end CoxProbabilityModel

end Mettapedia.ProbabilityTheory.Cox
