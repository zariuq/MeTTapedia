import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

/-!
# Bounds with separate residual caps for two outcomes

Settled masses and caps on unsettled mass are relative to one fixed
problem. The caller supplies the admission proof for those masses, for
example by counting distinct worlds. Positive and negative caps can
be tightened independently.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.ResidualMass

structure Masses where
  positive : ℚ
  negative : ℚ
  pos_nonneg : 0 ≤ positive
  neg_nonneg : 0 ≤ negative

def Masses.support (a : Masses) : ℚ := a.positive + a.negative
def Masses.posterior (a : Masses) : ℚ := a.positive / a.support

structure Partial where
  found : Masses
  unseen : Masses

def Partial.posCap (s : Partial) : ℚ := s.found.positive + s.unseen.positive
def Partial.negCap (s : Partial) : ℚ := s.found.negative + s.unseen.negative

structure Completion (s : Partial) (a : Masses) : Prop where
  foundPos : s.found.positive ≤ a.positive
  foundNeg : s.found.negative ≤ a.negative
  capPos : a.positive ≤ s.posCap
  capNeg : a.negative ≤ s.negCap

def Partial.interval (s : Partial) : Option (ℚ × ℚ) :=
  if s.posCap = 0 then
    if s.negCap = 0 then none else some (0, 0)
  else if s.negCap = 0 then some (1, 1)
  else some (s.found.positive / (s.found.positive + s.negCap),
    s.posCap / (s.posCap + s.found.negative))

private theorem posCap_nonneg (s : Partial) : 0 ≤ s.posCap :=
  add_nonneg s.found.pos_nonneg s.unseen.pos_nonneg

private theorem negCap_nonneg (s : Partial) : 0 ≤ s.negCap :=
  add_nonneg s.found.neg_nonneg s.unseen.neg_nonneg

theorem Completion.interval_sound {s : Partial} {a : Masses} (h : Completion s a)
    (possible : 0 < a.support) :
    ∃ lo hi, s.interval = some (lo, hi) ∧ lo ≤ a.posterior ∧ a.posterior ≤ hi := by
  by_cases noPos : s.posCap = 0
  · have posZero := le_antisymm (noPos ▸ h.capPos) a.pos_nonneg
    have hasNeg : s.negCap ≠ 0 := by
      intro noNeg
      have negZero := le_antisymm (noNeg ▸ h.capNeg) a.neg_nonneg
      simp [Masses.support, posZero, negZero] at possible
    exact ⟨0, 0, by simp [Partial.interval, noPos, hasNeg], by simp [Masses.posterior, posZero]⟩
  by_cases noNeg : s.negCap = 0
  · have negZero := le_antisymm (noNeg ▸ h.capNeg) a.neg_nonneg
    have pos : a.positive ≠ 0 := by simpa [Masses.support, negZero] using possible.ne'
    exact ⟨1, 1, by simp [Partial.interval, noPos, noNeg],
      by simp [Masses.posterior, Masses.support, negZero, pos]⟩
  have lowerDen : 0 < s.found.positive + s.negCap :=
    add_pos_of_nonneg_of_pos s.found.pos_nonneg (lt_of_le_of_ne (negCap_nonneg s) (Ne.symm noNeg))
  have upperDen : 0 < s.posCap + s.found.negative :=
    add_pos_of_pos_of_nonneg (lt_of_le_of_ne (posCap_nonneg s) (Ne.symm noPos)) s.found.neg_nonneg
  refine ⟨s.found.positive / (s.found.positive + s.negCap),
    s.posCap / (s.posCap + s.found.negative), by simp [Partial.interval, noPos, noNeg], ?_, ?_⟩
  · apply (div_le_div_iff₀ lowerDen possible).mpr
    have inequality := mul_le_mul h.foundPos h.capNeg a.neg_nonneg a.pos_nonneg
    unfold Masses.support
    nlinarith only [inequality]
  · apply (div_le_div_iff₀ possible upperDen).mpr
    have inequality := mul_le_mul h.capPos h.foundNeg s.found.neg_nonneg (posCap_nonneg s)
    unfold Masses.support
    nlinarith only [inequality]

/-- With positive caps on both outcomes, each endpoint can be attained
by choosing the extremes of the rectangular mass constraints. -/
theorem rectangle_attains (s : Partial) (possiblePos : 0 < s.posCap) (possibleNeg : 0 < s.negCap)
    {lo hi : ℚ} (answer : s.interval = some (lo, hi)) :
    (∃ a, Completion s a ∧ 0 < a.support ∧ a.posterior = lo) ∧
      (∃ a, Completion s a ∧ 0 < a.support ∧ a.posterior = hi) := by
  simp only [Partial.interval, if_neg possiblePos.ne', if_neg possibleNeg.ne', Option.some.injEq,
    Prod.mk.injEq] at answer
  have p : s.found.positive ≤ s.posCap := le_add_of_nonneg_right s.unseen.pos_nonneg
  have n : s.found.negative ≤ s.negCap := le_add_of_nonneg_right s.unseen.neg_nonneg
  constructor
  · refine ⟨⟨_, _, s.found.pos_nonneg, (negCap_nonneg s)⟩, ⟨le_rfl, n, p, le_rfl⟩, ?_, answer.1⟩
    exact add_pos_of_nonneg_of_pos s.found.pos_nonneg possibleNeg
  · refine ⟨⟨_, _, (posCap_nonneg s), s.found.neg_nonneg⟩, ⟨p, le_rfl, le_rfl, n⟩, ?_, answer.2⟩
    exact add_pos_of_pos_of_nonneg possiblePos s.found.neg_nonneg

theorem Completion.no_support {s : Partial} {a : Masses} (h : Completion s a)
    (empty : s.interval = none) : a.support = 0 := by
  by_contra ne
  have positive : 0 < a.support :=
    lt_of_le_of_ne (add_nonneg a.pos_nonneg a.neg_nonneg) (Ne.symm ne)
  obtain ⟨_, _, read, _, _⟩ := h.interval_sound positive
  rw [empty] at read
  contradiction

end Mettapedia.ProbabilityTheory.StochasticInference.ResidualMass
