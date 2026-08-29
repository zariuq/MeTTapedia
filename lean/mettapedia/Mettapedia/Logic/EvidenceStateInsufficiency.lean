import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Strength alone cannot implement evidence revision

The evidence-counts state `(n⁺, n⁻)` supports revision: observing a positive
instance moves the state to `(n⁺+1, n⁻)`.  Its strength readout is
`s = n⁺/(n⁺+n⁻)`.

This file proves two facts about that situation.

* **Insufficiency.**  No learner whose state is any function of the strength
  alone can implement revision: two count states with equal strength but
  different totals are forced to different post-revision strengths, so the
  update would have to send one value to two places.  The two-observation
  history `(1,1)` and the four-observation history `(2,2)` are the witness
  pair: both read `1/2`, but one positive observation must move them to `2/3`
  and `3/5` respectively.

* **Recoverability.**  The pair (strength, evidence total) determines the
  counts exactly (on inhabited states): `n⁺ = s·e` and `n⁻ = (1−s)·e`.  So a
  formulation that keeps a scalar strength and parametrizes its update
  geometry by the evidence total has not eliminated the second dimension — it
  stores the counts inside the geometry.  The state space of any faithful
  evidence learner is two-dimensional; what varies between formulations is
  only which role the second coordinate plays (a value coordinate, or the
  parameter of the update metric).

Consequence for graded-value designs: a metric-governed scalar update is
lossless exactly when the metric's evidence parameter is stored and updated
alongside the strength; drop it and revision is unimplementable.  This is the
operational content of the two-dimensionality of evidence, complementing the
interval/second-coordinate requirements studied in the quantale evidence
programme.
-/

namespace Mettapedia.Logic.EvidenceStateInsufficiency

structure Counts where
  pos : Nat
  neg : Nat
deriving DecidableEq, Repr

def Counts.total (counts : Counts) : Nat := counts.pos + counts.neg

def Counts.strength (counts : Counts) : ℚ :=
  (counts.pos : ℚ) / (counts.total : ℚ)

/-- Bayesian/PLN-style revision by one observation. -/
def Counts.revise (counts : Counts) (observation : Bool) : Counts :=
  if observation then ⟨counts.pos + 1, counts.neg⟩
  else ⟨counts.pos, counts.neg + 1⟩

/-- Two observations, strength 1/2. -/
def light : Counts := ⟨1, 1⟩

/-- Four observations, strength 1/2. -/
def heavy : Counts := ⟨2, 2⟩

theorem light_strength : light.strength = 1 / 2 := by
  norm_num [light, Counts.strength, Counts.total]

theorem heavy_strength : heavy.strength = 1 / 2 := by
  norm_num [heavy, Counts.strength, Counts.total]

theorem light_revised_strength :
    (light.revise true).strength = 2 / 3 := by
  norm_num [light, Counts.revise, Counts.strength, Counts.total]

theorem heavy_revised_strength :
    (heavy.revise true).strength = 3 / 5 := by
  norm_num [heavy, Counts.revise, Counts.strength, Counts.total]

/-- The same strength is forced apart by one observation: revision reads
information that strength does not carry. -/
theorem revision_separates_equal_strengths :
    light.strength = heavy.strength ∧
    (light.revise true).strength ≠ (heavy.revise true).strength := by
  refine ⟨light_strength.trans heavy_strength.symm, ?_⟩
  rw [light_revised_strength, heavy_revised_strength]
  norm_num

/-- **Insufficiency, in full generality.**  Take ANY state space, any encoding
of the current strength into it, any update, and any strength readout.  If the
encoded state depends on the counts only through their strength, the learner
cannot implement revision. -/
theorem no_strength_only_state_implements_revision
    {State : Type} (encode : ℚ → State)
    (step : State → State) (read : State → ℚ) :
    ¬ ∀ counts : Counts,
        read (step (encode counts.strength)) =
          (counts.revise true).strength := by
  intro law
  have from_light := law light
  have from_heavy := law heavy
  rw [light_strength, light_revised_strength] at from_light
  rw [heavy_strength, heavy_revised_strength] at from_heavy
  have collision : (2 : ℚ) / 3 = 3 / 5 :=
    from_light.symm.trans from_heavy
  norm_num at collision

/-- The scalar special case: no function of strength alone is the revised
strength. -/
theorem no_scalar_update_implements_revision :
    ¬ ∃ step : ℚ → ℚ, ∀ counts : Counts,
        step counts.strength = (counts.revise true).strength := by
  rintro ⟨step, law⟩
  exact no_strength_only_state_implements_revision
    (State := ℚ) id step id law

/-- On inhabited evidence states, the numerator is recovered from strength and
total. -/
theorem pos_eq_strength_mul_total (counts : Counts)
    (inhabited : 0 < counts.total) :
    (counts.pos : ℚ) = counts.strength * (counts.total : ℚ) := by
  have total_ne : ((counts.total : ℚ)) ≠ 0 := by
    have nat_ne : counts.total ≠ 0 := by omega
    exact_mod_cast nat_ne
  unfold Counts.strength
  field_simp

/-- **Recoverability.**  (strength, total) determines the counts: the evidence
total is exactly the hidden variable a metric-governed scalar formulation must
store.  Two inhabited states agreeing in both coordinates are equal. -/
theorem counts_determined_by_strength_and_total
    (left right : Counts)
    (left_inhabited : 0 < left.total) (right_inhabited : 0 < right.total)
    (strength_eq : left.strength = right.strength)
    (total_eq : left.total = right.total) :
    left = right := by
  have left_pos :=
    pos_eq_strength_mul_total left left_inhabited
  have right_pos :=
    pos_eq_strength_mul_total right right_inhabited
  have pos_eq : (left.pos : ℚ) = (right.pos : ℚ) := by
    rw [left_pos, right_pos, strength_eq, total_eq]
  have pos_nat : left.pos = right.pos := by exact_mod_cast pos_eq
  have neg_nat : left.neg = right.neg := by
    have := total_eq
    unfold Counts.total at this
    omega
  cases left; cases right
  simp_all

end Mettapedia.Logic.EvidenceStateInsufficiency

#print axioms
  Mettapedia.Logic.EvidenceStateInsufficiency.no_strength_only_state_implements_revision
#print axioms
  Mettapedia.Logic.EvidenceStateInsufficiency.no_scalar_update_implements_revision
#print axioms
  Mettapedia.Logic.EvidenceStateInsufficiency.counts_determined_by_strength_and_total
