import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic

/-! Two rational masses used by conditional factor readouts. -/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout

structure Masses where
  joint : ℚ
  evidence : ℚ
  deriving DecidableEq, Repr

def Masses.posterior? (masses : Masses) : Option ℚ :=
  if 0 < masses.evidence then some (masses.joint / masses.evidence) else none

theorem Masses.posterior_bounds (masses : Masses) (nonneg : 0 ≤ masses.joint)
    (included : masses.joint ≤ masses.evidence) {p : ℚ} (read : masses.posterior? = some p) :
    0 ≤ p ∧ p ≤ 1 := by
  unfold posterior? at read
  split at read
  next positive =>
    have same := Option.some.inj read
    subst p
    exact ⟨div_nonneg nonneg positive.le, (div_le_one (a := masses.joint) positive).mpr included⟩
  · contradiction

end Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout
