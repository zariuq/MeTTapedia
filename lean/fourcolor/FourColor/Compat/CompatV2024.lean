import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace FourColor
namespace Compat

open Equiv

@[simp] lemma zmod2_two_eq_zero : (2 : ZMod 2) = 0 := rfl

namespace Perm

lemma SameCycle.step_right {α} (σ : Perm α) (x : α) :
  σ.SameCycle x (σ x) := by
  refine ⟨(1 : ℤ), ?_⟩
  simp [zpow_one]

lemma SameCycle.step_right_inv {α} (σ : Perm α) (x : α) :
  σ.SameCycle x (σ.symm x) := by
  refine ⟨(-1 : ℤ), ?_⟩
  simp [Equiv.Perm.inv_def]

lemma sameCycle_apply_right {α} (σ : Perm α) {a b : α} :
  σ.SameCycle a (σ b) ↔ σ.SameCycle a b := by
  constructor
  · intro h
    have hb : σ.SameCycle b (σ b) := SameCycle.step_right σ b
    exact (Equiv.Perm.SameCycle.trans h (Equiv.Perm.SameCycle.symm hb))
  · intro h
    have hb : σ.SameCycle b (σ b) := SameCycle.step_right σ b
    exact (Equiv.Perm.SameCycle.trans h hb)

lemma sameCycle_inv_apply_right {α} (σ : Perm α) {a b : α} :
  σ.SameCycle a (σ.symm b) ↔ σ.SameCycle a b := by
  constructor
  · intro h
    have : σ (σ.symm b) = b := σ.apply_symm_apply b
    rw [← this]
    exact (Equiv.Perm.SameCycle.trans h (SameCycle.step_right σ (σ.symm b)))
  · intro h
    exact (Equiv.Perm.SameCycle.trans h (SameCycle.step_right_inv σ b))

end Perm
end Compat
end FourColor
