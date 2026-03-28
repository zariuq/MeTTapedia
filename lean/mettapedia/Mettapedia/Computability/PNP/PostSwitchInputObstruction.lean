import Mathlib.Tactic

/-!
# P vs NP crux: the exact post-switch input is not `T_i`-invariant

The paper defines the per-bit post-switch input as `u_i = (z, a_i, b)` and the
promise-preserving involution `T_i` as toggling the VV right-hand side by `a_i`.

This file formalizes the exact bridge point:
- the full input `(z, a_i, b)` is preserved by `T_i` iff `a_i = 0`;
- the reduced projection `(z, a_i)` is always preserved.

So once the paper keeps the full VV right-hand side `b`, the claim that `T_i`
preserves the local input is false on every nonzero VV column. If it drops `b`,
it lands exactly in the invariant-feature regime analyzed by the other
obstruction files.
-/

namespace Mettapedia.Computability.PNP

section

abbrev BitVec (n : ℕ) := Fin n → Bool

def zeroVec {n : ℕ} : BitVec n := fun _ => false

/-- The VV right-hand side update `b ↦ b ⊕ a`. -/
def vvToggle {n : ℕ} (a b : BitVec n) : BitVec n :=
  fun i => Bool.xor (b i) (a i)

structure PostSwitchInput (Z : Type*) (k : ℕ) where
  z : Z
  a : BitVec k
  b : BitVec k

/-- The exact local-input action induced by the paper's involution `T_i`. -/
def tiInputMap {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k) : PostSwitchInput Z k :=
  ⟨u.z, u.a, vvToggle u.a u.b⟩

/-- The obvious `T_i`-invariant projection obtained by dropping the VV
right-hand side. -/
def invariantProjection {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k) : Z × BitVec k :=
  (u.z, u.a)

@[simp] theorem invariantProjection_tiInputMap
    {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k) :
    invariantProjection (tiInputMap u) = invariantProjection u := by
  rfl

lemma vvToggle_eq_self_iff_zero {n : ℕ} (a b : BitVec n) :
    vvToggle a b = b ↔ a = zeroVec := by
  constructor
  · intro h
    funext i
    have hi : Bool.xor (b i) (a i) = b i := by
      simpa [vvToggle] using congrFun h i
    cases hbi : b i <;> cases hai : a i <;> simp [Bool.xor, hbi, hai, zeroVec] at hi ⊢
  · intro h
    subst h
    funext i
    simp [vvToggle, zeroVec]

theorem tiInputMap_eq_self_iff_zeroColumn
    {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k) :
    tiInputMap u = u ↔ u.a = zeroVec := by
  cases u
  simp [tiInputMap, vvToggle_eq_self_iff_zero]

def nonzeroColumn {n : ℕ} (a : BitVec n) : Prop :=
  ∃ i, a i = true

lemma nonzeroColumn_iff_ne_zero {n : ℕ} (a : BitVec n) :
    nonzeroColumn a ↔ a ≠ zeroVec := by
  constructor
  · intro h
    rcases h with ⟨i, hi⟩
    intro hz
    have : a i = false := by simpa [zeroVec] using congrFun hz i
    simp [hi] at this
  · intro h
    by_contra hzero
    apply h
    funext i
    cases hai : a i with
    | false =>
        simp [zeroVec]
    | true =>
        exact False.elim (hzero ⟨i, hai⟩)

theorem tiInputMap_ne_self_of_nonzeroColumn
    {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k)
    (ha : nonzeroColumn u.a) :
    tiInputMap u ≠ u := by
  intro h
  have hz : u.a = zeroVec := (tiInputMap_eq_self_iff_zeroColumn u).mp h
  exact (nonzeroColumn_iff_ne_zero u.a).mp ha hz

theorem tiInputMap_changes_b_of_nonzeroColumn
    {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k)
    (ha : nonzeroColumn u.a) :
    (tiInputMap u).b ≠ u.b := by
  intro hb
  apply tiInputMap_ne_self_of_nonzeroColumn u ha
  cases u
  simpa [tiInputMap] using hb

end

end Mettapedia.Computability.PNP
