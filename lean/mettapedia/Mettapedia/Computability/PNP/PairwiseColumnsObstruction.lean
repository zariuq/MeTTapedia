import Mathlib

/-!
# P vs NP crux: pairwise-independent columns do not imply universal hashing

The manuscript repeatedly speaks of the VV parity matrix as having
pairwise-independent columns.  This file formalizes a finite countermodel
showing that this property alone is too weak: three columns can be pairwise
independent while still satisfying a deterministic linear dependency, so a
nonzero input difference always hashes to zero.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

abbrev Bit := ZMod 2
abbrev Seed := Bit × Bit

/-- Three one-bit columns sampled from two uniform seed bits. -/
def col1 (ω : Seed) : Bit := ω.1
def col2 (ω : Seed) : Bit := ω.2
def col3 (ω : Seed) : Bit := ω.1 + ω.2

/-- The three pair maps are bijective, hence pairwise-uniform on the four seeds. -/
def col12Equiv : Seed ≃ Bit × Bit :=
  Equiv.refl _

def col13Equiv : Seed ≃ Bit × Bit where
  toFun ω := (col1 ω, col3 ω)
  invFun p := (p.1, p.1 + p.2)
  left_inv ω := by
    rcases ω with ⟨u, v⟩
    fin_cases u <;> fin_cases v <;> rfl
  right_inv p := by
    rcases p with ⟨u, v⟩
    fin_cases u <;> fin_cases v <;> rfl

def col23Equiv : Seed ≃ Bit × Bit where
  toFun ω := (col2 ω, col3 ω)
  invFun p := (p.1 + p.2, p.1)
  left_inv ω := by
    rcases ω with ⟨u, v⟩
    fin_cases u <;> fin_cases v <;> rfl
  right_inv p := by
    rcases p with ⟨u, v⟩
    fin_cases u <;> fin_cases v <;> rfl

theorem col12_bijective : Function.Bijective (fun ω : Seed => (col1 ω, col2 ω)) :=
  col12Equiv.bijective

theorem col13_bijective : Function.Bijective (fun ω : Seed => (col1 ω, col3 ω)) :=
  col13Equiv.bijective

theorem col23_bijective : Function.Bijective (fun ω : Seed => (col2 ω, col3 ω)) :=
  col23Equiv.bijective

/-- A one-bit linear hash built from the three columns. -/
def threeColumnHash (ω : Seed) (x : Fin 3 → Bit) : Bit :=
  x 0 * col1 ω + x 1 * col2 ω + x 2 * col3 ω

/-- The bad difference vector `(1,1,1)`. -/
def badDifference : Fin 3 → Bit := fun _ => 1

theorem badDifference_ne_zero : badDifference ≠ 0 := by
  intro h
  have h0 : badDifference 0 = 0 := by simpa using congrFun h 0
  simp [badDifference] at h0

theorem threeColumnHash_badDifference (ω : Seed) :
    threeColumnHash ω badDifference = 0 := by
  rcases ω with ⟨u, v⟩
  fin_cases u <;> fin_cases v <;> rfl

theorem badDifference_zeroFiber_card :
    Fintype.card {ω : Seed // threeColumnHash ω badDifference = 0} = Fintype.card Seed := by
  have hAll : ∀ ω : Seed, threeColumnHash ω badDifference = 0 := threeColumnHash_badDifference
  let e : {ω : Seed // threeColumnHash ω badDifference = 0} ≃ Seed :=
    { toFun := fun ω => ω.1
      invFun := fun ω => ⟨ω, hAll ω⟩
      left_inv := by
        intro ω
        apply Subtype.ext
        rfl
      right_inv := by
        intro ω
        rfl }
  exact Fintype.card_congr e

/-- A one-bit universal family would force every nonzero difference to hit zero on at most half
of the seed space. -/
def OneBitUniversal (H : Seed → (Fin 3 → Bit) → Bit) : Prop :=
  ∀ x : Fin 3 → Bit, x ≠ 0 →
    Fintype.card {ω : Seed // H ω x = 0} ≤ Fintype.card Seed / 2

theorem threeColumnHash_not_universal :
    ¬ OneBitUniversal threeColumnHash := by
  intro hU
  have hbad := hU badDifference badDifference_ne_zero
  have hcardSeed : Fintype.card Seed = 4 := by
    norm_num [Seed, Bit]
  rw [badDifference_zeroFiber_card, hcardSeed] at hbad
  norm_num at hbad

end Mettapedia.Computability.PNP
