import Mettapedia.Machines.BoundedProbeTable
import Mettapedia.Machines.CanonicalIndexDirectory

/-!
A bounded open-addressed front table with an exact balanced overflow tree.
The overflow has no placement-key assumption. This composes the existing
membership and tree-order laws and gives a deterministic comparison bound;
rekeying alone need not find a bounded placement for every key family.

For a native u32-sized tree, the existing AVL height theorem gives at most
65 comparisons. Thirty-two front-table probes therefore give at most 97
key comparisons even for crafted collisions. Native value transfer,
rotations, allocation failure and representation still require controls.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HybridProbeDirectory

open BoundedProbeTable CanonicalIndexDirectory

variable {K V : Type} [LinearOrder K]

def lookup (front : Table K) (home : K → Nat) (limit : Nat)
    (overflow : Tree K V) (key : K) : Bool :=
  BoundedProbeTable.lookup front home limit key || (overflow.lookup key).isSome

def Holds (front : Table K) (overflow : Tree K V) (key : K) : Prop :=
  BoundedProbeTable.Holds front key ∨ ∃ value, overflow.contains key value

theorem lookup_correct (front : Table K) (home : K → Nat) (limit : Nat)
    (overflow : Tree K V) (key : K)
    (within : Within front home limit) (ordered : overflow.ordered) :
    lookup front home limit overflow key = true ↔ Holds front overflow key := by
  simp only [lookup, Bool.or_eq_true, Holds]
  rw [BoundedProbeTable.lookup_iff front home limit within]
  constructor
  · rintro (found | found)
    · exact Or.inl found
    · cases answer : overflow.lookup key with
      | none => simp [answer] at found
      | some value =>
          exact Or.inr ⟨value, (Tree.lookup_correct overflow ordered key value).mp answer⟩
  · rintro (found | ⟨value, found⟩)
    · exact Or.inl found
    · have answer := (Tree.lookup_correct overflow ordered key value).mpr found
      exact Or.inr (by simp [answer])

/-- A completed rehash may change both the homes and the partition. -/
theorem partition_independent (front₁ front₂ : Table K) (home₁ home₂ : K → Nat)
    (limit₁ limit₂ : Nat) (tree₁ tree₂ : Tree K V)
    (within₁ : Within front₁ home₁ limit₁) (within₂ : Within front₂ home₂ limit₂)
    (ordered₁ : tree₁.ordered) (ordered₂ : tree₂.ordered)
    (same : ∀ key, Holds front₁ tree₁ key ↔ Holds front₂ tree₂ key) (key : K) :
    lookup front₁ home₁ limit₁ tree₁ key = lookup front₂ home₂ limit₂ tree₂ key := by
  have first := lookup_correct front₁ home₁ limit₁ tree₁ key within₁ ordered₁
  have second := lookup_correct front₂ home₂ limit₂ tree₂ key within₂ ordered₂
  cases a : lookup front₁ home₁ limit₁ tree₁ key <;>
    cases b : lookup front₂ home₂ limit₂ tree₂ key <;> simp_all

omit [LinearOrder K] in
theorem overflow_height_u32 (overflow : Tree K V) (balanced : overflow.balanced)
    (count : overflow.size < 2 ^ 32) : overflow.height ≤ 65 := by
  have bound := Tree.height_bound overflow balanced
  by_contra too_high
  have half : 33 ≤ overflow.height / 2 := by omega
  have power := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) half
  have sizes : overflow.size + 1 ≤ 2 ^ 32 := by omega
  norm_num at power sizes
  omega

theorem comparison_bound (overflow : Tree K V) (balanced : overflow.balanced)
    (count : overflow.size < 2 ^ 32) (key : K) :
    32 + overflow.probes key ≤ 97 := by
  have probes := Tree.probes_le_height overflow key
  have height := overflow_height_u32 overflow balanced count
  omega

end Mettapedia.Machines.HybridProbeDirectory
