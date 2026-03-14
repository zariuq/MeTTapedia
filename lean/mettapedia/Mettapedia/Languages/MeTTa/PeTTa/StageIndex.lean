import Mettapedia.OSLF.Framework.HypercubeGSLTFunctor

/-!
# PeTTa Stage Ordering

A 4-stage chain indexing the PeTTa GSLT fiber. Each stage shares the same
`LanguageDef` (user rewrite rules) but carries progressively richer semantic
packages (relation environment, execution contracts, scope contracts).

## Stages

1. **sourceCore** — plain source-rule fragment (LP-safe, no builtins)
2. **queryCore** — + match/get-atoms/premise-aware query
3. **statefulCore** — + add-atom/remove-atom/state effects
4. **boundaryAware** — + grounded-host/compat-head boundary

## References

- Plan: `cosmic-scribbling-thacker.md` Step 2
- `Mettapedia.OSLF.Framework.HypercubeGSLTFunctor` — `ForwardFiber`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.StageIndex

/-- The 4-stage PeTTa refinement chain.

    Each stage adds semantic surface area while sharing the same `LanguageDef`.
    The ordering is: `sourceCore ≤ queryCore ≤ statefulCore ≤ boundaryAware`. -/
inductive PeTTaStage where
  | sourceCore
  | queryCore
  | statefulCore
  | boundaryAware
  deriving DecidableEq, Repr

namespace PeTTaStage

/-- Numeric encoding for the total order. -/
def toNat : PeTTaStage → Nat
  | .sourceCore    => 0
  | .queryCore     => 1
  | .statefulCore  => 2
  | .boundaryAware => 3

/-- The ordering: stage `v ≤ w` iff `v.toNat ≤ w.toNat`. -/
instance : LE PeTTaStage where
  le v w := v.toNat ≤ w.toNat

instance : DecidableRel (α := PeTTaStage) (· ≤ ·) :=
  fun v w => Nat.decLe v.toNat w.toNat

/-- `toNat` is injective. -/
theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  cases a <;> cases b <;> simp [toNat] at h ⊢

instance : Preorder PeTTaStage where
  le_refl a := Nat.le_refl a.toNat
  le_trans a b c h1 h2 := Nat.le_trans h1 h2

/-- The ordering is antisymmetric. -/
theorem le_antisymm (a b : PeTTaStage) (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
  toNat_injective (Nat.le_antisymm h1 h2)

/-- The ordering is total. -/
theorem le_total (a b : PeTTaStage) : a ≤ b ∨ b ≤ a :=
  Nat.le_total a.toNat b.toNat

/-! ## Convenience lemmas -/

theorem sourceCore_le_queryCore : sourceCore ≤ queryCore := by decide
theorem queryCore_le_statefulCore : queryCore ≤ statefulCore := by decide
theorem statefulCore_le_boundaryAware : statefulCore ≤ boundaryAware := by decide
theorem sourceCore_le_boundaryAware : sourceCore ≤ boundaryAware := by decide

end PeTTaStage

end Mettapedia.Languages.MeTTa.PeTTa.StageIndex
