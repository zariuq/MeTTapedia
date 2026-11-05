import Mettapedia.GSLT.LanguageDef.Collections.SkewLayoutCost

/-!
# Controls for the skew layout

With small arrays of at most two elements, blocks of two and one delta
(`P₀`):

* six prepends onto the empty list give one delta before a front of one
  element and two trees of rank `0`, which read `[5 4 3 2 1 0]` and index as
  that list (`six_prepends`, `six_prepends_index`);
* two physical shapes of one list agree on every observation, while the number
  of deltas, a physical fact, separates them (`depth_not_abstract`);
* at forty elements every lookup takes at most nine steps, and two prepends
  per step onto a shared accumulator cost 112 steps over twenty steps against
  230 for a flat array with front slack (`forty_lookups`,
  `shared_twenty`).

Negative controls show what the invariants buy. A chain of rank-`0` trees,
which the skew ranks forbid, makes the lookup of its last element linear in
its length (`chain_lookup_linear`, `chain_invalid`); so does an unbounded chain
of deltas (`deltas_lookup_linear`, `deltas_invalid`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.SkewLayout.Controls

open Mettapedia.Machines.SharedPrependCost (sharedFlat)

/-- Small arrays of at most two elements, blocks of two, one delta. -/
def P₀ : Params := ⟨2, 2, by decide, 1⟩

/-- Prepend the elements of a list, last first, onto the empty list. -/
def build (P : Params) : List ℕ → Body ℕ P.block
  | [] => .small []
  | x :: xs => cons P x (build P xs)

theorem build_valid (P : Params) : ∀ xs : List ℕ, Valid P (build P xs)
  | [] => valid_empty P
  | x :: xs => valid_cons P x _ (build_valid P xs)

theorem build_elements (P : Params) : ∀ xs : List ℕ, (build P xs).elements = xs
  | [] => rfl
  | x :: xs => by rw [build, Body.elements_cons, build_elements P xs]

/-- The shape after six prepends: a delta before a front of one element and
two trees of rank `0`. -/
def shape : Body ℕ P₀.block → ℕ × List ℕ × List ℕ
  | .delta _ (.packed front forest) => (1, front, forest.ranks)
  | .packed front forest => (0, front, forest.ranks)
  | _ => (0, [], [])

theorem six_prepends :
    shape (build P₀ [5, 4, 3, 2, 1, 0]) = (1, [4], [0, 0]) ∧
      (build P₀ [5, 4, 3, 2, 1, 0]).elements = [5, 4, 3, 2, 1, 0] :=
  ⟨by decide, build_elements _ _⟩

theorem six_prepends_index :
    (build P₀ [5, 4, 3, 2, 1, 0]).nth 4 = some 1 ∧
      ((build P₀ [5, 4, 3, 2, 1, 0]).nthCounted 4).2 = 5 := by
  constructor <;> decide

/-- One list in two shapes: a delta before a front of two, and one front of
three. -/
def withDelta : Body ℕ 3 := .delta 2 (.packed [1, 0] [])
def withoutDelta : Body ℕ 3 := .packed [2, 1, 0] []

theorem depth_not_abstract :
    (skew (A := ℕ) (V := Unit) ⟨4, 3, by decide, 1⟩).abs (withDelta, .nil) =
        (skew (A := ℕ) (V := Unit) ⟨4, 3, by decide, 1⟩).abs (withoutDelta, .nil) ∧
      withDelta.depth ≠ withoutDelta.depth :=
  ⟨rfl, by decide⟩

/-- Forty elements: every lookup takes at most nine steps. -/
theorem forty_lookups :
    ∀ i < 40, ((build P₀ (List.range 40).reverse).nthCounted i).2 ≤ 9 := by
  decide

/-- Twenty steps of two prepends onto one shared accumulator. -/
theorem shared_twenty : (sharedSkew P₀ 20).2 = 112 ∧ (sharedFlat 20).2 = 230 := by
  constructor <;> decide

/-! ## What the invariants buy -/

/-- A chain of `m` rank-`0` trees of one element each. -/
def chain (m : ℕ) : Forest ℕ 1 := (List.range m).map fun k => ⟨0, .leaf ⟨[k], rfl⟩⟩

def chainBody (m : ℕ) : Body ℕ 1 := .packed [] (chain m)

/-- The lookup of the last element walks the whole chain. -/
theorem chain_lookup_linear (m : ℕ) : ((chainBody (m + 1)).nthCounted m).2 = m + 3 := by
  have walk : ∀ (ks : List ℕ) (i : ℕ), i < ks.length →
      (Forest.getCounted (ks.map fun k => (⟨0, .leaf ⟨[k], rfl⟩⟩ : Σ r, Tree ℕ 1 r)) i).2 = i + 2 := by
    intro ks
    induction ks with
    | nil => intro i inside; cases inside
    | cons k ks ih =>
        intro i inside
        cases i with
        | zero => rfl
        | succ i =>
            simp only [List.map_cons, Forest.getCounted, treeBlocks, Nat.one_mul]
            rw [if_neg (by omega), Nat.add_sub_cancel, ih i (by simpa using inside)]
  simp only [chainBody, Body.nthCounted, List.length_nil, Nat.not_lt_zero, if_false, Nat.sub_zero, chain]
  rw [walk _ m (by simp)]

/-- The chain breaks the skew ranks. -/
theorem chain_invalid (P : Params) (same : P.block = 1) (m : ℕ) (long : 3 ≤ m) :
    ¬ Valid P (same ▸ chainBody m : Body ℕ P.block) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  intro valid
  cases P with
  | mk small block positive deltas =>
      simp only at same
      subst same
      obtain ⟨_, skew⟩ := valid
      simp only [chain, List.range_succ_eq_map, List.map_cons, List.map_map, Forest.ranks] at skew
      obtain ⟨_, increasing⟩ := skew
      exact (Nat.lt_irrefl 0) ((List.pairwise_cons.mp increasing).1 0 (by simp))

/-- `m` deltas before an empty front. -/
def deltaChain : ℕ → Body ℕ 1
  | 0 => .packed [] []
  | m + 1 => .delta m (deltaChain m)

theorem deltas_lookup_linear : ∀ m, ((deltaChain (m + 1)).nthCounted m).2 = m + 1
  | 0 => rfl
  | m + 1 => by
      simp only [deltaChain, Body.nthCounted]
      have := deltas_lookup_linear m
      simp only [deltaChain] at this
      omega

theorem depth_deltaChain : ∀ m, (deltaChain m).depth = m
  | 0 => rfl
  | m + 1 => by simp [deltaChain, Body.depth, depth_deltaChain m]

/-- More deltas than the bound break the invariants. -/
theorem deltas_invalid (P : Params) (same : P.block = 1) (m : ℕ) (many : P.deltas < m) :
    ¬ Valid P (same ▸ deltaChain m : Body ℕ P.block) := by
  intro valid
  cases P with
  | mk small block positive deltas =>
      simp only at same many
      subst same
      have := depth_le_of_valid _ _ valid
      rw [depth_deltaChain] at this
      dsimp only at this
      omega

end Mettapedia.GSLT.LanguageDef.Collections.SkewLayout.Controls
