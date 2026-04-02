import Mettapedia.OSLF.PathMap.Trie.FiniteTrie

/-!
# Trie Anamorphism — Top-Down Unfold

Anamorphism (top-down unfold) for `FTrie V` using mutual recursion
to avoid Lean kernel recursion depth limits on `List.map` with
recursive lambdas.

## References

- Meijer, Fokkinga, Paterson (1991): "Bananas, Lenses, Envelopes and Barbed Wire"
- PathMap crate: `morphisms.rs` (anamorphism section)
-/

namespace Mettapedia.OSLF.PathMap.Trie

universe u v

variable {V : Type u}

/-- A coalgebra: seed → child (byte, seed) pairs + optional value. -/
structure AnaCoalgebra (V : Type u) (W : Type v) where
  unfold : W → List (UInt8 × W) × Option V

/-! ## §1: Anamorphism (mutual recursion) -/

mutual
  /-- Top-down unfold from a seed, bounded by fuel. -/
  def FTrie.ana {W : Type v} (coalg : AnaCoalgebra V W) : Nat → W → FTrie V
    | 0, _ => .empty
    | n + 1, seed =>
      let (childSeeds, val) := coalg.unfold seed
      .node val (FTrie.anaChildren coalg n childSeeds)

  /-- Unfold children from a seed list. -/
  def FTrie.anaChildren {W : Type v} (coalg : AnaCoalgebra V W) :
      Nat → List (UInt8 × W) → List (UInt8 × FTrie V)
    | _, [] => []
    | fuel, (b, s) :: rest =>
      (b, FTrie.ana coalg fuel s) :: FTrie.anaChildren coalg fuel rest
end

/-! ## §2: Base Cases -/

theorem FTrie.ana_zero {W : Type v} (coalg : AnaCoalgebra V W) (seed : W) :
    FTrie.ana coalg 0 seed = .empty := by
  simp [FTrie.ana]

theorem FTrie.anaChildren_nil {W : Type v} (coalg : AnaCoalgebra V W) (fuel : Nat) :
    FTrie.anaChildren coalg fuel ([] : List (UInt8 × W)) = [] := by
  simp [FTrie.anaChildren]

/-! ## §3: Singleton Coalgebra -/

/-- Coalgebra that produces a single-path trie. -/
def singletonCoalg (v : V) : AnaCoalgebra V (List UInt8) where
  unfold
    | [] => ([], some v)
    | b :: rest => ([(b, rest)], none)

theorem FTrie.ana_singleton_nil (v : V) (fuel : Nat) :
    FTrie.ana (singletonCoalg v) (fuel + 1) [] = .node (some v) [] := by
  simp [FTrie.ana, singletonCoalg, FTrie.anaChildren]

theorem FTrie.ana_singleton_cons (v : V) (fuel : Nat) (b : UInt8) (rest : List UInt8) :
    FTrie.ana (singletonCoalg v) (fuel + 1) (b :: rest) =
    .node none [(b, FTrie.ana (singletonCoalg v) fuel rest)] := by
  simp [FTrie.ana, singletonCoalg, FTrie.anaChildren]

/-! ## §4: Summary

**0 sorries. 0 axioms.**

- `AnaCoalgebra V W` — coalgebra structure
- `FTrie.ana` / `FTrie.anaChildren` — mutual structural anamorphism
- `singletonCoalg` with two unfolding theorems
- `ana_zero`, `anaChildren_nil` — base cases
-/

end Mettapedia.OSLF.PathMap.Trie
