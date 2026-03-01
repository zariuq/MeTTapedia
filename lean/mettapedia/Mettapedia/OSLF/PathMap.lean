import Mettapedia.OSLF.PathMap.Core
import Mettapedia.OSLF.PathMap.RelationBridge
import Mettapedia.OSLF.PathMap.Zipper
import Mettapedia.OSLF.PathMap.ZipperExecution
import Mettapedia.OSLF.PathMap.FlatZipperInstance
import Mettapedia.OSLF.PathMap.OSLFInstance
import Mettapedia.OSLF.PathMap.PLNBridge
import Mettapedia.OSLF.PathMap.SolomonoffBridge
import Mettapedia.OSLF.PathMap.Measure
import Mettapedia.OSLF.PathMap.WorldModelBridge
import Mettapedia.OSLF.PathMap.Trie.CoinductiveTrie
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement
import Mettapedia.OSLF.PathMap.Trie.TriePathMapInstance
import Mettapedia.OSLF.PathMap.Trie.TrieZipper
import Mettapedia.OSLF.PathMap.Trie.ZamContracts

/-!
# PathMap Formalization

Lean 4 formalization of PathMap's algebraic interface, providing:

1. `PathMap.Core` — `AlgebraicResult`, `PathMapLattice`, `PathMapDistributiveLattice`,
   `PathMapQuantale` typeclasses with algebraic laws (`JoinComm`, `MeetComm`,
   `JoinIdem`, `MeetIdem`, `Absorption`).  Concrete instances for `Bool` (all 5
   laws) and `Finset α` (all 5 laws).

2. `PathMap.Zipper` — `ZipperMoving`, `ZipperValues`, `ZipperWriting`,
   `ZipperIteration`, `ZipperForking`, `ZipperAbsolutePath` typeclass hierarchy
   with the fundamental invariant ("focus cannot move above root") and
   `SubtractLeftBiased` (`psubtract` never returns `COUNTER_IDENT`).

3. `PathMap.ZipperExecution` — `ZipperIterationSound` contract: zipper-based
   traversal collects exactly the stored values.  ZAM soundness theorems
   connecting zipper execution to OSLF reduction and modal operators.

4. `PathMap.FlatZipperInstance` — Reference `ZipperIterationSound` instance
   (flat list, no trie structure).  Validates the contract is satisfiable.

5. `PathMap.RelationBridge` — `RelationalSpace` typeclass abstracting the current
   `RelationEnv` (list-of-tuples) interface.

6. `PathMap.Trie.*` — Byte-indexed trie formalization (970 lines, 0 sorries):
   - `CoinductiveTrie` — `CTrie V`: coalgebraic trie, bisimulation, algebraic laws
   - `FiniteTrie` — `FTrie V`: inductive trie, join/meet/subtract/restrict
   - `TrieRefinement` — `FTrie → CTrie` embedding, `join_lookup` homomorphism
   - `TriePathMapInstance` — `PathMapQuantale (FTrie V)` + `JoinIdem` / `MeetIdem`
   - `TrieZipper` — `SimpleTrieZipper V`, `ZipperIterationSound` proof

## Relationship to OSLF

The OSLF's `RelationEnv` (`MeTTaIL/Engine.lean`) is the current concrete backend
for the `relationQuery` premise type.  PathMap is the planned replacement from
the MORK project.  The `RelationalSpace` typeclass in `RelationBridge` ensures
the OSLF formalization is not coupled to any specific storage backend.

The trie stack provides the first concrete `PathMapQuantale` instance backed by
an actual trie data structure (as opposed to flat `Finset` or `Bool` instances).

## References
- PathMap `ring.rs`: `/home/zar/claude/hyperon/PathMap/src/ring.rs`
- PathMap book:      `1.01.00_algebraic_ops.md`, `1.01.01_algebraic_traits.md`
- MORK kernel:       `/home/zar/claude/hyperon/MORK/`
- Abel, "Formal Languages, Coinductively Formalized in Agda" (Ljubljana 2017)
- Traytel et al., "Formal Languages, Formally and Coinductively" (FSCD 2016)
-/
