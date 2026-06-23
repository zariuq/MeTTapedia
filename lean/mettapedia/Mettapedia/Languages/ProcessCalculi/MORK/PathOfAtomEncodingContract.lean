import Mettapedia.OSLF.PathMap.Trie.DescendUntilRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.Syntax

/-!
# Path-of-Atom Encoding Contract

Formalizes the bridge algorithm shape behind CeTTa's `mork:path-of-atom`.

The live bridge does not guess a symbolic path. It:

1. renders an atom to text
2. parses that text into a fresh singleton PathMap
3. creates a cursor at the root of that singleton trie
4. runs `descend_until`
5. returns the resulting byte path

This file captures the theorem content of that pipeline without pretending Lean
already contains the exact Rust parser/renderer implementation.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.PathMap.Trie
open Mettapedia.OSLF.PathMap.Trie.FTrie

/-- Contract for the `path-of-atom` bridge algorithm.

`parseRendered` abstracts the live bridge path from rendered atom text to the
singleton trie that PathMap actually traverses. -/
structure PathOfAtomContract where
  render : Atom → String
  parseRendered : String → FTrie Unit
  encodedPath : Atom → List UInt8
  parse_rendered_singleton :
    ∀ a, parseRendered (render a) = FTrie.singleton (encodedPath a) ()

/-- The pure trie-level computation performed by the bridge:
render, parse into a fresh singleton trie, then descend-until from the root. -/
def pathOfAtom (contract : PathOfAtomContract) (a : Atom) : List UInt8 :=
  FTrie.descendUntilPath (contract.parseRendered (contract.render a)) []

/-- A singleton trie is completely traversed by root `descend_until`. -/
theorem singleton_descendUntilPath_root (p : List UInt8) :
    FTrie.descendUntilPath (FTrie.singleton p ()) [] = p := by
  induction p with
  | nil =>
      simp [FTrie.descendUntilPath, FTrie.singleton, FTrie.subtreeAt]
  | cons b rest ih =>
      cases rest with
      | nil =>
          simp [FTrie.descendUntilPath, FTrie.singleton, FTrie.descendUntilSuffix,
            FTrie.rootVal?, FTrie.subtreeAt]
      | cons c cs =>
          simp [FTrie.descendUntilPath, FTrie.singleton, FTrie.descendUntilSuffix,
            FTrie.rootVal?, FTrie.subtreeAt]
          simpa [FTrie.descendUntilPath, FTrie.subtreeAt_nil, FTrie.singleton,
            FTrie.descendUntilSuffix, FTrie.rootVal?] using ih

/-- Under the singleton-parse contract, `path-of-atom` returns the encoded byte path. -/
theorem pathOfAtom_eq_encodedPath (contract : PathOfAtomContract) (a : Atom) :
    pathOfAtom contract a = contract.encodedPath a := by
  rw [pathOfAtom, contract.parse_rendered_singleton]
  exact singleton_descendUntilPath_root (contract.encodedPath a)

/-! ## Examples -/

/-- Positive example: on an isolated singleton parse result, root
`descend_until` reaches the entire byte path. -/
example :
    FTrie.descendUntilPath (FTrie.singleton [1, 2, 3] ()) [] = [1, 2, 3] := by
  exact singleton_descendUntilPath_root [1, 2, 3]

/-- Negative example: if two rendered atoms shared one trie, branch structure
would stop root `descend_until` immediately. This is why the bridge uses a
fresh singleton parse space for `path-of-atom`. -/
example :
    FTrie.descendUntilPath
      (FTrie.join (FTrie.singleton [1] ()) (FTrie.singleton [2] ())) [] = [] := by
  simp [FTrie.descendUntilPath, FTrie.subtreeAt_nil, FTrie.join,
    FTrie.joinChildren, FTrie.singleton]

/-! ## Summary

This file does not try to re-implement the Rust parser in Lean. Instead it
states the exact theorem-shaped contract that the bridge algorithm relies on:

- rendering + parsing a single atom yields a singleton trie at the encoded path
- root `descend_until` on that singleton trie returns the full encoded path

So `mork:path-of-atom` is mathematically justified by the singleton parse
contract, not by an informal promise about symbolic surface syntax.
-/

end Mettapedia.Languages.ProcessCalculi.MORK
