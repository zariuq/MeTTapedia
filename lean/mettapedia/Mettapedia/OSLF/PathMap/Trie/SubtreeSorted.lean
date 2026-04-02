import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement

/-!
# subtreeAt preserves Sorted
-/

namespace Mettapedia.OSLF.PathMap.Trie

open FTrie

universe u

variable {V : Type u}

/-- childrenSorted means every child is Sorted. Extract one. -/
private theorem childrenSorted_mem (cs : List (UInt8 × FTrie V))
    (hcs : childrenSorted cs) (k : UInt8) (child : FTrie V)
    (hmem : (k, child) ∈ cs) : child.Sorted := by
  induction cs with
  | nil => simp at hmem
  | cons hd tl ih =>
    obtain ⟨key, ch⟩ := hd
    have ⟨hs_ch, hcs_tl⟩ := hcs
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem'
    · exact hs_ch
    · exact ih hcs_tl hmem'

/-- find? success implies membership. -/
private theorem find_some_mem (cs : List (UInt8 × FTrie V)) (b : UInt8)
    (k : UInt8) (child : FTrie V)
    (hfind : cs.find? (fun (j, _) => j == b) = some (k, child)) :
    (k, child) ∈ cs := by
  induction cs with
  | nil => simp [List.find?] at hfind
  | cons hd tl ih =>
    simp only [List.find?] at hfind
    split at hfind
    · simp at hfind; exact List.mem_cons.mpr (Or.inl hfind.symm)
    · exact List.mem_cons.mpr (Or.inr (ih hfind))

theorem FTrie.subtreeAt_sorted (t : FTrie V) (pfx : List UInt8)
    (hs : t.Sorted) : (t.subtreeAt pfx).Sorted := by
  induction pfx generalizing t with
  | nil => rw [subtreeAt_nil]; exact hs
  | cons b rest ih =>
    match t with
    | .empty => simp [subtreeAt]; exact trivial
    | .node val children =>
      simp only [subtreeAt]
      have ⟨_, hcs⟩ := hs
      match hfind : children.find? (fun (k, _) => k == b) with
      | none => simp [hfind]; exact trivial
      | some (k, child) =>
        simp [hfind]
        have hmem := find_some_mem children b k child hfind
        exact ih child (childrenSorted_mem children hcs k child hmem)

end Mettapedia.OSLF.PathMap.Trie
