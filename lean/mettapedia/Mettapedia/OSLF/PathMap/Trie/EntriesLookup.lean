import Mettapedia.OSLF.PathMap.Trie.FiniteTrie

/-!
# Lookup ↔ Entries Bridge

Forward direction (sorry-free): lookup → entries.
Converse direction: needs Sorted hypothesis, deferred to next session.
-/

namespace Mettapedia.OSLF.PathMap.Trie

open FTrie

universe u

variable {V : Type u}

mutual
  theorem FTrie.lookup_mem_entries (t : FTrie V) (p : List UInt8) (v : V)
      (h : t.lookup p = some v) : (p, v) ∈ t.entries := by
    match t with
    | .empty => simp [lookup] at h
    | .node val children =>
      match p with
      | [] => simp only [lookup] at h; subst h; simp [entries]
      | b :: rest =>
        simp only [lookup] at h; simp only [entries]
        apply List.mem_append_right
        exact lookupChild_mem_entries children b rest v h

  theorem lookupChild_mem_entries (cs : List (UInt8 × FTrie V))
      (b : UInt8) (rest : List UInt8) (v : V)
      (h : lookupChild b rest cs = some v) :
      (b :: rest, v) ∈ entriesChildren cs := by
    match cs with
    | [] => simp [lookupChild] at h
    | (k, child) :: tl =>
      simp only [lookupChild] at h; simp only [entriesChildren, List.mem_append]
      by_cases hkb : (k == b) = true
      · rw [if_pos hkb] at h
        left; exact List.mem_map.mpr ⟨(rest, v),
          FTrie.lookup_mem_entries child rest v h,
          by rw [beq_iff_eq.mp hkb]⟩
      · rw [if_neg hkb] at h
        right; exact lookupChild_mem_entries tl b rest v h
end

end Mettapedia.OSLF.PathMap.Trie
