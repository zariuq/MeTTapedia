import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement

/-!
# Entries → Keys Bridge

Proves: if `(b :: rest, v) ∈ entriesChildren cs`, then `b` is a key of
some element in `cs`. Combined with Pairwise (sorted keys), this means
the first byte of any entry determines WHICH child it came from.

Then proves: entries_mem_lookup (converse) for Sorted tries.
-/

namespace Mettapedia.OSLF.PathMap.Trie

open FTrie

universe u

variable {V : Type u}

/-! ## §1: First byte of entries comes from child keys -/

/-- If `(p, v) ∈ entriesChildren cs` and `p = b :: rest`, then
    `b` is the first component (key) of some element in `cs`. -/
theorem entriesChildren_first_byte_is_key
    (cs : List (UInt8 × FTrie V)) (b : UInt8) (rest : List UInt8) (v : V)
    (h : (b :: rest, v) ∈ entriesChildren cs) :
    ∃ child, (b, child) ∈ cs := by
  induction cs with
  | nil => simp [entriesChildren] at h
  | cons hd tl ih =>
    obtain ⟨k, child⟩ := hd
    simp only [entriesChildren, List.mem_append] at h
    rcases h with hmap | hrest
    · -- From this child's entries (mapped with k :: prefix)
      simp only [List.mem_map] at hmap
      obtain ⟨⟨suffix, w⟩, _, heq⟩ := hmap
      simp at heq
      exact ⟨child, by simp [heq.1]⟩
    · -- From rest's entries
      obtain ⟨child', hmem⟩ := ih hrest
      exact ⟨child', List.mem_cons_of_mem _ hmem⟩

/-! ## §2: Pairwise + first_byte_is_key → byte inequality -/

/-- If all keys in `rest` are `> b`, and an entry from `entriesChildren rest`
    starts with byte `pb`, then `pb > b` (hence `pb ≠ b`). -/
theorem entriesChildren_first_byte_gt
    (b : UInt8) (rest : List (UInt8 × FTrie V)) (pb : UInt8)
    (prest : List UInt8) (v : V)
    (hall : ∀ p ∈ rest, b < p.1)
    (hentry : (pb :: prest, v) ∈ entriesChildren rest) :
    b < pb := by
  obtain ⟨child, hmem⟩ := entriesChildren_first_byte_is_key rest pb prest v hentry
  exact hall (pb, child) hmem

/-! ## §3: entries_mem_lookup for Sorted tries -/

mutual
  /-- **For sorted tries: entries membership implies lookup success.** -/
  theorem FTrie.entries_mem_lookup (t : FTrie V) (p : List UInt8) (v : V)
      (hs : t.Sorted)
      (h : (p, v) ∈ t.entries) : t.lookup p = some v := by
    match t with
    | .empty => simp [entries] at h
    | .node val children =>
      have ⟨hpw, hcs⟩ := hs
      simp only [entries] at h
      rcases List.mem_append.mp h with hval | hchild
      · match val with
        | some w => simp at hval; obtain ⟨rfl, rfl⟩ := hval; simp [lookup]
        | none => simp at hval
      · match p with
        | [] =>
          -- entries from children always have non-empty paths
          exfalso
          exact entriesChildren_nil_path_absurd children hchild
        | pb :: prest =>
          simp only [lookup]
          exact entriesChildren_to_lookupChild children pb prest v hpw hcs hchild

  /-- Helper: entriesChildren never produces empty paths. -/
  theorem entriesChildren_nil_path_absurd
      (cs : List (UInt8 × FTrie V))
      (h : ([], v) ∈ entriesChildren cs) : False := by
    match cs with
    | [] => simp [entriesChildren] at h
    | (k, child) :: rest =>
      simp only [entriesChildren, List.mem_append] at h
      rcases h with hmap | hrest
      · simp only [List.mem_map] at hmap
        obtain ⟨⟨suffix, w⟩, _, heq⟩ := hmap
        simp at heq
      · exact entriesChildren_nil_path_absurd rest hrest

  /-- Helper: entries from children correspond to lookupChild. -/
  theorem entriesChildren_to_lookupChild
      (cs : List (UInt8 × FTrie V)) (pb : UInt8)
      (prest : List UInt8) (v : V)
      (hpw : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs)
      (hcs : childrenSorted cs)
      (h : (pb :: prest, v) ∈ entriesChildren cs) :
      lookupChild pb prest cs = some v := by
    match cs with
    | [] => simp [entriesChildren] at h
    | (k, child) :: rest =>
      simp only [entriesChildren, List.mem_append] at h
      have hpw' := (List.pairwise_cons.mp hpw).2
      have hall := (List.pairwise_cons.mp hpw).1
      have ⟨hs, hcs'⟩ := hcs
      simp only [lookupChild]
      rcases h with hmap | hrest
      · -- From this child
        simp only [List.mem_map] at hmap
        obtain ⟨⟨suffix, w⟩, hmem, heq⟩ := hmap
        -- heq : (k, suffix) = (pb, prest) ∧ ... → k = pb, suffix = prest, w = v
        simp only [Prod.mk.injEq, List.cons.injEq] at heq
        have ⟨⟨h1, h2⟩, h3⟩ := heq
        subst h1; subst h2; subst h3
        simp only [lookupChild, beq_self_eq_true, ↓reduceIte]
        exact FTrie.entries_mem_lookup child _ _ hs hmem
      · -- From rest: pb is a key from rest, so pb > k (by Pairwise)
        have hgt : k < pb := entriesChildren_first_byte_gt k rest pb prest v hall hrest
        have hne : ¬ (k == pb) = true := by
          intro heq
          have hkeq := beq_iff_eq.mp heq; subst hkeq
          exact absurd hgt (by simp [UInt8.not_lt])
        rw [if_neg hne]
        exact entriesChildren_to_lookupChild rest pb prest v hpw' hcs' hrest
end

end Mettapedia.OSLF.PathMap.Trie
