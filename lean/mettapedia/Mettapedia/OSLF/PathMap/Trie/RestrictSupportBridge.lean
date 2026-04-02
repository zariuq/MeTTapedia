import Mettapedia.OSLF.PathMap.PathPrefixRestrictRefinement
import Mettapedia.OSLF.PathMap.Trie.EntriesKeys
import Mettapedia.OSLF.PathMap.Trie.EntriesLookup
import Mettapedia.OSLF.PathMap.Trie.RestrictRefinement
import Mettapedia.OSLF.PathMap.Trie.UnitBridge

/-!
# Restrict Support Bridge

This file closes the remaining gap for PathMap `restrict` on `FTrie Unit`.

It proves:

1. `restrict` preserves `Sorted`
2. the finite prefix-admission test is exactly existence of a lookup on some
   prefix of the queried path
3. the concrete support of `FTrie.restrict` matches the extensional
   `restrictPaths` semantics from `PathPrefixRestrictRefinement.lean`

Together with `RestrictRefinement.lean`, this connects the concrete trie
implementation all the way up to the extensional path-level oracle.
-/

namespace Mettapedia.OSLF.PathMap.Trie

open FTrie
open Mettapedia.PathMap

universe u

variable {V : Type u}

private theorem uint8_eq_not_lt (a b : UInt8) (h1 : ¬ (a < b)) (h2 : ¬ (b < a)) :
    a = b := by
  rw [UInt8.lt_iff_toNat_lt] at h1 h2
  rw [Nat.not_lt] at h1 h2
  exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.le_antisymm h2 h1))

private theorem normalize_node_none_sorted (cs : List (UInt8 × FTrie V))
    (hpw : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs)
    (hcs : childrenSorted cs) :
    (FTrie.node none cs).normalize.Sorted := by
  cases cs with
  | nil => simp [FTrie.normalize, FTrie.Sorted]
  | cons hd tl => simpa [FTrie.normalize, FTrie.Sorted] using And.intro hpw hcs

mutual
  theorem FTrie.restrict_sorted (t₁ t₂ : FTrie V) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
      (t₁.restrict t₂).Sorted := by
    cases t₁ with
    | empty =>
        simpa [FTrie.restrict]
    | node v₁ c₁ =>
        cases t₂ with
        | empty =>
            simpa [FTrie.restrict]
        | node v₂ c₂ =>
            cases v₂ with
            | some _ =>
                simpa [FTrie.restrict] using h₁
            | none =>
                have ⟨hpw₁, hcs₁⟩ := h₁
                have ⟨hpw₂, hcs₂⟩ := h₂
                simpa [FTrie.restrict] using
                  normalize_node_none_sorted _
                    (restrictChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).1
                    (restrictChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).2

  theorem restrictChildren_sorted
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (hpw₁ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₁)
      (hpw₂ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₂)
      (hcs₁ : childrenSorted cs₁) (hcs₂ : childrenSorted cs₂) :
      List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) (restrictChildren cs₁ cs₂) ∧
      childrenSorted (restrictChildren cs₁ cs₂) := by
    match cs₁, cs₂ with
    | [], _ =>
        unfold FTrie.restrictChildren
        exact ⟨by simp, trivial⟩
    | (b₁, t₁) :: rest₁, [] =>
        unfold FTrie.restrictChildren
        exact ⟨by simp, trivial⟩
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
        unfold FTrie.restrictChildren
        have hpw₁' := (List.pairwise_cons.mp hpw₁).2
        have hall₁ := (List.pairwise_cons.mp hpw₁).1
        have hpw₂' := (List.pairwise_cons.mp hpw₂).2
        have hall₂ := (List.pairwise_cons.mp hpw₂).1
        have ⟨hs₁, hcs₁'⟩ := hcs₁
        have ⟨hs₂, hcs₂'⟩ := hcs₂
        split
        · exact restrictChildren_sorted rest₁ ((b₂, t₂) :: rest₂) hpw₁' hpw₂ hcs₁' hcs₂
        · split
          · exact restrictChildren_sorted ((b₁, t₁) :: rest₁) rest₂ hpw₁ hpw₂' hcs₁ hcs₂'
          · have heq := uint8_eq_not_lt _ _ ‹¬ b₁ < b₂› ‹¬ b₂ < b₁›
            subst heq
            have ⟨ihpw, ihcs⟩ := restrictChildren_sorted rest₁ rest₂ hpw₁' hpw₂' hcs₁' hcs₂'
            cases hr : restrict t₁ t₂ with
            | empty =>
                exact ⟨ihpw, ihcs⟩
            | node v cs =>
                exact ⟨List.pairwise_cons.mpr
                  ⟨rc_gt b₁ rest₁ rest₂ hall₁ hall₂, ihpw⟩,
                  by rw [← hr]; exact FTrie.restrict_sorted t₁ t₂ hs₁ hs₂,
                  ihcs⟩

  theorem rc_gt (b : UInt8)
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (h₁ : ∀ p ∈ cs₁, b < p.1) (h₂ : ∀ p ∈ cs₂, b < p.1) :
      ∀ p ∈ restrictChildren cs₁ cs₂, b < p.1 := by
    match cs₁, cs₂ with
    | [], _ =>
        unfold FTrie.restrictChildren
        intro p hp
        simp at hp
    | (b₁, t₁) :: rest₁, [] =>
        unfold FTrie.restrictChildren
        intro p hp
        simp at hp
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
        unfold FTrie.restrictChildren
        have hb₁ := h₁ _ (.head _)
        have hb₂ := h₂ _ (.head _)
        have h₁' : ∀ q ∈ rest₁, b < q.1 := fun q hq => h₁ q (.tail _ hq)
        have h₂' : ∀ q ∈ rest₂, b < q.1 := fun q hq => h₂ q (.tail _ hq)
        intro p
        split
        · intro hp
          exact rc_gt b rest₁ ((b₂, t₂) :: rest₂) h₁' h₂ p hp
        · split
          · intro hp
            exact rc_gt b ((b₁, t₁) :: rest₁) rest₂ h₁ h₂' p hp
          · intro hp
            generalize hm : restrict t₁ t₂ = merged at hp
            match merged, hp with
            | .empty, hp =>
                exact rc_gt b rest₁ rest₂ h₁' h₂' p hp
            | .node _ _, hp =>
                rcases List.mem_cons.mp hp with rfl | hm'
                · exact hb₁
                · exact rc_gt b rest₁ rest₂ h₁' h₂' p hm'
end

namespace FTrie

/-- Extensional path support of a `Unit`-valued trie. -/
noncomputable def pathSupport (t : FTrie Unit) : Finset BytePath :=
  t.pathList.toFinset

theorem pathSupport_mem_of_lookup (t : FTrie Unit) (p : BytePath)
    (h : t.lookup p = some ()) :
    p ∈ t.pathSupport := by
  apply List.mem_toFinset.mpr
  change p ∈ t.pathList
  rw [FTrie.pathList, List.mem_map]
  simpa using (show ∃ x : Unit, (p, x) ∈ t.entries from ⟨(), FTrie.lookup_mem_entries t p () h⟩)

theorem lookup_of_pathSupport_mem (t : FTrie Unit) (p : BytePath)
    (hs : t.Sorted) (h : p ∈ t.pathSupport) :
    t.lookup p = some () := by
  apply FTrie.entries_mem_lookup t p () hs
  have hList : p ∈ t.pathList := by
    exact List.mem_toFinset.mp (by simpa [FTrie.pathSupport] using h)
  rw [FTrie.pathList] at hList
  rw [List.mem_map] at hList
  rcases hList with ⟨⟨q, v⟩, hEntry, hEq⟩
  simp at hEq
  subst q
  cases v
  simpa using hEntry

namespace CTrie

theorem hasPrefix_lookup_iff (t : CTrie Unit) (p : BytePath) :
    CTrie.hasPrefix t p = true ↔ ∃ q, q <+: p ∧ t q = some () := by
  induction p generalizing t with
  | nil =>
      cases hroot : t [] with
      | none =>
          constructor
          · simp [CTrie.hasPrefix, hroot]
          · intro h
            rcases h with ⟨q, hq, hLookup⟩
            have : q = [] := List.prefix_nil.mp hq
            subst this
            simp [hroot] at hLookup
      | some v =>
          cases v
          constructor
          · intro _
            exact ⟨[], by simp, hroot⟩
          · intro _
            simp [CTrie.hasPrefix, hroot]
  | cons b rest ih =>
      cases hroot : t [] with
      | some v =>
          cases v
          constructor
          · intro _
            exact ⟨[], by simp, hroot⟩
          · intro _
            simp [CTrie.hasPrefix, hroot]
      | none =>
          constructor
          · intro h
            have hTail : CTrie.hasPrefix (fun q => t (b :: q)) rest = true := by
              simpa [CTrie.hasPrefix, hroot] using h
            rcases (ih (fun q => t (b :: q))).mp hTail with ⟨q, hqp, hLookup⟩
            exact ⟨b :: q, List.cons_prefix_cons.mpr ⟨rfl, hqp⟩, hLookup⟩
          · intro h
            rcases h with ⟨q, hqp, hLookup⟩
            cases q with
            | nil =>
                simp [hroot] at hLookup
            | cons qb qrest =>
                obtain ⟨hHead, hRest⟩ := List.cons_prefix_cons.mp hqp
                have hTail : CTrie.hasPrefix (fun q => t (qb :: q)) rest = true :=
                  (ih (fun q => t (qb :: q))).mpr ⟨qrest, hRest, hLookup⟩
                simpa [CTrie.hasPrefix, hroot, hHead] using hTail

end CTrie

theorem hasValuedPrefix_lookup_iff (t : FTrie Unit) (p : BytePath) :
    t.hasValuedPrefix p = true ↔ ∃ q, q <+: p ∧ t.lookup q = some () := by
  rw [FTrie.hasValuedPrefix_eq_toCTrie_hasPrefix]
  simpa [FTrie.toCTrie_apply] using (CTrie.hasPrefix_lookup_iff t.toCTrie p)

theorem allows_pathSupport_iff_hasValuedPrefix (t : FTrie Unit) (p : BytePath)
    (hs : t.Sorted) :
    Allows t.pathSupport p ↔ t.hasValuedPrefix p = true := by
  constructor
  · intro h
    rcases h with ⟨q, hq, hqp⟩
    have hLookup : t.lookup q = some () := lookup_of_pathSupport_mem t q hs hq
    exact (hasValuedPrefix_lookup_iff t p).mpr ⟨q, hqp, hLookup⟩
  · intro h
    rcases (hasValuedPrefix_lookup_iff t p).mp h with ⟨q, hqp, hLookup⟩
    exact ⟨q, pathSupport_mem_of_lookup t q hLookup, hqp⟩

theorem pathSupport_restrict_eq_restrictPaths
    (t₁ t₂ : FTrie Unit) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    (t₁.restrict t₂).pathSupport = restrictPaths t₁.pathSupport t₂.pathSupport := by
  apply Finset.ext
  intro p
  rw [restrictPaths_mem_iff]
  constructor
  · intro hp
    have hLookup : (t₁.restrict t₂).lookup p = some () :=
      lookup_of_pathSupport_mem _ _ (FTrie.restrict_sorted t₁ t₂ h₁ h₂) hp
    rw [FTrie.restrict_lookup t₁ t₂ p h₁ h₂] at hLookup
    cases hPref : t₂.hasValuedPrefix p with
    | false =>
        simp [hPref] at hLookup
    | true =>
        simp [hPref] at hLookup
        exact ⟨pathSupport_mem_of_lookup _ _ hLookup,
          (allows_pathSupport_iff_hasValuedPrefix t₂ p h₂).2 hPref⟩
  · intro hp
    rcases hp with ⟨hp₁, hp₂⟩
    have hLookup₁ : t₁.lookup p = some () := lookup_of_pathSupport_mem _ _ h₁ hp₁
    have hPref : t₂.hasValuedPrefix p = true :=
      (allows_pathSupport_iff_hasValuedPrefix t₂ p h₂).1 hp₂
    have hRestrict : (t₁.restrict t₂).lookup p = some () := by
      rw [FTrie.restrict_lookup t₁ t₂ p h₁ h₂, hPref, hLookup₁]
      simp
    exact pathSupport_mem_of_lookup _ _ hRestrict

end FTrie

end Mettapedia.OSLF.PathMap.Trie
