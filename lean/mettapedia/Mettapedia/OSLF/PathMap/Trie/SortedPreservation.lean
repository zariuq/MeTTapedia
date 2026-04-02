import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement
import Mettapedia.OSLF.PathMap.Trie.UnitBridge

/-!
# Sortedness Preservation + fromPathList End-to-End
-/

namespace Mettapedia.OSLF.PathMap.Trie

open FTrie

universe u

variable {V : Type u}

private theorem uint8_eq_not_lt (a b : UInt8) (h1 : ¬(a < b)) (h2 : ¬(b < a)) :
    a = b := by
  rw [UInt8.lt_iff_toNat_lt] at h1 h2; rw [Nat.not_lt] at h1 h2
  exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.le_antisymm h2 h1))

theorem FTrie.singleton_lookup_ne (p q : List UInt8) (v : V) (hne : p ≠ q) :
    (FTrie.singleton p v).lookup q = none := by
  induction p generalizing q with
  | nil => match q with
    | [] => exact absurd rfl hne
    | _ :: _ => simp [singleton, lookup, lookupChild]
  | cons b rest ih =>
    match q with
    | [] => simp [singleton, lookup]
    | qb :: qrest =>
      simp only [singleton, lookup, lookupChild]
      by_cases hbq : (b == qb) = true
      · have := beq_iff_eq.mp hbq; subst this; simp
        exact ih qrest (fun h => hne (congrArg (b :: ·) h))
      · simp [hbq]

/-! ## Boss battle: 3-theorem mutual block -/

mutual
  theorem FTrie.join_sorted (t₁ t₂ : FTrie V) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
      (join t₁ t₂).Sorted := by
    cases t₁ with
    | empty => unfold join; exact h₂
    | node v₁ c₁ =>
      cases t₂ with
      | empty =>
        have : join (.node v₁ c₁) .empty = .node v₁ c₁ := by unfold join; rfl
        rw [this]; exact h₁
      | node v₂ c₂ =>
        unfold join
        have ⟨hpw₁, hcs₁⟩ := h₁
        have ⟨hpw₂, hcs₂⟩ := h₂
        exact joinChildren_sorted c₁ c₂ hpw₁ hpw₂ hcs₁ hcs₂

  theorem joinChildren_sorted
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (hpw₁ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₁)
      (hpw₂ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₂)
      (hcs₁ : childrenSorted cs₁) (hcs₂ : childrenSorted cs₂) :
      List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) (joinChildren cs₁ cs₂) ∧
      childrenSorted (joinChildren cs₁ cs₂) := by
    match cs₁, cs₂ with
    | [], _ => unfold joinChildren; exact ⟨hpw₂, hcs₂⟩
    | (b₁, t₁) :: rest₁, [] =>
      have : joinChildren ((b₁, t₁) :: rest₁) ([] : List (UInt8 × FTrie V)) =
          (b₁, t₁) :: rest₁ := by unfold joinChildren; rfl
      rw [this]; exact ⟨hpw₁, hcs₁⟩
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
      unfold joinChildren
      have hpw₁' := (List.pairwise_cons.mp hpw₁).2
      have hall₁ := (List.pairwise_cons.mp hpw₁).1
      have hpw₂' := (List.pairwise_cons.mp hpw₂).2
      have hall₂ := (List.pairwise_cons.mp hpw₂).1
      have ⟨hs₁, hcs₁'⟩ := hcs₁
      have ⟨hs₂, hcs₂'⟩ := hcs₂
      split
      · -- b₁ < b₂
        rename_i hlt
        have ⟨ihpw, ihcs⟩ := joinChildren_sorted rest₁ ((b₂, t₂) :: rest₂)
          hpw₁' hpw₂ hcs₁' hcs₂
        exact ⟨List.pairwise_cons.mpr
          ⟨jc_gt b₁ rest₁ ((b₂, t₂) :: rest₂) hall₁
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hm
              · exact hlt
              · exact Trans.trans hlt (hall₂ p hm)),
           ihpw⟩,
          hs₁, ihcs⟩
      · split
        · -- b₂ < b₁
          rename_i _ hlt₂
          have ⟨ihpw, ihcs⟩ := joinChildren_sorted ((b₁, t₁) :: rest₁) rest₂
            hpw₁ hpw₂' hcs₁ hcs₂'
          exact ⟨List.pairwise_cons.mpr
            ⟨jc_gt b₂ ((b₁, t₁) :: rest₁) rest₂
              (fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hm
                · exact hlt₂
                · exact Trans.trans hlt₂ (hall₁ p hm))
              hall₂,
             ihpw⟩,
            hs₂, ihcs⟩
        · -- b₁ = b₂
          rename_i hn₁ hn₂
          have heq := uint8_eq_not_lt _ _ hn₁ hn₂
          subst heq
          have ⟨ihpw, ihcs⟩ := joinChildren_sorted rest₁ rest₂
            hpw₁' hpw₂' hcs₁' hcs₂'
          cases hj : join t₁ t₂ with
          | empty => exact ⟨ihpw, ihcs⟩
          | node v cs =>
            exact ⟨List.pairwise_cons.mpr
              ⟨jc_gt b₁ rest₁ rest₂ hall₁ hall₂, ihpw⟩,
              by rw [← hj]; exact FTrie.join_sorted t₁ t₂ hs₁ hs₂,
              ihcs⟩

  theorem jc_gt (b : UInt8)
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (h₁ : ∀ p ∈ cs₁, b < p.1) (h₂ : ∀ p ∈ cs₂, b < p.1) :
      ∀ p ∈ joinChildren cs₁ cs₂, b < p.1 := by
    match cs₁, cs₂ with
    | [], _ => unfold joinChildren; exact h₂
    | (b₁, t₁) :: rest₁, [] =>
      have : joinChildren ((b₁, t₁) :: rest₁) ([] : List (UInt8 × FTrie V)) =
          (b₁, t₁) :: rest₁ := by unfold joinChildren; rfl
      rw [this]; exact h₁
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
      unfold joinChildren
      have hb₁ := h₁ _ (.head _)
      have hb₂ := h₂ _ (.head _)
      have h₁' : ∀ q ∈ rest₁, b < q.1 := fun q hq => h₁ q (.tail _ hq)
      have h₂' : ∀ q ∈ rest₂, b < q.1 := fun q hq => h₂ q (.tail _ hq)
      intro p
      split
      · -- b₁ < b₂
        intro hp; rcases List.mem_cons.mp hp with rfl | hm
        · exact hb₁
        · exact jc_gt b rest₁ ((b₂, t₂) :: rest₂) h₁' h₂ p hm
      · split
        · -- b₂ < b₁
          intro hp; rcases List.mem_cons.mp hp with rfl | hm
          · exact hb₂
          · exact jc_gt b ((b₁, t₁) :: rest₁) rest₂ h₁ h₂' p hm
        · -- b₁ = b₂
          -- The unfolded joinChildren has: let merged := join t₁ t₂; match merged with ...
          -- We need to case-split on the value of `merged`
          intro hp
          generalize hm : join t₁ t₂ = merged at hp
          match merged, hp with
          | .empty, hp => exact jc_gt b rest₁ rest₂ h₁' h₂' p hp
          | .node _ _, hp =>
            rcases List.mem_cons.mp hp with rfl | hm'
            · exact hb₁
            · exact jc_gt b rest₁ rest₂ h₁' h₂' p hm'
end

/-! ## fromPathList pipeline -/

theorem FTrie.fromPathList_sorted (paths : List (List UInt8)) :
    (FTrie.fromPathList paths).Sorted := by
  induction paths with
  | nil => exact trivial
  | cons p rest ih =>
    simp only [FTrie.fromPathList]
    exact FTrie.join_sorted _ _ (FTrie.singleton_sorted p ()) ih

theorem FTrie.fromPathList_mem (paths : List (List UInt8)) (q : List UInt8)
    (hmem : q ∈ paths) :
    (FTrie.fromPathList paths).lookup q = some () := by
  induction paths with
  | nil => simp at hmem
  | cons p rest ih =>
    simp only [FTrie.fromPathList]
    rw [FTrie.join_lookup _ _ _
        (FTrie.singleton_sorted p ()) (FTrie.fromPathList_sorted rest)]
    rcases List.mem_cons.mp hmem with rfl | hrest
    · simp [singleton_lookup_self]
    · have := ih hrest; simp [this]

end Mettapedia.OSLF.PathMap.Trie
