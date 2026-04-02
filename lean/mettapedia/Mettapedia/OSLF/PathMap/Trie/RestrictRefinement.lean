import Mettapedia.OSLF.PathMap.Trie.CoinductiveTrie
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement

/-!
# Restrict Refinement — `FTrie.restrict` ↪ Prefix Semantics

This file pins the finite trie `restrict` implementation to the coinductive
prefix semantics.

The proof has two layers:

1. `hasValuedPrefix` is the finite, computable prefix-admission test.  It is
   shown equivalent to `CTrie.hasPrefix` on the embedded coinductive trie.
2. `restrict_lookup` proves that `FTrie.restrict` keeps exactly those lhs
   lookups whose rhs admits some valued prefix.

This is the trie-level theorem slice needed before connecting the concrete trie
implementation back to the extensional support semantics for PathMap `restrict`.
-/

namespace Mettapedia.OSLF.PathMap.Trie

universe u

namespace FTrie

variable {V : Type u}

mutual
  /-- Finite, computable prefix-admission test for `FTrie`. -/
  def hasValuedPrefix : FTrie V → List UInt8 → Bool
    | .empty, _ => false
    | .node val _, [] => val.isSome
    | .node val children, b :: rest =>
        val.isSome || hasValuedPrefixChild b rest children

  /-- Child-list helper for `hasValuedPrefix`. -/
  def hasValuedPrefixChild (b : UInt8) (rest : List UInt8) :
      List (UInt8 × FTrie V) → Bool
    | [] => false
    | (k, child) :: cs =>
        if k == b then hasValuedPrefix child rest
        else hasValuedPrefixChild b rest cs
end

@[simp] theorem hasValuedPrefix_empty (p : List UInt8) :
    (FTrie.empty : FTrie V).hasValuedPrefix p = false := rfl

@[simp] theorem hasValuedPrefixChild_nil (b : UInt8) (rest : List UInt8) :
    hasValuedPrefixChild (V := V) b rest [] = false := rfl

theorem hasValuedPrefixChild_cons_eq (k : UInt8) (child : FTrie V)
    (cs : List (UInt8 × FTrie V)) (b : UInt8) (rest : List UInt8) (h : k = b) :
    hasValuedPrefixChild b rest ((k, child) :: cs) = child.hasValuedPrefix rest := by
  subst h
  simp [hasValuedPrefixChild]

theorem hasValuedPrefixChild_cons_ne (k : UInt8) (child : FTrie V)
    (cs : List (UInt8 × FTrie V)) (b : UInt8) (rest : List UInt8) (h : k ≠ b) :
    hasValuedPrefixChild b rest ((k, child) :: cs) = hasValuedPrefixChild b rest cs := by
  simp [hasValuedPrefixChild, h]

theorem hasValuedPrefixChild_false_of_forall_lt (b : UInt8) (rest : List UInt8)
    (cs : List (UInt8 × FTrie V)) (h : ∀ p ∈ cs, b < p.1) :
    hasValuedPrefixChild b rest cs = false := by
  induction cs with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨k, child⟩ := hd
      have hk : b < k := h _ List.mem_cons_self
      have hne : k ≠ b := by
        intro hkEq
        subst hkEq
        simp at hk
      have htl : ∀ p ∈ tl, b < p.1 := fun p hp =>
        h p (List.mem_cons_of_mem _ hp)
      simp [hasValuedPrefixChild, hne, ih htl]

private theorem hasPrefix_const_none : ∀ (p : List UInt8),
    CTrie.hasPrefix (fun (_ : List UInt8) => (none : Option V)) p = false := by
  intro p
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [CTrie.hasPrefix, ih]

@[simp] theorem normalize_node_none_lookup_nil (cs : List (UInt8 × FTrie V)) :
    (FTrie.node none cs).normalize.lookup [] = none := by
  cases cs <;> simp [FTrie.normalize, FTrie.lookup]

@[simp] theorem normalize_node_none_lookup_cons (cs : List (UInt8 × FTrie V))
    (b : UInt8) (rest : List UInt8) :
    (FTrie.node none cs).normalize.lookup (b :: rest) = lookupChild b rest cs := by
  cases cs <;> simp [FTrie.normalize, FTrie.lookup]

mutual
  /-- The finite prefix-admission test agrees with the coinductive one. -/
  theorem hasValuedPrefix_eq_toCTrie_hasPrefix
      (t : FTrie V) (p : List UInt8) :
      t.hasValuedPrefix p = t.toCTrie.hasPrefix p := by
    match t with
    | .empty =>
        cases p with
        | nil => rfl
        | cons _ rest =>
            simp [hasValuedPrefix, CTrie.hasPrefix, toCTrie_apply, FTrie.lookup,
              hasPrefix_const_none rest]
    | .node val children =>
        cases p with
        | nil =>
            simp [hasValuedPrefix, CTrie.hasPrefix, toCTrie_apply, FTrie.lookup]
        | cons b rest =>
            have hChild := hasValuedPrefixChild_eq_lookupChild_hasPrefix children b rest
            simpa [hasValuedPrefix, CTrie.hasPrefix, toCTrie_apply, FTrie.lookup] using
              congrArg (fun x => val.isSome || x) hChild

  /-- Child-list version of `hasValuedPrefix_eq_toCTrie_hasPrefix`. -/
  theorem hasValuedPrefixChild_eq_lookupChild_hasPrefix
      (cs : List (UInt8 × FTrie V)) (b : UInt8) (rest : List UInt8) :
      hasValuedPrefixChild b rest cs =
        CTrie.hasPrefix (fun p => lookupChild b p cs) rest := by
    induction cs with
    | nil =>
        cases rest with
        | nil => rfl
        | cons _ tail =>
            simp [hasValuedPrefixChild, CTrie.hasPrefix, lookupChild,
              hasPrefix_const_none tail]
    | cons hd tl ih =>
        obtain ⟨k, child⟩ := hd
        by_cases hkb : k = b
        · subst hkb
          simpa [hasValuedPrefixChild, lookupChild, toCTrie_apply] using
            (hasValuedPrefix_eq_toCTrie_hasPrefix child rest)
        · simp [hasValuedPrefixChild, lookupChild, hkb, ih]
end

private theorem uint8_eq_of_not_lt_not_lt (a b : UInt8)
    (h1 : ¬ (a < b)) (h2 : ¬ (b < a)) : a = b := by
  rw [UInt8.lt_iff_toNat_lt] at h1 h2
  rw [Nat.not_lt] at h1 h2
  exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.le_antisymm h2 h1))

mutual
  /-- `restrict` agrees with the finite prefix-admission test on lookup. -/
  theorem restrict_lookup (t₁ t₂ : FTrie V) (p : List UInt8)
      (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
      (t₁.restrict t₂).lookup p =
        if t₂.hasValuedPrefix p then t₁.lookup p else none := by
    cases t₁ with
    | empty =>
        simp [FTrie.restrict, FTrie.lookup]
    | node v₁ c₁ =>
        cases t₂ with
        | empty =>
            simp [FTrie.restrict, hasValuedPrefix]
        | node v₂ c₂ =>
            cases v₂ with
            | some v =>
                cases p with
                | nil =>
                    simp [FTrie.restrict, FTrie.lookup, hasValuedPrefix]
                | cons b rest =>
                    simp [FTrie.restrict, FTrie.lookup, hasValuedPrefix]
            | none =>
                cases p with
                | nil =>
                    simp [FTrie.restrict, hasValuedPrefix]
                | cons b rest =>
                    have ⟨hpw₁, hcs₁⟩ := h₁
                    have ⟨hpw₂, hcs₂⟩ := h₂
                    simpa [FTrie.restrict, FTrie.lookup, hasValuedPrefix] using
                      restrictChildren_lookup c₁ c₂ b rest hpw₁ hpw₂ hcs₁ hcs₂

  /-- Child-list helper for `restrict_lookup`. -/
  theorem restrictChildren_lookup
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (b : UInt8) (rest : List UInt8)
      (hpw₁ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₁)
      (hpw₂ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₂)
      (hcs₁ : childrenSorted cs₁) (hcs₂ : childrenSorted cs₂) :
      lookupChild b rest (restrictChildren cs₁ cs₂) =
        if hasValuedPrefixChild b rest cs₂ then lookupChild b rest cs₁ else none := by
    match cs₁, cs₂ with
    | [], cs₂ =>
        simp [FTrie.restrictChildren, lookupChild]
    | cs₁, [] =>
        cases cs₁ <;> simp [FTrie.restrictChildren, hasValuedPrefixChild]
    | (k1, t1) :: rest1, (k2, t2) :: rest2 =>
        unfold FTrie.restrictChildren
        have hpw₁' := (List.pairwise_cons.mp hpw₁).2
        have hall₁ := (List.pairwise_cons.mp hpw₁).1
        have hpw₂' := (List.pairwise_cons.mp hpw₂).2
        have hall₂ := (List.pairwise_cons.mp hpw₂).1
        have ⟨hs₁, hcs₁'⟩ := hcs₁
        have ⟨hs₂, hcs₂'⟩ := hcs₂
        split
        · rename_i hlt
          by_cases hb : b = k1
          · subst hb
            have hselFalse :
                hasValuedPrefixChild b rest ((k2, t2) :: rest2) = false := by
              apply hasValuedPrefixChild_false_of_forall_lt
              intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact hlt
              · exact Trans.trans hlt (hall₂ p hp)
            rw [restrictChildren_lookup rest1 ((k2, t2) :: rest2) b rest
              hpw₁' hpw₂ hcs₁' hcs₂, hselFalse]
            simp
          · rw [lookupChild_cons_ne _ _ _ _ _ (Ne.symm hb)]
            exact restrictChildren_lookup rest1 ((k2, t2) :: rest2) b rest
              hpw₁' hpw₂ hcs₁' hcs₂
        · split
          · rename_i _ hlt
            by_cases hb : b = k2
            · subst hb
              have hnone :
                  lookupChild b rest ((k1, t1) :: rest1) = none := by
                apply lookupChild_none_of_forall_lt
                intro p hp
                rcases List.mem_cons.mp hp with rfl | hp
                · exact hlt
                · exact Trans.trans hlt (hall₁ p hp)
              rw [restrictChildren_lookup ((k1, t1) :: rest1) rest2 b rest
                hpw₁ hpw₂' hcs₁ hcs₂']
              simp [hnone]
            · rw [hasValuedPrefixChild_cons_ne _ _ _ _ _ (by
                intro hEq
                exact hb hEq.symm)]
              exact restrictChildren_lookup ((k1, t1) :: rest1) rest2 b rest
                hpw₁ hpw₂' hcs₁ hcs₂'
          · rename_i hnlt₁ hnlt₂
            have heq : k1 = k2 := uint8_eq_of_not_lt_not_lt _ _ hnlt₁ hnlt₂
            subst heq
            by_cases hb : b = k1
            · subst hb
              cases hr : t1.restrict t2 with
              | empty =>
                  have htailFalse :
                      hasValuedPrefixChild b rest rest2 = false := by
                    apply hasValuedPrefixChild_false_of_forall_lt
                    intro p hp
                    exact hall₂ p hp
                  have hTail :
                      lookupChild b rest (restrictChildren rest1 rest2) = none := by
                    rw [restrictChildren_lookup rest1 rest2 b rest
                      hpw₁' hpw₂' hcs₁' hcs₂', htailFalse]
                    simp
                  have hRec := restrict_lookup t1 t2 rest hs₁ hs₂
                  rw [hr, lookup_empty] at hRec
                  rw [hTail]
                  simpa [hasValuedPrefixChild_cons_eq, lookupChild_cons_eq]
                    using hRec
              | node v cs =>
                  rw [lookupChild_cons_eq _ (.node v cs) _ _ _ rfl]
                  have hRec := restrict_lookup t1 t2 rest hs₁ hs₂
                  rw [hr] at hRec
                  simpa [hasValuedPrefixChild_cons_eq, lookupChild_cons_eq] using hRec
            · rw [lookupChild_cons_ne _ _ _ _ _ (Ne.symm hb)]
              rw [hasValuedPrefixChild_cons_ne _ _ _ _ _ (by
                intro hEq
                exact hb hEq.symm)]
              cases hr : t1.restrict t2 with
              | empty =>
                  exact restrictChildren_lookup rest1 rest2 b rest
                    hpw₁' hpw₂' hcs₁' hcs₂'
              | node v cs =>
                  rw [lookupChild_cons_ne _ (.node v cs) _ _ _ (Ne.symm hb)]
                  exact restrictChildren_lookup rest1 rest2 b rest
                    hpw₁' hpw₂' hcs₁' hcs₂'
end

/-- The finite-trie prefix test refines the coinductive one exactly. -/
theorem toCTrie_hasPrefix (t : FTrie V) (p : List UInt8) :
    t.toCTrie.hasPrefix p = t.hasValuedPrefix p := by
  symm
  exact hasValuedPrefix_eq_toCTrie_hasPrefix t p

/-- The finite-trie `restrict` implementation refines the coinductive prefix
semantics. -/
theorem toCTrie_restrict (t₁ t₂ : FTrie V) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    CTrie.Bisim (t₁.restrict t₂).toCTrie (CTrie.restrict t₁.toCTrie t₂.toCTrie) := by
  intro p
  simpa [CTrie.restrict, toCTrie_apply, hasValuedPrefix_eq_toCTrie_hasPrefix] using
    (restrict_lookup t₁ t₂ p h₁ h₂)

end FTrie

end Mettapedia.OSLF.PathMap.Trie
