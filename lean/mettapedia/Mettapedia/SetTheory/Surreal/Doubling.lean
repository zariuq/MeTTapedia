import Mettapedia.SetTheory.Surreal.OptionBounds

/-!
# A number is the average of its bracket

```
c + c  =  a + b        a = greatest left option,  b = least right option
```

This is the theorem that makes finite-birthday surreals dyadic, and it is
purely additive — no birthday of a dyadic is computed anywhere.

## Why it is true

`c + c` is the cut of its own option families, and those are `u + c` for `u` a
left option of `c` and `v + c` for `v` a right option. Since `a` is the
greatest left option and `b` the least, that family has greatest element
`a + c` and least element `b + c`. So `c + c` is the simplest number strictly
between `a + c` and `b + c` — and `a + b` lies there too, because `a < c < b`.

The other direction compares against the cut of `a + b`, and needs its four
option shapes to miss `c + c`. Two are immediate from the bracket facts in
`OptionBounds.lean`:

```
u ∈ leftOptions b  →  u ≤ a   →  a + u ≤ a + a < c + c
v ∈ rightOptions a →  b ≤ v   →  b + b ≤ v + b,  c + c < b + b
```

The other two recurse: a left option `u` of `a` satisfies `u + b ≤ a + a`
because `u` is below `a`'s own left bound and `b` is below `a`'s own right
bound, and the theorem **at `a`** says those two sum to `a + a`. Since `a` is
younger than `c`, that is the induction hypothesis. The right option of `b` is
the mirror image.

## The integer cases

`ofNat k` has no right options at all, so `a` may have no right bound to
recurse on. There the missing bound is supplied by `ofNat_succ_le_of_lt`:
`b ≤ ofNat (k+1)`, and `ofNat (k-1) + ofNat (k+1) = ofNat k + ofNat k` by the
integer addition law. The mirror case is `-ofNat k`, which has no left
options.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

/-! ## Negating a bracket -/

/-- Negation swaps a bracket and reverses it. -/
theorem HasBracket.neg {c a b : Surreal} (h : HasBracket c a b) :
    HasBracket (-c) (-b) (-a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [leftOptions_neg]; exact ⟨b, h.memRight, rfl⟩
  · rw [rightOptions_neg]; exact ⟨a, h.memLeft, rfl⟩
  · intro u hu
    rw [leftOptions_neg] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact _root_.neg_le_neg (h.minRight v hv)
  · intro v hv
    rw [rightOptions_neg] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact _root_.neg_le_neg (h.maxLeft u hu)

/-! ## The integer bound supplied by a bracket -/

/-- **When the left bound is `ofNat k`, the right bound is at most
`ofNat (k+1)`.**  `ofNat k` has no right options, so this is what replaces the
missing one. -/
theorem le_ofNat_succ_of_bracket {c a b : Surreal} {k : ℕ}
    (h : HasBracket c a b) (ha : a = ofNat k) : b ≤ ofNat (k + 1) := by
  have hbk : birthday a = (k : Ordinal) := by rw [ha, birthday_ofNat]
  have hkc : (k : Ordinal) < birthday c := hbk ▸ h.birthday_left
  have hk1 : ((k + 1 : ℕ) : Ordinal) ≤ birthday c := by
    rw [Nat.cast_succ]; exact Order.add_one_le_of_lt hkc
  have hk1lt : ((k + 1 : ℕ) : Ordinal) < birthday c := by
    rcases lt_or_eq_of_le hk1 with hlt | heq
    · exact hlt
    · exfalso
      have hgt : ofNat k < c := ha ▸ h.lt_left
      have hle : ofNat (k + 1) ≤ c := ofNat_succ_le_of_lt hgt (le_of_eq heq.symm)
      have hle2 : c ≤ ofNat (k + 1) := le_ofNat_of_birthday_le (le_of_eq heq.symm)
      have hc : c = ofNat (k + 1) := le_antisymm hle2 hle
      have hmem := h.memRight
      rw [hc, rightOptions_ofNat_empty] at hmem
      exact hmem.elim
  have hcgt : c < ofNat (k + 1) := by
    by_contra hcon
    rcases lt_or_eq_of_le (not_lt.mp hcon) with hlt | heq
    · have hmem : ofNat (k + 1) ∈ leftOptions c :=
        ⟨hlt, by rw [birthday_ofNat]; exact hk1lt⟩
      have hle := h.maxLeft _ hmem
      rw [ha] at hle
      exact absurd hle (not_le.mpr (ofNat_lt_ofNat (Nat.lt_succ_self k)))
    · rw [← heq, birthday_ofNat] at hk1lt
      exact absurd hk1lt (lt_irrefl _)
  exact h.minRight _ ⟨hcgt, by rw [birthday_ofNat]; exact hk1lt⟩

/-! ## The theorem -/

/-- **A number is the average of its bracket.** -/
theorem double_eq_bracket_sum : ∀ (c : Surreal), birthday c < Ordinal.omega0 →
    ∀ (a b : Surreal), HasBracket c a b → add c c = add a b := by
  refine fun c => (InvImage.wf birthday wellFounded_lt).induction
    (C := fun c => birthday c < Ordinal.omega0 →
      ∀ (a b : Surreal), HasBracket c a b → add c c = add a b) c ?_
  clear c
  intro c IH hfin a b h
  have hac : a < c := h.lt_left
  have hcb : c < b := h.lt_right
  have hfa : birthday a < Ordinal.omega0 := lt_trans h.birthday_left hfin
  have hfb : birthday b < Ordinal.omega0 := lt_trans h.birthday_right hfin
  have hsmall : add a a < add c c :=
    lt_trans (add_lt_add_right hac a) (add_lt_add_left hac c)
  have hbig : add c c < add b b :=
    lt_trans (add_lt_add_right hcb c) (add_lt_add_left hcb b)
  refine (isCut_add' c c).eq_of_between (isCut_add' a b) ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · -- Left options of `c + c` are below `a + b`.
    intro p hp
    have hple : p ≤ add a c := by
      rcases mem_leftSum_cases hp with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · exact add_le_add_right (h.maxLeft u hu) c
      · rw [add_comm' c u]; exact add_le_add_right (h.maxLeft u hu) c
    exact lt_of_le_of_lt hple (add_lt_add_left hcb a)
  · -- Right options of `c + c` are above `a + b`.
    intro p hp
    have hpge : add b c ≤ p := by
      rcases mem_rightSum_cases hp with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · exact add_le_add_right (h.minRight v hv) c
      · rw [add_comm' c v]; exact add_le_add_right (h.minRight v hv) c
    refine lt_of_lt_of_le ?_ hpge
    rw [add_comm' a b]
    exact add_lt_add_left hac b
  · -- Left options of `a + b` are below `c + c`.
    intro p hp
    refine lt_of_le_of_lt ?_ hsmall
    rcases mem_leftSum_cases hp with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · -- `u` is a left option of `a`.
      by_cases hra : (rightOptions a).Nonempty
      · obtain ⟨a', b', h'⟩ := exists_hasBracket hfa ⟨u, hu⟩ hra
        rw [IH a h.birthday_left hfa a' b' h']
        exact le_trans (add_le_add_right (h'.maxLeft u hu) b)
          (add_le_add_left (le_rightBound_of_bracket h h'.memRight) a')
      · obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp hfa
        have hak : a = ofNat k :=
          eq_ofNat_of_rightOptions_empty hk (Set.not_nonempty_iff_eq_empty.mp hra)
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
          cases k with
          | zero =>
              exfalso
              rw [hak, ofNat_zero] at hu
              exact absurd hu.2 (not_lt.mpr (by exact zero_le))
          | succ j => exact ⟨j, rfl⟩
        have h1 : u ≤ ofNat j := leftOptions_ofNat_succ_le (hak ▸ hu)
        have h2 : b ≤ ofNat (j + 1 + 1) := le_ofNat_succ_of_bracket h hak
        calc add u b ≤ add (ofNat j) b := add_le_add_right h1 b
          _ ≤ add (ofNat j) (ofNat (j + 1 + 1)) := add_le_add_left h2 _
          _ = ofNat (j + (j + 1 + 1)) := ofNat_add _ _
          _ = ofNat ((j + 1) + (j + 1)) := by congr 1; omega
          _ = add (ofNat (j + 1)) (ofNat (j + 1)) := (ofNat_add _ _).symm
          _ = add a a := by rw [hak]
    · -- `u` is a left option of `b`, hence at most `a`.
      exact add_le_add_left (leftBound_le_of_bracket h hu) a
  · -- Right options of `a + b` are above `c + c`.
    intro p hp
    refine lt_of_lt_of_le hbig ?_
    rcases mem_rightSum_cases hp with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · -- `v` is a right option of `a`, hence at least `b`.
      exact add_le_add_right (le_rightBound_of_bracket h hv) b
    · -- `v` is a right option of `b`.
      by_cases hlb : (leftOptions b).Nonempty
      · obtain ⟨a', b', h'⟩ := exists_hasBracket hfb hlb ⟨v, hv⟩
        rw [IH b h.birthday_right hfb a' b' h']
        exact le_trans (add_le_add_right (leftBound_le_of_bracket h h'.memLeft) b')
          (add_le_add_left (h'.minRight v hv) a)
      · obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp hfb
        have hbk : b = -(ofNat k) :=
          eq_neg_ofNat_of_leftOptions_empty hk (Set.not_nonempty_iff_eq_empty.mp hlb)
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
          cases k with
          | zero =>
              exfalso
              rw [hbk, ofNat_zero, neg_zero'] at hv
              exact absurd hv.2 (not_lt.mpr (by exact zero_le))
          | succ j => exact ⟨j, rfl⟩
        have h1 : -(ofNat j) ≤ v := rightOptions_neg_ofNat_succ_ge (hbk ▸ hv)
        have h2 : -(ofNat (j + 1 + 1)) ≤ a := by
          have hneg : -b = ofNat (j + 1) := by rw [hbk, neg_neg']
          have hle := le_ofNat_succ_of_bracket h.neg hneg
          refine le_of_not_gt (fun hgt => ?_)
          rw [← neg_neg' a] at hgt
          exact absurd (neg_lt_neg_iff.mp hgt) (not_lt.mpr hle)
        calc add b b = add (-(ofNat (j + 1))) (-(ofNat (j + 1))) := by rw [hbk]
          _ = -(add (ofNat (j + 1)) (ofNat (j + 1))) := (neg_add' _ _).symm
          _ = -(ofNat ((j + 1) + (j + 1))) := by rw [ofNat_add]
          _ = -(ofNat ((j + 1 + 1) + j)) := by congr 2; omega
          _ = -(add (ofNat (j + 1 + 1)) (ofNat j)) := by rw [ofNat_add]
          _ = add (-(ofNat (j + 1 + 1))) (-(ofNat j)) := neg_add' _ _
          _ ≤ add a (-(ofNat j)) := add_le_add_right h2 _
          _ ≤ add a v := add_le_add_left h1 a

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.double_eq_bracket_sum
