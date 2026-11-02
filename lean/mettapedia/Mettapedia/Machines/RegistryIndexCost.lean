import Mathlib.Tactic

/-!
# Registering holders: a scanned registry against an indexed one

A term universe keeps a registry of holders (root providers, store-format
observers), each named by a key (its function and context).  The registry is an
array of slots: adding a holder appends it, removing one moves the last slot into
the freed one.  Finding a key's slot by scanning the array costs the slot's
position, and adding first scans for a duplicate, so registering `S` holders one
after another reads `S * (S + 1) / 2` slots; a program making a space per item
pays that.

An index from each key to its slot finds it in one step.  The array operations
stay the same (append; move the last slot into the freed one), so the indexed
registry holds exactly the slots the scanned one does, provided the index is kept
coherent, which includes re-pointing the key whose slot moved.

The index is modelled as an exact map whose operations cost one step; a hash
table gives that in expectation, which this file does not re-prove.

This file proves:
* `scanPos_eq_idx`: under a coherent index, the scan finds the slot the index
  names, so `indexAdd_eq_scanAdd` and `indexRemove_eq_scanRemove`: both
  registries end with the same slots;
* `valid_indexAdd` and `valid_indexRemove`: the indexed operations keep the
  index coherent;
* `scanAddAll_cost` and `indexAddAll_cost`: registering `S` fresh holders costs
  `S * (S + 1) / 2` slot reads by scanning and `S` steps by index.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RegistryIndexCost

/-- A registry: `len` slots holding keys, and an index from a key to its slot. -/
structure Reg where
  len : Nat
  slot : Nat → Nat
  idx : Nat → Option Nat

/-- The index is coherent: it names the slot of every key held, and names only
slots below `len` holding that key. -/
def Valid (r : Reg) : Prop :=
  (∀ p < r.len, r.idx (r.slot p) = some p) ∧
    ∀ k p, r.idx k = some p → p < r.len ∧ r.slot p = k

/-- The first slot below `n` holding `k`, scanning upward from slot `0`. -/
def scanPos (slot : Nat → Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, k =>
    match scanPos slot n k with
    | some p => some p
    | none => if slot n = k then some n else none

/-- Adding a key at the end. -/
def append (r : Reg) (k : Nat) : Reg :=
  ⟨r.len + 1, Function.update r.slot r.len k, Function.update r.idx k (some r.len)⟩

/-- Removing the key in slot `p`: the last slot's key moves into `p`, and the index
forgets the removed key and re-points the moved one. -/
def swapRemove (r : Reg) (p : Nat) : Reg :=
  ⟨r.len - 1, Function.update r.slot p (r.slot (r.len - 1)),
    if p = r.len - 1 then Function.update r.idx (r.slot p) none
    else Function.update (Function.update r.idx (r.slot p) none)
      (r.slot (r.len - 1)) (some p)⟩

/-- Adding by scanning: a duplicate costs the slots read up to it; a new key
costs reading every slot, then the append. -/
def scanAdd (r : Reg) (k : Nat) : Reg × Nat :=
  match scanPos r.slot r.len k with
  | some p => (r, p + 1)
  | none => (append r k, r.len + 1)

/-- Removing by scanning: the slots read up to the key, then the move. -/
def scanRemove (r : Reg) (k : Nat) : Reg × Nat :=
  match scanPos r.slot r.len k with
  | some p => (swapRemove r p, p + 1)
  | none => (r, r.len)

/-- Adding by index: one step. -/
def indexAdd (r : Reg) (k : Nat) : Reg × Nat :=
  match r.idx k with
  | some _ => (r, 1)
  | none => (append r k, 1)

/-- Removing by index: one step. -/
def indexRemove (r : Reg) (k : Nat) : Reg × Nat :=
  match r.idx k with
  | some p => (swapRemove r p, 1)
  | none => (r, 1)

/-! ## The scan finds what the index names -/

theorem scanPos_spec (slot : Nat → Nat) (k : Nat) :
    ∀ n p, scanPos slot n k = some p ↔ p < n ∧ slot p = k ∧ ∀ q < p, slot q ≠ k := by
  intro n
  induction n with
  | zero => intro p; simp [scanPos]
  | succ n ih =>
    intro p
    simp only [scanPos]
    cases h : scanPos slot n k with
    | some q =>
      rw [ih] at h
      obtain ⟨hq, hsq, hmin⟩ := h
      constructor
      · rintro ⟨⟩; exact ⟨by omega, hsq, hmin⟩
      · rintro ⟨hp, hsp, hpmin⟩
        have : q = p := by
          rcases Nat.lt_trichotomy q p with hlt | heq | hgt
          · exact absurd hsq (hpmin q hlt)
          · exact heq
          · exact absurd hsp (hmin p hgt)
        rw [this]
    | none =>
      have hnone : ∀ q < n, slot q ≠ k := by
        intro q hq hsq
        induction q using Nat.strong_induction_on with
        | _ q ihq =>
          by_cases hfirst : ∀ r < q, slot r ≠ k
          · have := (ih q).mpr ⟨hq, hsq, hfirst⟩
            rw [h] at this; cases this
          · push Not at hfirst
            obtain ⟨r, hr, hsr⟩ := hfirst
            exact ihq r hr (by omega) hsr
      by_cases hn : slot n = k
      · rw [if_pos hn]
        constructor
        · rintro ⟨⟩; exact ⟨by omega, hn, hnone⟩
        · rintro ⟨hp, hsp, hpmin⟩
          have : p = n := by
            by_contra hne
            exact hnone p (by omega) hsp
          rw [this]
      · rw [if_neg hn]
        constructor
        · intro h'; cases h'
        · rintro ⟨hp, hsp, _⟩
          rcases Nat.lt_or_ge p n with hlt | hge
          · exact absurd hsp (hnone p hlt)
          · have : p = n := by omega
            subst this; exact absurd hsp hn

theorem scanPos_eq_idx (r : Reg) (hr : Valid r) (k : Nat) :
    scanPos r.slot r.len k = r.idx k := by
  cases hk : r.idx k with
  | some p =>
    obtain ⟨hp, hsp⟩ := hr.2 k p hk
    rw [scanPos_spec]
    refine ⟨hp, hsp, ?_⟩
    intro q hq hsq
    have h1 := hr.1 q (by omega)
    rw [hsq, hk] at h1
    cases h1; omega
  | none =>
    cases hs : scanPos r.slot r.len k with
    | none => rfl
    | some p =>
      rw [scanPos_spec] at hs
      obtain ⟨hp, hsp, _⟩ := hs
      have h1 := hr.1 p hp
      rw [hsp, hk] at h1
      cases h1

theorem indexAdd_eq_scanAdd (r : Reg) (hr : Valid r) (k : Nat) :
    (indexAdd r k).1 = (scanAdd r k).1 := by
  unfold indexAdd scanAdd
  rw [scanPos_eq_idx r hr k]
  cases r.idx k <;> rfl

theorem indexRemove_eq_scanRemove (r : Reg) (hr : Valid r) (k : Nat) :
    (indexRemove r k).1 = (scanRemove r k).1 := by
  unfold indexRemove scanRemove
  rw [scanPos_eq_idx r hr k]
  cases r.idx k <;> rfl

/-! ## The indexed operations keep the index coherent -/

theorem valid_append (r : Reg) (hr : Valid r) (k : Nat) (hk : r.idx k = none) :
    Valid (append r k) := by
  constructor
  · intro p hp
    simp only [append] at hp ⊢
    by_cases hpl : p = r.len
    · subst hpl; simp
    · have hp' : p < r.len := by omega
      rw [Function.update_of_ne hpl]
      have hne : r.slot p ≠ k := by
        intro heq; have := hr.1 p hp'; rw [heq, hk] at this; cases this
      rw [Function.update_of_ne hne]
      exact hr.1 p hp'
  · intro j p hj
    simp only [append] at hj ⊢
    by_cases hjk : j = k
    · subst hjk; simp at hj; subst hj; simp
    · rw [Function.update_of_ne hjk] at hj
      obtain ⟨hp, hsp⟩ := hr.2 j p hj
      refine ⟨by omega, ?_⟩
      rw [Function.update_of_ne (by omega)]
      exact hsp

theorem valid_swapRemove (r : Reg) (hr : Valid r) (p : Nat) (hp : p < r.len) :
    Valid (swapRemove r p) := by
  have hlast : r.len - 1 < r.len := by omega
  -- Distinct slots hold distinct keys.
  have hinj : ∀ a < r.len, ∀ b < r.len, r.slot a = r.slot b → a = b := by
    intro a ha b hb hab
    have h1 := hr.1 a ha
    have h2 := hr.1 b hb
    rw [hab, h2] at h1
    cases h1; rfl
  constructor
  · intro q hq
    simp only [swapRemove] at hq ⊢
    by_cases hpl : p = r.len - 1
    · rw [if_pos hpl]
      have hqp : q ≠ p := by omega
      rw [Function.update_of_ne hqp]
      have hne : r.slot q ≠ r.slot p := fun h => hqp (hinj q (by omega) p hp h)
      rw [Function.update_of_ne hne]
      exact hr.1 q (by omega)
    · rw [if_neg hpl]
      by_cases hqp : q = p
      · subst hqp; simp
      · rw [Function.update_of_ne hqp]
        have hne1 : r.slot q ≠ r.slot (r.len - 1) :=
          fun h => by have := hinj q (by omega) (r.len - 1) hlast h; omega
        have hne2 : r.slot q ≠ r.slot p := fun h => hqp (hinj q (by omega) p hp h)
        rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact hr.1 q (by omega)
  · intro j q hj
    simp only [swapRemove] at hj ⊢
    by_cases hpl : p = r.len - 1
    · rw [if_pos hpl] at hj
      by_cases hjp : j = r.slot p
      · subst hjp; simp at hj
      · rw [Function.update_of_ne hjp] at hj
        obtain ⟨hq, hsq⟩ := hr.2 j q hj
        have hqp : q ≠ p := by
          intro h; subst h; exact hjp hsq.symm
        refine ⟨by omega, ?_⟩
        rw [Function.update_of_ne hqp]; exact hsq
    · rw [if_neg hpl] at hj
      by_cases hjm : j = r.slot (r.len - 1)
      · subst hjm; simp at hj; subst hj
        exact ⟨by omega, by simp⟩
      · rw [Function.update_of_ne hjm] at hj
        by_cases hjp : j = r.slot p
        · subst hjp; simp at hj
        · rw [Function.update_of_ne hjp] at hj
          obtain ⟨hq, hsq⟩ := hr.2 j q hj
          have hqp : q ≠ p := by
            intro h; subst h; exact hjp hsq.symm
          have hql : q ≠ r.len - 1 := by
            intro h; subst h; exact hjm hsq.symm
          refine ⟨by omega, ?_⟩
          rw [Function.update_of_ne hqp]; exact hsq

theorem valid_indexAdd (r : Reg) (hr : Valid r) (k : Nat) : Valid (indexAdd r k).1 := by
  unfold indexAdd
  cases hk : r.idx k with
  | some _ => exact hr
  | none => exact valid_append r hr k hk

theorem valid_indexRemove (r : Reg) (hr : Valid r) (k : Nat) :
    Valid (indexRemove r k).1 := by
  unfold indexRemove
  cases hk : r.idx k with
  | some p => exact valid_swapRemove r hr p (hr.2 k p hk).1
  | none => exact hr

/-! ## Registering `S` fresh holders -/

/-- The empty registry. -/
def empty : Reg := ⟨0, fun _ => 0, fun _ => none⟩

theorem valid_empty : Valid empty := ⟨by simp [empty], by simp [empty]⟩

/-- Add keys `0, 1, …, n - 1` one after another with an add operation, summing
its costs. -/
def addAll (op : Reg → Nat → Reg × Nat) : Nat → Reg × Nat
  | 0 => (empty, 0)
  | n + 1 =>
    let prev := addAll op n
    let r := op prev.1 n
    (r.1, prev.2 + r.2)

/-- After adding `0, …, n - 1` by index, the registry holds them in order. -/
theorem indexAddAll_state (n : Nat) :
    Valid (addAll indexAdd n).1 ∧ (addAll indexAdd n).1.len = n ∧
      ∀ k, n ≤ k → (addAll indexAdd n).1.idx k = none := by
  induction n with
  | zero => exact ⟨valid_empty, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨hv, hl, hfresh⟩ := ih
    have hn : (addAll indexAdd n).1.idx n = none := hfresh n (le_refl n)
    simp only [addAll, indexAdd, hn]
    refine ⟨valid_append _ hv n hn, by simp [append, hl], ?_⟩
    intro k hk
    simp only [append]
    rw [Function.update_of_ne (by omega)]
    exact hfresh k (by omega)

theorem indexAddAll_cost (n : Nat) : (addAll indexAdd n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := (indexAddAll_state n).2.2 n (le_refl n)
    simp only [addAll, indexAdd, hn, ih]

/-- Adding by scanning ends with the registry adding by index does, at a cost
of `n * (n + 1) / 2` slot reads. -/
theorem scanAddAll_cost (n : Nat) :
    (addAll scanAdd n).1 = (addAll indexAdd n).1 ∧
      2 * (addAll scanAdd n).2 = n * (n + 1) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hs, hc⟩ := ih
    obtain ⟨hv, hl, hfresh⟩ := indexAddAll_state n
    have hn : (addAll indexAdd n).1.idx n = none := hfresh n (le_refl n)
    have hscan' : scanPos (addAll indexAdd n).1.slot (addAll indexAdd n).1.len n = none := by
      rw [scanPos_eq_idx _ hv n, hn]
    have hscan : scanPos (addAll scanAdd n).1.slot (addAll scanAdd n).1.len n = none := by
      rw [hs, hscan']
    refine ⟨?_, ?_⟩
    · simp only [addAll, scanAdd, indexAdd, hn, hs, hscan']
    · simp only [addAll, scanAdd, hscan]
      rw [hs, hl]
      nlinarith [hc]

end Mettapedia.Machines.RegistryIndexCost
