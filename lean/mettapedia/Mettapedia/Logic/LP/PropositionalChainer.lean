import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Propositional Horn Chainer (Didactic PoC)

This file provides a minimal forward-chaining ATP core for propositional Horn rules:

- executable saturation algorithm (`saturate`)
- declarative proof system (`Derivable`)
- soundness + completeness (`saturate_iff_derivable`)

The setup is intentionally small and didactic:
finite proposition universe `α`, finite rule set, finite fact base.
-/

namespace Mettapedia.Logic.LP

open scoped Classical

section PropHorn

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A propositional Horn rule: finite premise set implies one head atom. -/
structure PropRule (α : Type*) where
  premises : Finset α
  head : α
deriving DecidableEq

abbrev PropProgram (α : Type*) := Finset (PropRule α)

/-- Rules whose premises are already satisfied in interpretation `I`. -/
def fired (P : PropProgram α) (I : Finset α) : Finset α :=
  (P.filter fun r => r.premises ⊆ I).image PropRule.head

/-- One forward-chaining step: keep current facts and add all fired heads. -/
def step (P : PropProgram α) (I : Finset α) : Finset α :=
  I ∪ fired P I

/-- Iterated forward chaining from initial facts. -/
def iterate (P : PropProgram α) (facts : Finset α) : Nat → Finset α
  | 0 => facts
  | n + 1 => step P (iterate P facts n)

/-- Max fuel for guaranteed stabilization over finite `α`. -/
def maxSteps : Nat := Fintype.card α + 1

/-- Executable saturated closure used by the chainer. -/
def saturate (P : PropProgram α) (facts : Finset α) : Finset α :=
  iterate P facts (maxSteps (α := α))

/-- Boolean query interface. -/
def chainerProves (P : PropProgram α) (facts : Finset α) (q : α) : Bool :=
  decide (q ∈ saturate P facts)

omit [Fintype α] in
lemma mem_fired_iff (P : PropProgram α) (I : Finset α) (a : α) :
    a ∈ fired P I ↔ ∃ r ∈ P, r.premises ⊆ I ∧ r.head = a := by
  unfold fired
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨r, hrf, rfl⟩
    rcases Finset.mem_filter.mp hrf with ⟨hrP, hsub⟩
    exact ⟨r, hrP, hsub, rfl⟩
  · rintro ⟨r, hrP, hsub, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨r, Finset.mem_filter.mpr ⟨hrP, hsub⟩, rfl⟩

omit [Fintype α] in
lemma step_inflationary (P : PropProgram α) (I : Finset α) :
    I ⊆ step P I := by
  intro a ha
  exact Finset.mem_union.mpr (Or.inl ha)

omit [Fintype α] in
lemma step_monotone (P : PropProgram α) {I J : Finset α} (hIJ : I ⊆ J) :
    step P I ⊆ step P J := by
  intro a ha
  rcases Finset.mem_union.mp ha with haI | haF
  · exact Finset.mem_union.mpr (Or.inl (hIJ haI))
  · rcases (mem_fired_iff P I a).1 haF with ⟨r, hrP, hsub, hhead⟩
    apply Finset.mem_union.mpr
    right
    exact (mem_fired_iff P J a).2 ⟨r, hrP, Set.Subset.trans hsub hIJ, hhead⟩

omit [Fintype α] in
lemma iterate_subset_succ (P : PropProgram α) (facts : Finset α) (n : Nat) :
    iterate P facts n ⊆ iterate P facts (n + 1) := by
  simpa [iterate] using step_inflationary P (iterate P facts n)

omit [Fintype α] in
lemma iterate_mono (P : PropProgram α) (facts : Finset α) {n m : Nat} (h : n ≤ m) :
    iterate P facts n ⊆ iterate P facts m := by
  induction h with
  | refl =>
      exact Set.Subset.rfl
  | @step k hk ih =>
      exact Set.Subset.trans ih (iterate_subset_succ P facts k)

omit [Fintype α] in
lemma iterate_card_lt_of_ne (P : PropProgram α) (facts : Finset α) (n : Nat)
    (hne : iterate P facts n ≠ iterate P facts (n + 1)) :
    (iterate P facts n).card < (iterate P facts (n + 1)).card := by
  refine Finset.card_lt_card ?_
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨iterate_subset_succ P facts n, hne⟩

omit [Fintype α] in
lemma index_le_card_of_strict
    (P : PropProgram α) (facts : Finset α) (n : Nat)
    (hstrict : ∀ k < n, (iterate P facts k).card < (iterate P facts (k + 1)).card) :
    n ≤ (iterate P facts n).card := by
  induction n with
  | zero =>
      exact Nat.zero_le _
  | succ n ih =>
      have hstrict' :
          ∀ k < n, (iterate P facts k).card < (iterate P facts (k + 1)).card := by
        intro k hk
        exact hstrict k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have ih' : n ≤ (iterate P facts n).card := ih hstrict'
      have hlt : (iterate P facts n).card < (iterate P facts (n + 1)).card :=
        hstrict n (Nat.lt_succ_self n)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih' hlt)

lemma exists_fixedpoint_le_card (P : PropProgram α) (facts : Finset α) :
    ∃ k ≤ Fintype.card α, iterate P facts k = iterate P facts (k + 1) := by
  by_contra hnone
  have hneq : ∀ k ≤ Fintype.card α, iterate P facts k ≠ iterate P facts (k + 1) := by
    intro k hk heq
    exact hnone ⟨k, hk, heq⟩
  have hstrict :
      ∀ k < Fintype.card α + 1,
        (iterate P facts k).card < (iterate P facts (k + 1)).card := by
    intro k hk
    have hk' : k ≤ Fintype.card α := Nat.le_of_lt_succ hk
    exact iterate_card_lt_of_ne P facts k (hneq k hk')
  have hlow :
      Fintype.card α + 1 ≤ (iterate P facts (Fintype.card α + 1)).card :=
    index_le_card_of_strict P facts (Fintype.card α + 1) hstrict
  have hup :
      (iterate P facts (Fintype.card α + 1)).card ≤ Fintype.card α :=
    Finset.card_le_univ (s := iterate P facts (Fintype.card α + 1))
  exact (Nat.not_succ_le_self (Fintype.card α)) (Nat.le_trans hlow hup)

omit [Fintype α] in
lemma fixedpoint_shift (P : PropProgram α) (facts : Finset α) {k : Nat}
    (hk : iterate P facts k = iterate P facts (k + 1)) :
    ∀ t, iterate P facts (k + t) = iterate P facts (k + t + 1)
  | 0 => by simpa using hk
  | t + 1 =>
      have ih : iterate P facts (k + t) = iterate P facts (k + t + 1) :=
        fixedpoint_shift (P := P) (facts := facts) hk t
      have hfix : step P (iterate P facts (k + t + 1)) = iterate P facts (k + t + 1) := by
        calc
          step P (iterate P facts (k + t + 1))
              = step P (iterate P facts (k + t)) := by rw [← ih]
          _ = iterate P facts (k + t + 1) := by rfl
      calc
        iterate P facts (k + (t + 1))
            = iterate P facts (k + t + 1) := by simp [Nat.add_assoc]
        _ = step P (iterate P facts (k + t + 1)) := by rw [hfix]
        _ = iterate P facts (k + t + 2) := by rfl
        _ = iterate P facts (k + (t + 1) + 1) := by simp [Nat.add_assoc]

lemma saturate_fixed (P : PropProgram α) (facts : Finset α) :
    step P (saturate P facts) = saturate P facts := by
  rcases exists_fixedpoint_le_card P facts with ⟨k, hkle, hk⟩
  let N : Nat := Fintype.card α
  have hshift :
      iterate P facts (N + 1) = iterate P facts (N + 2) := by
    have h := fixedpoint_shift P facts hk (N + 1 - k)
    have hkN1 : k ≤ N + 1 := Nat.le_trans hkle (Nat.le_succ _)
    have hk1 : k + (N + 1 - k) = N + 1 := Nat.add_sub_of_le hkN1
    have hk2 : k + (N + 1 - k) + 1 = N + 2 := by
      simp [hk1, Nat.add_assoc]
    simpa [hk1, hk2] using h
  unfold saturate maxSteps
  -- `iterate ... (N+2) = step ... (iterate ... (N+1))`
  simpa [Nat.add_assoc] using hshift.symm

lemma saturate_contains_facts (P : PropProgram α) (facts : Finset α) :
    facts ⊆ saturate P facts := by
  unfold saturate maxSteps
  exact iterate_mono P facts (Nat.zero_le _)

lemma rule_closed_saturate (P : PropProgram α) (facts : Finset α)
    {r : PropRule (α := α)} (hr : r ∈ P)
    (hsub : r.premises ⊆ saturate P facts) :
    r.head ∈ saturate P facts := by
  have hstep : r.head ∈ step P (saturate P facts) := by
    apply Finset.mem_union.mpr
    right
    exact (mem_fired_iff P (saturate P facts) r.head).2 ⟨r, hr, hsub, rfl⟩
  simpa [saturate_fixed P facts] using hstep

/-- Declarative derivability for propositional Horn programs. -/
inductive Derivable (P : PropProgram α) (facts : Finset α) : α → Prop where
  | fact {a} : a ∈ facts → Derivable P facts a
  | rule {r : PropRule (α := α)} :
      r ∈ P →
      (∀ b, b ∈ r.premises → Derivable P facts b) →
      Derivable P facts r.head

omit [Fintype α] in
lemma iterate_sound (P : PropProgram α) (facts : Finset α) :
    ∀ n a, a ∈ iterate P facts n → Derivable P facts a
  | 0, a, ha => Derivable.fact ha
  | n + 1, a, ha =>
      by
        have hstep : a ∈ step P (iterate P facts n) := by simpa [iterate] using ha
        rcases Finset.mem_union.mp hstep with hprev | hfired
        · exact iterate_sound (P := P) (facts := facts) n a hprev
        · rcases (mem_fired_iff P (iterate P facts n) a).1 hfired with ⟨r, hrP, hsub, hhead⟩
          subst hhead
          refine Derivable.rule hrP ?_
          intro b hb
          exact iterate_sound (P := P) (facts := facts) n b (hsub hb)

omit [Fintype α] in
omit [DecidableEq α] in
lemma derivable_subset_of_closed
    (P : PropProgram α) (facts S : Finset α)
    (hfacts : facts ⊆ S)
    (hclosed : ∀ r ∈ P, r.premises ⊆ S → r.head ∈ S) :
    ∀ a, Derivable P facts a → a ∈ S := by
  intro a ha
  induction ha with
  | fact h => exact hfacts h
  | rule hr hpre ih =>
      exact hclosed _ hr (by intro b hb; exact ih b hb)

theorem saturate_sound (P : PropProgram α) (facts : Finset α) (a : α) :
    a ∈ saturate P facts → Derivable P facts a := by
  intro ha
  unfold saturate maxSteps at ha
  exact iterate_sound P facts (Fintype.card α + 1) a ha

theorem saturate_complete (P : PropProgram α) (facts : Finset α) (a : α) :
    Derivable P facts a → a ∈ saturate P facts := by
  intro ha
  refine derivable_subset_of_closed P facts (saturate P facts)
      (saturate_contains_facts P facts)
      (fun r hr hsub => rule_closed_saturate P facts hr hsub) a ha

theorem saturate_iff_derivable (P : PropProgram α) (facts : Finset α) (a : α) :
    a ∈ saturate P facts ↔ Derivable P facts a := by
  constructor
  · exact saturate_sound P facts a
  · exact saturate_complete P facts a

theorem chainerProves_true_iff (P : PropProgram α) (facts : Finset α) (q : α) :
    chainerProves P facts q = true ↔ Derivable P facts q := by
  unfold chainerProves
  constructor
  · intro h
    exact (saturate_iff_derivable P facts q).1 ((decide_eq_true_iff (p := q ∈ saturate P facts)).1 h)
  · intro h
    exact (decide_eq_true_iff (p := q ∈ saturate P facts)).2 ((saturate_iff_derivable P facts q).2 h)

end PropHorn

end Mettapedia.Logic.LP
