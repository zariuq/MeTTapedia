import Mettapedia.OSLF.PiCalculus.StructuralCongruence

/-!
# Reduction Semantics for π-Calculus

Defines the reduction relation (→) for asynchronous π-calculus.

## References
- Lybech (2022), Section 3, page 98

## LLM Formalization Tips (FULLY PROVEN)

**Key pattern for Finset subset/equality proofs:**
1. Use `simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn ⊢`
2. Use `rcases hn with h1 | h2` for disjunctions (NOT `cases`)
3. For `n ≠ y` from `n = x ∧ x ≠ y`, use `rw [h]; exact hx` instead of `tauto`
4. For alpha-conversion, prove helper lemma `substitute_freeNames_fresh` first

**Proof structure for `substitute_freeNames` (by induction on Process):**
- Use `split_ifs with hx hw` after `simp only [Process.substitute]`
- Add `simp only [Process.freeNames]` AFTER split_ifs in each branch
- Use `by_cases` for output (two independent if-then-else)

**For alpha-conversion cases:**
- Prove reverse direction lemma: `substitute_freeNames_reverse`
- Combine with forward direction to get: `substitute_freeNames_fresh`
- Alpha cases then follow by `congr 1; exact substitute_freeNames_fresh ...`

**Web resources:**
- [Mathlib Finset docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html)
-/

namespace Mettapedia.OSLF.PiCalculus

/-- Reduction relation (Type-valued for extraction) -/
inductive Reduces : Process → Process → Type where
  | comm (x : Name) (y z : Name) (P : Process) :
      Reduces
        (Process.par (Process.input x y P) (Process.output x z))
        (P.substitute y z)

  | par_left (P P' Q : Process) :
      Reduces P P' →
      Reduces (P ||| Q) (P' ||| Q)

  | par_right (P Q Q' : Process) :
      Reduces Q Q' →
      Reduces (P ||| Q) (P ||| Q')

  | res (x : Name) (P P' : Process) :
      Reduces P P' →
      Reduces (Process.nu x P) (Process.nu x P')

  | struct (P P' Q Q' : Process) :
      StructuralCongruence P P' →
      Reduces P' Q' →
      StructuralCongruence Q' Q →
      Reduces P Q

notation:50 P " ⇝ " Q => Reduces P Q

/-- Substitution affects free names predictably (forward direction) -/
theorem Process.substitute_freeNames (P : Process) (y z : Name) :
    (P.substitute y z).freeNames ⊆ insert z (P.freeNames \ {y}) := by
  induction P with
  | nil =>
      simp [Process.substitute, Process.freeNames]
  | par P Q ihP ihQ =>
      simp only [Process.substitute, Process.freeNames]
      intro n hn
      simp only [Finset.mem_union] at hn
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_union]
      cases hn with
      | inl hnP =>
          have := ihP hnP
          simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
          cases this with
          | inl h => left; exact h
          | inr h => right; exact ⟨Or.inl h.1, h.2⟩
      | inr hnQ =>
          have := ihQ hnQ
          simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
          cases this with
          | inl h => left; exact h
          | inr h => right; exact ⟨Or.inr h.1, h.2⟩
  | input x w P ih =>
      simp only [Process.substitute]
      split_ifs with hx hw
      · -- Case: x = y (substitute channel name)
        subst hx
        simp only [Process.freeNames]
        intro n hn
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn ⊢
        rcases hn with hz | ⟨hn', hnw⟩
        · left; exact hz
        · have := ih hn'
          simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
          tauto
      · -- Case: x ≠ y, w = y (binding variable captures, no sub in body)
        subst hw
        simp only [Process.freeNames]
        intro n hn
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn ⊢
        rcases hn with hnx | ⟨hnP, hnw⟩
        · -- n = x, need to show n ≠ w (= y), but x ≠ y (= w) is hx
          right; constructor
          · left; exact hnx
          · rw [hnx]; exact hx
        · right; exact ⟨Or.inr ⟨hnP, hnw⟩, hnw⟩
      · -- Case: x ≠ y, w ≠ y (standard substitution)
        simp only [Process.freeNames]
        intro n hn
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn ⊢
        rcases hn with hxn | ⟨hn', hnw⟩
        · right; constructor
          · left; exact hxn
          · rw [hxn]; exact hx
        · have := ih hn'
          simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
          rcases this with hz | ⟨hP, hny⟩
          · left; exact hz
          · right; exact ⟨Or.inr ⟨hP, hnw⟩, hny⟩
  | output x w =>
      simp only [Process.substitute, Process.freeNames]
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff] at hn ⊢
      -- 4 cases from two nested if-then-else
      rcases hn with hn_fst | hn_snd
      · -- n is in first position
        by_cases hx : x = y
        · simp only [hx, ↓reduceIte] at hn_fst; left; exact hn_fst
        · simp only [hx, ↓reduceIte] at hn_fst
          right; constructor
          · left; exact hn_fst
          · rw [hn_fst]; exact hx
      · -- n is in second position
        by_cases hw : w = y
        · simp only [hw, ↓reduceIte] at hn_snd; left; exact hn_snd
        · simp only [hw, ↓reduceIte] at hn_snd
          right; constructor
          · right; exact hn_snd
          · rw [hn_snd]; exact hw
  | nu x P ih =>
      simp only [Process.substitute]
      split_ifs with hx
      · -- Case x = y: nu x P unchanged
        subst hx
        simp only [Process.freeNames]
        intro n hn
        simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert] at hn ⊢
        tauto
      · -- Case x ≠ y: uses IH
        simp only [Process.freeNames]
        intro n hn
        simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert] at hn ⊢
        have h_in_sub := ih hn.1
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at h_in_sub
        tauto
  | replicate x w P ih =>
      simp only [Process.substitute]
      split_ifs with hx hw
      · -- Case: x = y (substitute channel name)
        subst hx
        simp only [Process.freeNames]
        intro n hn
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn ⊢
        rcases hn with hz | ⟨hn', hnw⟩
        · left; exact hz
        · have := ih hn'
          simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
          tauto
      · -- Case: x ≠ y, w = y (binding var captures)
        subst hw
        simp only [Process.freeNames]
        intro n hn
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn ⊢
        rcases hn with hnx | ⟨hnP, hnw⟩
        · right; constructor
          · left; exact hnx
          · rw [hnx]; exact hx
        · right; exact ⟨Or.inr ⟨hnP, hnw⟩, hnw⟩
      · -- Case: x ≠ y, w ≠ y (standard substitution)
        simp only [Process.freeNames]
        intro n hn
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn ⊢
        rcases hn with hxn | ⟨hn', hnw⟩
        · right; constructor
          · left; exact hxn
          · rw [hxn]; exact hx
        · have := ih hn'
          simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
          rcases this with hz | ⟨hP, hny⟩
          · left; exact hz
          · right; exact ⟨Or.inr ⟨hP, hnw⟩, hny⟩

/-- Reverse direction: elements in P.freeNames \ {y} stay in (P.substitute y z).freeNames -/
theorem Process.substitute_freeNames_reverse (P : Process) (y z : Name) (n : Name)
    (hn : n ∈ P.freeNames) (hny : n ≠ y) : n ∈ (P.substitute y z).freeNames := by
  induction P generalizing n with
  | nil => simp [freeNames] at hn
  | par P Q ihP ihQ =>
      simp only [freeNames, Finset.mem_union] at hn
      simp only [substitute, freeNames, Finset.mem_union]
      rcases hn with hnP | hnQ
      · left; exact ihP n hnP hny
      · right; exact ihQ n hnQ hny
  | input x w P ih =>
      simp only [freeNames, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn
      simp only [substitute]
      split_ifs with hx hw
      · -- x = y: substitute x to z, body gets substitution
        subst hx
        simp only [freeNames, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hn with hnx | ⟨hnP, hnw⟩
        · -- n = x = y, but n ≠ y contradiction
          subst hnx; exact absurd rfl hny
        · -- n ∈ P.freeNames \ {w}
          right; exact ⟨ih n hnP hny, hnw⟩
      · -- x ≠ y, w = y: binding captures, no substitution in body
        subst hw
        simp only [freeNames, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hn with hnx | ⟨hnP, hnw⟩
        · left; exact hnx
        · right; exact ⟨hnP, hnw⟩
      · -- x ≠ y, w ≠ y: standard substitution
        simp only [freeNames, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hn with hnx | ⟨hnP, hnw⟩
        · left; exact hnx
        · right; exact ⟨ih n hnP hny, hnw⟩
  | output x w =>
      simp only [freeNames, substitute, Finset.mem_insert, Finset.mem_singleton] at hn ⊢
      rcases hn with hnx | hnw
      · -- n = x
        by_cases hx : x = y
        · subst hx hnx; exact absurd rfl hny
        · subst hnx; simp only [hx, ↓reduceIte]; left; trivial
      · -- n = w
        by_cases hw : w = y
        · subst hw hnw; exact absurd rfl hny
        · subst hnw; simp only [hw, ↓reduceIte]; right; trivial
  | nu x P ih =>
      simp only [freeNames, Finset.mem_sdiff, Finset.mem_singleton] at hn
      simp only [substitute]
      split_ifs with hx
      · -- x = y: binding captures
        simp only [freeNames, Finset.mem_sdiff, Finset.mem_singleton]
        exact hn
      · -- x ≠ y: substitute in body
        simp only [freeNames, Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨ih n hn.1 hny, hn.2⟩
  | replicate x w P ih =>
      simp only [freeNames, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn
      simp only [substitute]
      split_ifs with hx hw
      · -- x = y
        subst hx
        simp only [freeNames, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hn with hnx | ⟨hnP, hnw⟩
        · subst hnx; exact absurd rfl hny
        · right; exact ⟨ih n hnP hny, hnw⟩
      · -- x ≠ y, w = y
        subst hw
        simp only [freeNames, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hn with hnx | ⟨hnP, hnw⟩
        · left; exact hnx
        · right; exact ⟨hnP, hnw⟩
      · -- x ≠ y, w ≠ y
        simp only [freeNames, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hn with hnx | ⟨hnP, hnw⟩
        · left; exact hnx
        · right; exact ⟨ih n hnP hny, hnw⟩

/-- When z is fresh, substitution preserves free names up to the renaming y ↔ z -/
theorem Process.substitute_freeNames_fresh (P : Process) (y z : Name) (hz : z ∉ P.freeNames) :
    P.freeNames \ {y} = (P.substitute y z).freeNames \ {z} := by
  apply Finset.ext
  intro n
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · -- Forward: n ∈ P.freeNames ∧ n ≠ y → n ∈ (P.substitute y z).freeNames ∧ n ≠ z
    intro ⟨hn_free, hny⟩
    constructor
    · exact substitute_freeNames_reverse P y z n hn_free hny
    · intro hnz; subst hnz; exact hz hn_free
  · -- Backward: use substitute_freeNames
    intro ⟨hn_sub, hnz⟩
    have h := substitute_freeNames P y z hn_sub
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at h
    rcases h with rfl | ⟨hn_free, hny⟩
    · exact absurd rfl hnz
    · exact ⟨hn_free, hny⟩

/-- Structural congruence preserves free names -/
theorem StructuralCongruence.freeNames_eq {P Q : Process} (h : P ≡ Q) :
    P.freeNames = Q.freeNames := by
  induction h with
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  | par_cong _ _ _ _ _ _ ih1 ih2 =>
      simp only [Process.freeNames]
      rw [ih1, ih2]
  | input_cong x y _ _ _ ih =>
      simp only [Process.freeNames]
      rw [ih]
  | nu_cong x _ _ _ ih =>
      simp only [Process.freeNames]
      rw [ih]
  | replicate_cong x y _ _ _ ih =>
      simp only [Process.freeNames]
      rw [ih]
  | par_comm P Q =>
      simp only [Process.freeNames, Finset.union_comm]
  | par_assoc P Q R =>
      simp only [Process.freeNames, Finset.union_assoc]
  | par_nil_left P =>
      simp [Process.freeNames]
  | par_nil_right P =>
      simp [Process.freeNames]
  | nu_nil x =>
      simp [Process.freeNames]
  | nu_par x P Q h_fresh =>
      simp only [Process.freeNames]
      apply Finset.ext
      intro n
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
      constructor
      · intro ⟨h, hne⟩
        rcases h with hP | hQ
        · exact Or.inl ⟨hP, hne⟩
        · exact Or.inr hQ
      · intro h
        rcases h with ⟨hP, hne⟩ | hQ
        · exact ⟨Or.inl hP, hne⟩
        · constructor
          · exact Or.inr hQ
          · intro heq
            subst heq
            exact h_fresh hQ
  | nu_swap x y P =>
      simp only [Process.freeNames]
      apply Finset.ext
      intro n
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · intro ⟨⟨hnP, hne_y⟩, hne_x⟩
        exact ⟨⟨hnP, hne_x⟩, hne_y⟩
      · intro ⟨⟨hnP, hne_x⟩, hne_y⟩
        exact ⟨⟨hnP, hne_y⟩, hne_x⟩
  | alpha_input x y z P h_fresh h_ne =>
      -- Goal: insert x (P.freeNames \ {y}) = insert x ((P.substitute y z).freeNames \ {z})
      simp only [Process.freeNames]
      congr 1
      exact Process.substitute_freeNames_fresh P y z h_fresh
  | alpha_nu x y P h_fresh =>
      -- Goal: P.freeNames \ {x} = (P.substitute x y).freeNames \ {y}
      simp only [Process.freeNames]
      exact Process.substitute_freeNames_fresh P x y h_fresh
  | alpha_replicate x y z P h_fresh h_ne =>
      -- Goal: insert x (P.freeNames \ {y}) = insert x ((P.substitute y z).freeNames \ {z})
      simp only [Process.freeNames]
      congr 1
      exact Process.substitute_freeNames_fresh P y z h_fresh
  | replicate_unfold x y P =>
      simp only [Process.freeNames]
      ext n
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
      tauto

namespace Reduces

/-- Reduction preserves free names -/
theorem freeNames_reduces {P Q : Process} (h : P ⇝ Q) : Q.freeNames ⊆ P.freeNames := by
  induction h with
  | comm x y z P =>
      have h_sub := Process.substitute_freeNames P y z
      calc (P.substitute y z).freeNames
        _ ⊆ insert z (P.freeNames \ {y}) := h_sub
        _ ⊆ (Process.par (Process.input x y P) (Process.output x z)).freeNames := by
            simp only [Process.freeNames]; intro; simp; tauto
  | par_left P P' Q _ ih =>
      intro n hn
      simp only [Process.freeNames, Finset.mem_union] at hn ⊢
      cases hn with
      | inl hn => left; exact ih hn
      | inr hn => right; exact hn
  | par_right P Q Q' _ ih =>
      intro n hn
      simp only [Process.freeNames, Finset.mem_union] at hn ⊢
      cases hn with
      | inl hn => left; exact hn
      | inr hn => right; exact ih hn
  | res x P P' _ ih =>
      intro n hn
      simp only [Process.freeNames, Finset.mem_sdiff, Finset.mem_singleton] at hn ⊢
      exact ⟨ih hn.1, hn.2⟩
  | struct P P' Q Q' h_struct1 h_red h_struct2 a_ih =>
      calc Q.freeNames
        _ = Q'.freeNames := h_struct2.freeNames_eq.symm
        _ ⊆ P'.freeNames := a_ih
        _ = P.freeNames := h_struct1.freeNames_eq.symm

end Reduces

end Mettapedia.OSLF.PiCalculus
