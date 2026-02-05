import Mettapedia.OSLF.PiCalculus.StructuralCongruence

/-!
# Reduction Semantics for π-Calculus

Defines the reduction relation (→) for asynchronous π-calculus.

## References
- Lybech (2022), Section 3, page 98

## LLM Formalization Tips & Status

**✅ PROVEN (5 cases):**
- `substitute_freeNames` for nil, par: straightforward
- `freeNames_eq` for nu_par, nu_swap: Use `Finset.ext`, `rcases h with p1 | p2` (not `cases`)
- Simple structural laws: `simp` or direct reasoning

**❌ BLOCKED (7 sorries) - Finset API complexity:**
- `substitute_freeNames` for input/output/nu/replicate (4 cases):
  - Provable but automation (aesop, tauto, omega) all fail
  - Need manual `by_cases` + `intro n hn` + Finset.mem_* + IH
  - Each match case creates nested goal structure that simp destabilizes
  - After simp, `cases` fails with "not an inductive type"

- `freeNames_eq` for alpha_input/alpha_nu/alpha_replicate (3 cases):
  - All depend on substitute_freeNames being proven first
  - Once unblocked, should follow from IH

**Why automation fails:**
- `split` on match creates complex implicit equalities
- `simp` rewrites goals into non-inductive forms
- Finset operations (∈, ⊆, \, insert) don't reduce to simple constructors
- Need Finset-specific lemmas or extensive manual case analysis

**Web resources:**
- [Coates thesis](https://project-archive.inf.ed.ac.uk/ug4/20201778/ug4_proj.pdf): 5700 lines continuous π-calculus Lean 3
- [Mathlib Finset docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html): Finset API reference
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

/-- Substitution affects free names predictably -/
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
      simp only [Process.substitute, Process.freeNames]
      split_ifs with hx hw
      · -- Case: x = y
        subst hx
        intro n hn
        rw [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn
        rw [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hn with hz | ⟨hn', hnw⟩
        · left; exact hz
        · have := ih hn'
          rw [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
          rcases this with hz' | ⟨hP, hny⟩
          · left; exact hz'
          · right; exact ⟨⟨Or.inr hP, hnw⟩, hny⟩
      · -- Case: x ≠ y, w = y
        subst hw
        intro n hn
        rw [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn
        rw [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hn with hxn | ⟨hP, hnw⟩
        · right; exact ⟨⟨Or.inl hxn, hnw⟩, hx⟩
        · right; exact ⟨⟨Or.inr hP, hnw⟩, by trivial⟩
      · -- Case: x ≠ y, w ≠ y
        intro n hn
        rw [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hn
        rw [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hn with hxn | ⟨hn', hnw⟩
        · right; exact ⟨⟨Or.inl hxn, hnw⟩, hx⟩
        · have := ih hn'
          rw [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
          rcases this with hz | ⟨hP, hny⟩
          · left; exact hz
          · right; exact ⟨⟨Or.inr hP, hnw⟩, hny⟩
  | output x w =>
      -- TODO: Complex let bindings create 4 cases
      -- Each case needs to map {x', w'} into insert z ({x, w} \ {y})
      -- Provable but simp/split interaction is tricky
      sorry
  | nu x P ih =>
      -- TODO: 2 cases but finset subset reasoning is tricky
      -- Case x=y: trivial inclusion
      -- Case x≠y: uses IH but goal structure complex after split
      sorry
  | replicate x w P ih =>
      -- TODO: 3 cases from match like input
      sorry

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
      -- TODO: Requires substitute_freeNames to be proven
      sorry
  | alpha_nu x y P h_fresh =>
      -- TODO: Requires substitute_freeNames to be proven
      sorry
  | alpha_replicate x y z P h_fresh h_ne =>
      -- TODO: Requires substitute_freeNames to be proven
      sorry
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
