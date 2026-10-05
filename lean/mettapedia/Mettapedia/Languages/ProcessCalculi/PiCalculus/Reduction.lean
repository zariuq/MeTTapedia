import Mettapedia.Languages.ProcessCalculi.PiCalculus.StructuralCongruence

/-!
# Reduction Semantics for π-Calculus

Defines the reduction relation (→) for asynchronous π-calculus.

## References
- Lybech (2022), Section 3, page 98

Substitution support is proved once in `Syntax`: its exact finite-set image
law gives the forward bound, unchanged-name inclusion, and alpha-support law.
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

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

/-- Substitution introduces only the replacement and retains other free names. -/
theorem Process.substitute_freeNames (P : Process) (y z : Name) :
    (P.substitute y z).freeNames ⊆ insert z (P.freeNames \ {y}) := by
  rw [Process.substitute_freeNames_eq]
  intro name member
  obtain ⟨origin, present, rfl⟩ := Finset.mem_image.mp member
  by_cases same : origin = y
  · simp only [Process.replaceName, if_pos same]
    exact Finset.mem_insert_self _ _
  · simp only [Process.replaceName, if_neg same]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr
      ⟨present, fun member => same (Finset.mem_singleton.mp member)⟩))

/-- Every source free name distinct from the substituted one remains free. -/
theorem Process.substitute_freeNames_reverse (P : Process) (y z : Name) (n : Name)
    (hn : n ∈ P.freeNames) (hny : n ≠ y) : n ∈ (P.substitute y z).freeNames := by
  rw [Process.substitute_freeNames_eq]
  exact Finset.mem_image.mpr ⟨n, hn, if_neg hny⟩

/-- Removing the freshly renamed binder recovers the original free support. -/
theorem Process.substitute_freeNames_fresh (P : Process) (y z : Name) (hz : z ∉ P.freeNames) :
    P.freeNames \ {y} = (P.substitute y z).freeNames \ {z} := by
  rw [Process.substitute_freeNames_eq, Process.image_replace_erase_target _ y z hz]

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

end Mettapedia.Languages.ProcessCalculi.PiCalculus
