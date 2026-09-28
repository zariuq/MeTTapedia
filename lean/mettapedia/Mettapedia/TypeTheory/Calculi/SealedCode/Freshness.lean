import Mettapedia.TypeTheory.Calculi.SealedCode.Confluence

/-!
# No program contains its own name

A sealed name codes a term strictly smaller than any term it occurs in, so no
term contains its own name, and quoting a term at least as large as `M` gives
a name that does not occur in `M`.

Reduction keeps this. A name that appears during reduction either occurred in
the program already or was sealed from normal code. A program that is not
normal is therefore never sealed during its own reduction, and a normal
program does not reduce. So no reduct of a program contains the program's
name. This relies on sealing waiting for normal code.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SealedCode

open Term

/-- Size of a term, counting the code of its sealed names. -/
def size : {n : Nat} → Term n → Nat
  | _, .var _ => 1
  | _, .sym _ => 1
  | _, .lam b => size b + 1
  | _, .app f a => size f + size a + 1
  | _, .quote M => size M + 1
  | _, .lift M => size M + 1
  | _, .drop K => size K + 1

/-- `NamedIn P M`: a sealed name of code `P` occurs in `M`, possibly inside
the code of another sealed name. -/
inductive NamedIn (P : Term 0) : {n : Nat} → Term n → Prop where
  | here {n : Nat} : NamedIn P (.quote P : Term n)
  | inQuote {n : Nat} {M : Term 0} : NamedIn P M → NamedIn P (.quote M : Term n)
  | lam {n : Nat} {b : Term (n + 1)} : NamedIn P b → NamedIn P (.lam b)
  | appL {n : Nat} {f a : Term n} : NamedIn P f → NamedIn P (.app f a)
  | appR {n : Nat} {f a : Term n} : NamedIn P a → NamedIn P (.app f a)
  | lift {n : Nat} {M : Term n} : NamedIn P M → NamedIn P (.lift M)
  | drop {n : Nat} {K : Term n} : NamedIn P K → NamedIn P (.drop K)

/-- A name codes a term strictly smaller than any term it occurs in. -/
theorem NamedIn.size_lt {P : Term 0} {n : Nat} {M : Term n} (h : NamedIn P M) :
    size P < size M := by
  induction h with
  | here => simp [size]
  | inQuote _ ih => simp only [size]; omega
  | lam _ ih => simp only [size]; omega
  | appL _ ih => simp only [size]; omega
  | appR _ ih => simp only [size]; omega
  | lift _ ih => simp only [size]; omega
  | drop _ ih => simp only [size]; omega

/-- **No term contains its own name.** -/
theorem not_namedIn_self (M : Term 0) : ¬ NamedIn M M :=
  fun h => Nat.lt_irrefl _ h.size_lt

/-- **Freshness by quotation.** The name of any code at least as large as `M`
does not occur in `M`; in particular the name of any term properly containing
`M` is fresh for `M`. -/
theorem fresh_of_size_le {n : Nat} {M : Term n} {P : Term 0} (h : size M ≤ size P) :
    ¬ NamedIn P M :=
  fun named => absurd (named.size_lt) (Nat.not_lt.mpr h)

/-! ## Names under renaming and substitution -/

theorem NamedIn.rename {P : Term 0} {n : Nat} {M : Term n} (h : NamedIn P M) :
    ∀ {m : Nat} (ρ : Ren n m), NamedIn P (M.rename ρ) := by
  induction h with
  | here => intro m ρ; exact .here
  | inQuote inner => intro m ρ; exact .inQuote inner
  | lam _ ih => intro m ρ; exact .lam (ih _)
  | appL _ ih => intro m ρ; exact .appL (ih ρ)
  | appR _ ih => intro m ρ; exact .appR (ih ρ)
  | lift _ ih => intro m ρ; exact .lift (ih ρ)
  | drop _ ih => intro m ρ; exact .drop (ih ρ)

theorem NamedIn.of_rename {P : Term 0} {n : Nat} {M : Term n} :
    ∀ {m : Nat} {ρ : Ren n m}, NamedIn P (M.rename ρ) → NamedIn P M := by
  induction M with
  | var i => intro m ρ h; cases h
  | sym s => intro m ρ h; cases h
  | lam b ih =>
      intro m ρ h
      cases h with
      | lam inner => exact .lam (ih inner)
  | app f a ihf iha =>
      intro m ρ h
      cases h with
      | appL inner => exact .appL (ihf inner)
      | appR inner => exact .appR (iha inner)
  | quote M _ =>
      intro m ρ h
      cases h with
      | here => exact .here
      | inQuote inner => exact .inQuote inner
  | lift M ih =>
      intro m ρ h
      cases h with
      | lift inner => exact .lift (ih inner)
  | drop K ih =>
      intro m ρ h
      cases h with
      | drop inner => exact .drop (ih inner)

theorem NamedIn.ofClosed {P M : Term 0} {n : Nat} (h : NamedIn P (ofClosed M : Term n)) :
    NamedIn P M :=
  NamedIn.of_rename h

/-- A name in a substitution instance occurs in the term or in a substituted
term. -/
theorem NamedIn.of_subst {P : Term 0} {n : Nat} {M : Term n} :
    ∀ {m : Nat} {σ : Sub n m}, NamedIn P (M.subst σ) →
      NamedIn P M ∨ ∃ i, NamedIn P (σ i) := by
  induction M with
  | var i => intro m σ h; exact .inr ⟨i, h⟩
  | sym s => intro m σ h; cases h
  | lam b ih =>
      intro m σ h
      cases h with
      | lam inner =>
          rcases ih inner with inBody | ⟨i, inSub⟩
          · exact .inl (.lam inBody)
          · cases i using Fin.cases with
            | zero => cases inSub
            | succ i => exact .inr ⟨i, NamedIn.of_rename inSub⟩
  | app f a ihf iha =>
      intro m σ h
      cases h with
      | appL inner =>
          rcases ihf inner with inF | inSub
          · exact .inl (.appL inF)
          · exact .inr inSub
      | appR inner =>
          rcases iha inner with inA | inSub
          · exact .inl (.appR inA)
          · exact .inr inSub
  | quote M _ =>
      intro m σ h
      cases h with
      | here => exact .inl .here
      | inQuote inner => exact .inl (.inQuote inner)
  | lift M ih =>
      intro m σ h
      cases h with
      | lift inner =>
          rcases ih inner with inM | inSub
          · exact .inl (.lift inM)
          · exact .inr inSub
  | drop K ih =>
      intro m σ h
      cases h with
      | drop inner =>
          rcases ih inner with inK | inSub
          · exact .inl (.drop inK)
          · exact .inr inSub

/-! ## Names that appear during reduction -/

/-- **A name appearing in one step either was already there or was sealed from
normal code.** -/
theorem Step.namedIn {n : Nat} {M N : Term n} (h : Step M N) :
    ∀ {P : Term 0}, NamedIn P N → NamedIn P M ∨ Normal P := by
  induction h with
  | beta b a =>
      intro P named
      rcases NamedIn.of_subst named with inBody | ⟨i, inSub⟩
      · exact .inl (.appL (.lam inBody))
      · cases i using Fin.cases with
        | zero => exact .inl (.appR inSub)
        | succ i => cases inSub
  | runQuote M =>
      intro P named
      exact .inl (.drop (.inQuote named.ofClosed))
  | runLift M =>
      intro P named
      exact .inl (.drop (.lift named))
  | name M normal =>
      intro P named
      cases named with
      | here => exact .inr normal
      | inQuote inner => exact .inl (.lift (inner.rename Fin.elim0))
  | lam _ ih =>
      intro P named
      cases named with
      | lam inner =>
          rcases ih inner with h | h
          · exact .inl (.lam h)
          · exact .inr h
  | appL _ ih =>
      intro P named
      cases named with
      | appL inner =>
          rcases ih inner with h | h
          · exact .inl (.appL h)
          · exact .inr h
      | appR inner => exact .inl (.appR inner)
  | appR _ ih =>
      intro P named
      cases named with
      | appL inner => exact .inl (.appL inner)
      | appR inner =>
          rcases ih inner with h | h
          · exact .inl (.appR h)
          · exact .inr h
  | lift _ ih =>
      intro P named
      cases named with
      | lift inner =>
          rcases ih inner with h | h
          · exact .inl (.lift h)
          · exact .inr h
  | drop _ ih =>
      intro P named
      cases named with
      | drop inner =>
          rcases ih inner with h | h
          · exact .inl (.drop h)
          · exact .inr h

theorem Steps.namedIn {n : Nat} {M N : Term n} (h : Steps M N) {P : Term 0}
    (named : NamedIn P N) : NamedIn P M ∨ Normal P := by
  induction h with
  | refl => exact .inl named
  | tail _ step ih =>
      rcases step.namedIn named with h | h
      · exact ih h
      · exact .inr h

/-- **No reduct of a program contains the program's name.** -/
theorem no_self_code {M N : Term 0} (h : Steps M N) : ¬ NamedIn M N := by
  intro named
  rcases h.namedIn named with inM | normal
  · exact not_namedIn_self M inM
  · rw [steps_eq_of_irreducible normal.no_step h] at named
    exact not_namedIn_self M named

end Mettapedia.TypeTheory.Calculi.SealedCode
