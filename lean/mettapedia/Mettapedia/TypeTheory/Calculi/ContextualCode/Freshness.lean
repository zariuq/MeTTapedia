import Mettapedia.TypeTheory.Calculi.ContextualCode.Confluence

/-!
# No program reaches its own name

Because code is made only by `lift`, which seals normal code, and by matching,
which names pieces of code that already exists, every template that appears
during reduction has code that is smaller than the program or normal
(`bounded_steps`). A program that steps is not normal, so no reduct of a
program contains a template whose code is the program (`no_self_code`). A
calculus that fills templates as written loses this: the sealed-code control
`fill_quine` steps to its own name.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ContextualCode

open Term

/-- Size of a term, counting the code of its templates. -/
def size : {n : Nat} → Term n → Nat
  | _, .var _ => 1
  | _, .sym _ => 1
  | _, .lam b => size b + 1
  | _, .app f a => size f + size a + 1
  | _, .cquote _ M => size M + 1
  | _, .lift M => size M + 1
  | _, .drop K => size K + 1
  | _, .cmatch _ K _ F => size K + size F + 1

theorem size_rename : ∀ {n m : Nat} (ρ : Ren n m) (M : Term n), size (M.rename ρ) = size M
  | _, _, _, .var _ => rfl
  | _, _, _, .sym _ => rfl
  | _, _, ρ, .lam b => by simp only [Term.rename, size, size_rename (liftRen ρ) b]
  | _, _, ρ, .app f a => by simp only [Term.rename, size, size_rename ρ f, size_rename ρ a]
  | _, _, _, .cquote _ _ => rfl
  | _, _, ρ, .lift M => by simp only [Term.rename, size, size_rename ρ M]
  | _, _, ρ, .drop K => by simp only [Term.rename, size, size_rename ρ K]
  | _, _, ρ, .cmatch _ K _ F => by simp only [Term.rename, size, size_rename ρ K, size_rename ρ F]

/-! ## Templates inside a term -/

/-- `TemplateIn C N`: some template in `N`, possibly inside the code of another
template, has code `C`. -/
inductive TemplateIn {j : Nat} (C : Term j) : {n : Nat} → Term n → Prop where
  | here {n : Nat} : TemplateIn C (.cquote j C : Term n)
  | inCode {n k : Nat} {M : Term k} : TemplateIn C M → TemplateIn C (.cquote k M : Term n)
  | lam {n : Nat} {b : Term (n + 1)} : TemplateIn C b → TemplateIn C (.lam b)
  | appL {n : Nat} {f a : Term n} : TemplateIn C f → TemplateIn C (.app f a)
  | appR {n : Nat} {f a : Term n} : TemplateIn C a → TemplateIn C (.app f a)
  | lift {n : Nat} {M : Term n} : TemplateIn C M → TemplateIn C (.lift M)
  | drop {n : Nat} {K : Term n} : TemplateIn C K → TemplateIn C (.drop K)
  | cmatchK {n m k : Nat} {K F : Term n} {P : Pat m k} :
      TemplateIn C K → TemplateIn C (.cmatch k K P F)
  | cmatchF {n m k : Nat} {K F : Term n} {P : Pat m k} :
      TemplateIn C F → TemplateIn C (.cmatch k K P F)

/-- The code of a template is strictly smaller than any term containing it. -/
theorem TemplateIn.size_lt {j : Nat} {C : Term j} {n : Nat} {N : Term n} (h : TemplateIn C N) :
    size C < size N := by
  induction h with
  | here => simp [size]
  | inCode _ ih => simp only [size]; omega
  | lam _ ih => simp only [size]; omega
  | appL _ ih => simp only [size]; omega
  | appR _ ih => simp only [size]; omega
  | lift _ ih => simp only [size]; omega
  | drop _ ih => simp only [size]; omega
  | cmatchK _ ih => simp only [size]; omega
  | cmatchF _ ih => simp only [size]; omega

/-- A template inside the code of a template inside `X` is inside `X`. -/
theorem TemplateIn.trans {i : Nat} {C' : Term i} {n : Nat} {X : Term n} (h : TemplateIn C' X)
    {j : Nat} {C : Term j} (hC : TemplateIn C C') : TemplateIn C X := by
  induction h with
  | here => exact .inCode hC
  | inCode _ ih => exact .inCode ih
  | lam _ ih => exact .lam ih
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih
  | lift _ ih => exact .lift ih
  | drop _ ih => exact .drop ih
  | cmatchK _ ih => exact .cmatchK ih
  | cmatchF _ ih => exact .cmatchF ih

theorem TemplateIn.of_rename {j : Nat} {C : Term j} :
    ∀ {n m : Nat} {ρ : Ren n m} (X : Term n), TemplateIn C (X.rename ρ) → TemplateIn C X
  | _, _, _, .var _, h => by cases h
  | _, _, _, .sym _, h => by cases h
  | _, _, ρ, .lam b, h => by
      cases h with
      | lam inner => exact .lam (TemplateIn.of_rename b inner)
  | _, _, ρ, .app f a, h => by
      cases h with
      | appL inner => exact .appL (TemplateIn.of_rename f inner)
      | appR inner => exact .appR (TemplateIn.of_rename a inner)
  | _, _, _, .cquote _ _, h => by
      cases h with
      | here => exact .here
      | inCode inner => exact .inCode inner
  | _, _, ρ, .lift M, h => by
      cases h with
      | lift inner => exact .lift (TemplateIn.of_rename M inner)
  | _, _, ρ, .drop K, h => by
      cases h with
      | drop inner => exact .drop (TemplateIn.of_rename K inner)
  | _, _, ρ, .cmatch _ K _ F, h => by
      cases h with
      | cmatchK inner => exact .cmatchK (TemplateIn.of_rename K inner)
      | cmatchF inner => exact .cmatchF (TemplateIn.of_rename F inner)

theorem TemplateIn.rename {j : Nat} {C : Term j} {n : Nat} {X : Term n} (h : TemplateIn C X) :
    ∀ {m : Nat} (ρ : Ren n m), TemplateIn C (X.rename ρ) := by
  induction h with
  | here => intro m ρ; exact .here
  | inCode inner _ => intro m ρ; exact .inCode inner
  | lam _ ih => intro m ρ; exact .lam (ih _)
  | appL _ ih => intro m ρ; exact .appL (ih ρ)
  | appR _ ih => intro m ρ; exact .appR (ih ρ)
  | lift _ ih => intro m ρ; exact .lift (ih ρ)
  | drop _ ih => intro m ρ; exact .drop (ih ρ)
  | cmatchK _ ih => intro m ρ; exact .cmatchK (ih ρ)
  | cmatchF _ ih => intro m ρ; exact .cmatchF (ih ρ)

/-- A template in a substitution instance is a template of the term or of a
substituted term: substitution creates no code. -/
theorem TemplateIn.of_subst {j : Nat} {C : Term j} :
    ∀ {n m : Nat} {σ : Sub n m} (X : Term n), TemplateIn C (X.subst σ) →
      TemplateIn C X ∨ ∃ i, TemplateIn C (σ i)
  | _, _, _, .var i, h => .inr ⟨i, h⟩
  | _, _, _, .sym _, h => by cases h
  | _, _, σ, .lam b, h => by
      cases h with
      | lam inner =>
          rcases TemplateIn.of_subst b inner with h | ⟨i, hi⟩
          · exact .inl (.lam h)
          · cases i using Fin.cases with
            | zero => cases hi
            | succ i => exact .inr ⟨i, TemplateIn.of_rename (σ i) hi⟩
  | _, _, σ, .app f a, h => by
      cases h with
      | appL inner =>
          rcases TemplateIn.of_subst f inner with h | h
          · exact .inl (.appL h)
          · exact .inr h
      | appR inner =>
          rcases TemplateIn.of_subst a inner with h | h
          · exact .inl (.appR h)
          · exact .inr h
  | _, _, _, .cquote _ _, h => by
      cases h with
      | here => exact .inl .here
      | inCode inner => exact .inl (.inCode inner)
  | _, _, σ, .lift M, h => by
      cases h with
      | lift inner =>
          rcases TemplateIn.of_subst M inner with h | h
          · exact .inl (.lift h)
          · exact .inr h
  | _, _, σ, .drop K, h => by
      cases h with
      | drop inner =>
          rcases TemplateIn.of_subst K inner with h | h
          · exact .inl (.drop h)
          · exact .inr h
  | _, _, σ, .cmatch _ K _ F, h => by
      cases h with
      | cmatchK inner =>
          rcases TemplateIn.of_subst K inner with h | h
          · exact .inl (.cmatchK h)
          · exact .inr h
      | cmatchF inner =>
          rcases TemplateIn.of_subst F inner with h | h
          · exact .inl (.cmatchF h)
          · exact .inr h

theorem TemplateIn.of_lamN {j : Nat} {C : Term j} :
    ∀ {k : Nat} (M : Term k), TemplateIn C (lamN k M) → TemplateIn C M
  | 0, _, h => h
  | k + 1, M, h => by
      have := TemplateIn.of_lamN (.lam M) h
      cases this with
      | lam inner => exact inner

theorem TemplateIn.of_appsN {j : Nat} {C : Term j} {n : Nat} (F : Term n) :
    ∀ {k : Nat} (a : Fin k → Term n), TemplateIn C (appsN F a) →
      TemplateIn C F ∨ ∃ i, TemplateIn C (a i)
  | 0, _, h => .inl h
  | k + 1, a, h => by
      cases h with
      | appL inner =>
          rcases TemplateIn.of_appsN F (fun i => a i.castSucc) inner with h | ⟨i, hi⟩
          · exact .inl h
          · exact .inr ⟨i.castSucc, hi⟩
      | appR inner => exact .inr ⟨Fin.last k, inner⟩

/-! ## Pieces of code -/

/-- `Frag X C`: the closed code `X` occurs in `C` outside the templates of `C`. -/
inductive Frag (X : Term 0) : {n : Nat} → Term n → Prop where
  | here {n : Nat} : Frag X (ofClosed X : Term n)
  | lam {n : Nat} {b : Term (n + 1)} : Frag X b → Frag X (.lam b)
  | appL {n : Nat} {f a : Term n} : Frag X f → Frag X (.app f a)
  | appR {n : Nat} {f a : Term n} : Frag X a → Frag X (.app f a)
  | lift {n : Nat} {M : Term n} : Frag X M → Frag X (.lift M)
  | drop {n : Nat} {K : Term n} : Frag X K → Frag X (.drop K)
  | cmatchK {n m k : Nat} {K F : Term n} {P : Pat m k} : Frag X K → Frag X (.cmatch k K P F)
  | cmatchF {n m k : Nat} {K F : Term n} {P : Pat m k} : Frag X F → Frag X (.cmatch k K P F)

theorem Frag.size_le {X : Term 0} {n : Nat} {C : Term n} (h : Frag X C) : size X ≤ size C := by
  induction h with
  | here => exact (size_rename _ X).ge
  | lam _ ih => simp only [size]; omega
  | appL _ ih => simp only [size]; omega
  | appR _ ih => simp only [size]; omega
  | lift _ ih => simp only [size]; omega
  | drop _ ih => simp only [size]; omega
  | cmatchK _ ih => simp only [size]; omega
  | cmatchF _ ih => simp only [size]; omega

theorem Frag.templateIn {X : Term 0} {n : Nat} {C : Term n} (h : Frag X C) {j : Nat}
    {T : Term j} (hT : TemplateIn T X) : TemplateIn T C := by
  induction h with
  | here => exact hT.rename _
  | lam _ ih => exact .lam ih
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih
  | lift _ ih => exact .lift ih
  | drop _ ih => exact .drop ih
  | cmatchK _ ih => exact .cmatchK ih
  | cmatchF _ ih => exact .cmatchF ih

/-- Normality is reflected by renaming. -/
theorem Normal.of_rename : ∀ {n m : Nat} {ρ : Ren n m} (M : Term n), Normal (M.rename ρ) → Normal M
  | _, _, _, .var i, _ => .var i
  | _, _, _, .sym s, _ => .sym s
  | _, _, _, .cquote k M, _ => .cquote k M
  | _, _, ρ, .lam b, h => by
      cases h with
      | lam inner => exact .lam (Normal.of_rename b inner)
  | _, _, ρ, .app f a, h => by
      cases h with
      | app hf ha notLam =>
          refine .app (Normal.of_rename f hf) (Normal.of_rename a ha) ?_
          rintro b rfl
          exact notLam _ rfl
  | _, _, ρ, .lift M, h => by
      cases h with
      | lift inner isOpen =>
          exact .lift (Normal.of_rename M inner) ((open_rename ρ M).mp isOpen)
  | _, _, ρ, .drop K, h => by
      cases h with
      | drop inner notQuote notLift =>
          refine .drop (Normal.of_rename K inner) ?_ ?_
          · rintro k M rfl
            exact notQuote k M rfl
          · rintro M rfl
            exact notLift _ rfl
  | _, _, ρ, .cmatch k K P F, h => by
      cases h with
      | cmatch hK hF noMatch =>
          refine .cmatch (Normal.of_rename K hK) (Normal.of_rename F hF) ?_
          rintro σ covers rfl
          exact noMatch σ covers rfl

/-- A piece of normal code, outside its templates, is normal. -/
theorem Frag.normal {X : Term 0} {n : Nat} {C : Term n} (h : Frag X C) (normal : Normal C) :
    Normal X := by
  induction h with
  | here => exact Normal.of_rename X normal
  | lam _ ih =>
      cases normal with
      | lam inner => exact ih inner
  | appL _ ih =>
      cases normal with
      | app hf _ _ => exact ih hf
  | appR _ ih =>
      cases normal with
      | app _ ha _ => exact ih ha
  | lift _ ih =>
      cases normal with
      | lift inner _ => exact ih inner
  | drop _ ih =>
      cases normal with
      | drop inner _ _ => exact ih inner
  | cmatchK _ ih =>
      cases normal with
      | cmatch hK _ _ => exact ih hK
  | cmatchF _ ih =>
      cases normal with
      | cmatch _ hF _ => exact ih hF

/-- The code in a hole of a filled pattern is a piece of the filled pattern, or
of the code of a template inside it. -/
theorem Pat.hole_frag {m : Nat} (σ : Fin m → Term 0) (j : Fin m) :
    ∀ {k : Nat} (P : Pat m k), P.HasHole j →
      Frag (σ j) (P.fill σ) ∨ ∃ (i : Nat) (C : Term i), TemplateIn C (P.fill σ) ∧ Frag (σ j) C
  | _, .hole i, h => by
      simp only [Pat.HasHole] at h
      subst h
      exact .inl .here
  | _, .var _, h => h.elim
  | _, .sym _, h => h.elim
  | _, .lam P, h => by
      rcases Pat.hole_frag σ j P h with hf | ⟨i, C, hC, hf⟩
      · exact .inl (.lam hf)
      · exact .inr ⟨i, C, .lam hC, hf⟩
  | _, .app P Q, h => by
      rcases h with h | h
      · rcases Pat.hole_frag σ j P h with hf | ⟨i, C, hC, hf⟩
        · exact .inl (.appL hf)
        · exact .inr ⟨i, C, .appL hC, hf⟩
      · rcases Pat.hole_frag σ j Q h with hf | ⟨i, C, hC, hf⟩
        · exact .inl (.appR hf)
        · exact .inr ⟨i, C, .appR hC, hf⟩
  | _, .cquote i P, h => by
      rcases Pat.hole_frag σ j P h with hf | ⟨i', C, hC, hf⟩
      · exact .inr ⟨i, P.fill σ, .here, hf⟩
      · exact .inr ⟨i', C, .inCode hC, hf⟩
  | _, .lift P, h => by
      rcases Pat.hole_frag σ j P h with hf | ⟨i, C, hC, hf⟩
      · exact .inl (.lift hf)
      · exact .inr ⟨i, C, .lift hC, hf⟩
  | _, .drop P, h => by
      rcases Pat.hole_frag σ j P h with hf | ⟨i, C, hC, hf⟩
      · exact .inl (.drop hf)
      · exact .inr ⟨i, C, .drop hC, hf⟩

/-! ## Code during reduction -/

/-- **Where the code of a template after a step comes from**: it was the code
of a template before, or it is normal (sealed by `lift`), or it is a piece of
the code of a template before (named by a match). -/
theorem Step.templateIn {n : Nat} {N N' : Term n} (h : Step N N') :
    ∀ {j : Nat} {C : Term j}, TemplateIn C N' →
      TemplateIn C N ∨ Normal C ∨
        ∃ (X : Term 0) (i : Nat) (C' : Term i), (⟨j, C⟩ : (l : Nat) × Term l) = ⟨0, X⟩ ∧
          TemplateIn C' N ∧ Frag X C' := by
  induction h with
  | beta b a =>
      intro j C hC
      rcases TemplateIn.of_subst b hC with h | ⟨i, hi⟩
      · exact .inl (.appL (.lam h))
      · cases i using Fin.cases with
        | zero => exact .inl (.appR hi)
        | succ i => cases hi
  | run k M =>
      intro j C hC
      exact .inl (.drop (.inCode (TemplateIn.of_lamN M (TemplateIn.of_rename _ hC))))
  | runLift M =>
      intro j C hC
      exact .inl (.drop (.lift hC))
  | name V normal =>
      intro j C hC
      cases hC with
      | here => exact .inr (.inl normal)
      | inCode inner => exact .inl (.lift (inner.rename _))
  | cmatch P σ F covers =>
      intro j C hC
      rcases TemplateIn.of_appsN F _ hC with h | ⟨i, hi⟩
      · exact .inl (.cmatchF h)
      · cases hi with
        | here =>
            refine .inr (.inr ⟨σ i, ?_⟩)
            rcases Pat.hole_frag σ i P (covers i) with hf | ⟨i', C', hC', hf⟩
            · exact ⟨_, P.fill σ, rfl, .cmatchK .here, hf⟩
            · exact ⟨i', C', rfl, .cmatchK (.inCode hC'), hf⟩
        | inCode inner =>
            rcases Pat.hole_frag σ i P (covers i) with hf | ⟨i', C', hC', hf⟩
            · exact .inl (.cmatchK (.inCode (hf.templateIn inner)))
            · exact .inl (.cmatchK (.inCode (hC'.trans (hf.templateIn inner))))
  | lam _ ih =>
      intro j C hC
      cases hC with
      | lam inner =>
          rcases ih inner with h | h | ⟨X, i, C', e, hC', hf⟩
          · exact .inl (.lam h)
          · exact .inr (.inl h)
          · exact .inr (.inr ⟨X, i, C', e, .lam hC', hf⟩)
  | appL _ ih =>
      intro j C hC
      cases hC with
      | appL inner =>
          rcases ih inner with h | h | ⟨X, i, C', e, hC', hf⟩
          · exact .inl (.appL h)
          · exact .inr (.inl h)
          · exact .inr (.inr ⟨X, i, C', e, .appL hC', hf⟩)
      | appR inner => exact .inl (.appR inner)
  | appR _ ih =>
      intro j C hC
      cases hC with
      | appL inner => exact .inl (.appL inner)
      | appR inner =>
          rcases ih inner with h | h | ⟨X, i, C', e, hC', hf⟩
          · exact .inl (.appR h)
          · exact .inr (.inl h)
          · exact .inr (.inr ⟨X, i, C', e, .appR hC', hf⟩)
  | lift _ ih =>
      intro j C hC
      cases hC with
      | lift inner =>
          rcases ih inner with h | h | ⟨X, i, C', e, hC', hf⟩
          · exact .inl (.lift h)
          · exact .inr (.inl h)
          · exact .inr (.inr ⟨X, i, C', e, .lift hC', hf⟩)
  | drop _ ih =>
      intro j C hC
      cases hC with
      | drop inner =>
          rcases ih inner with h | h | ⟨X, i, C', e, hC', hf⟩
          · exact .inl (.drop h)
          · exact .inr (.inl h)
          · exact .inr (.inr ⟨X, i, C', e, .drop hC', hf⟩)
  | cmatchL _ ih =>
      intro j C hC
      cases hC with
      | cmatchK inner =>
          rcases ih inner with h | h | ⟨X, i, C', e, hC', hf⟩
          · exact .inl (.cmatchK h)
          · exact .inr (.inl h)
          · exact .inr (.inr ⟨X, i, C', e, .cmatchK hC', hf⟩)
      | cmatchF inner => exact .inl (.cmatchF inner)
  | cmatchR _ ih =>
      intro j C hC
      cases hC with
      | cmatchK inner => exact .inl (.cmatchK inner)
      | cmatchF inner =>
          rcases ih inner with h | h | ⟨X, i, C', e, hC', hf⟩
          · exact .inl (.cmatchF h)
          · exact .inr (.inl h)
          · exact .inr (.inr ⟨X, i, C', e, .cmatchF hC', hf⟩)

/-- Every template in `N` has code smaller than `M` or normal code. -/
def Bounded (M : Term 0) {n : Nat} (N : Term n) : Prop :=
  ∀ (j : Nat) (C : Term j), TemplateIn C N → size C < size M ∨ Normal C

/-- **Every template that appears while a program runs has code smaller than
the program, or normal code.** -/
theorem bounded_steps {M : Term 0} {N : Term 0} (h : Steps M N) : Bounded M N := by
  induction h with
  | refl => exact fun _ _ hC => .inl hC.size_lt
  | tail _ step ih =>
      intro j C hC
      rcases step.templateIn hC with h | h | ⟨X, i, C', e, hC', hf⟩
      · exact ih j C h
      · exact .inr h
      · simp only [Sigma.mk.injEq] at e
        obtain ⟨rfl, e⟩ := e
        rw [eq_of_heq e]
        rcases ih i C' hC' with h | h
        · exact .inl (lt_of_le_of_lt hf.size_le h)
        · exact .inr (hf.normal h)

/-- **No reduct of a program contains a template whose code is the program.** In
particular no program reaches its own name. -/
theorem no_self_code {M N : Term 0} (h : Steps M N) : ¬ TemplateIn M N := by
  intro hM
  rcases bounded_steps h 0 M hM with lt | normal
  · exact Nat.lt_irrefl _ lt
  · rw [steps_eq_of_irreducible normal.no_step h] at hM
    exact Nat.lt_irrefl _ hM.size_lt

/-- **Freshness by quotation**: the code of any template at least as large as
`M` does not occur as a template in `M`. -/
theorem fresh_of_size_le {n j : Nat} {M : Term n} {P : Term j} (h : size M ≤ size P) :
    ¬ TemplateIn P M :=
  fun hP => absurd hP.size_lt (Nat.not_lt.mpr h)

end Mettapedia.TypeTheory.Calculi.ContextualCode
