import Mettapedia.TypeTheory.Calculi.SealedCode.Reduction

/-!
# Confluence: names do not depend on the route

Parallel reduction contracts any set of redexes at once. Its complete
development `dev` contracts all of them, and every parallel reduct develops
further to it, so parallel reduction has the diamond property and reduction is
confluent.

Consequently a term has at most one normal form. In particular, every route by
which a program becomes a name reaches the same name: sealing waits for code
that is closed and normal, and a normal form is unique.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SealedCode

open Term

/-- Parallel reduction. -/
inductive Par : {n : Nat} → Term n → Term n → Prop where
  | var {n : Nat} (i : Fin n) : Par (.var i) (.var i)
  | sym {n : Nat} (s : String) : Par (.sym s : Term n) (.sym s)
  | quote {n : Nat} (M : Term 0) : Par (.quote M : Term n) (.quote M)
  | lam {n : Nat} {b b' : Term (n + 1)} : Par b b' → Par (.lam b) (.lam b')
  | app {n : Nat} {f f' a a' : Term n} : Par f f' → Par a a' → Par (.app f a) (.app f' a')
  | beta {n : Nat} {b b' : Term (n + 1)} {a a' : Term n} :
      Par b b' → Par a a' → Par (.app (.lam b) a) (b'.inst a')
  | lift {n : Nat} {M M' : Term n} : Par M M' → Par (.lift M) (.lift M')
  | name {n : Nat} {M : Term n} {M₀ : Term 0} :
      Par M (ofClosed M₀) → Normal M₀ → Par (.lift M) (.quote M₀)
  | drop {n : Nat} {K K' : Term n} : Par K K' → Par (.drop K) (.drop K')
  | runQuote {n : Nat} (M : Term 0) : Par (.drop (.quote M) : Term n) (ofClosed M)
  | runLift {n : Nat} {M M' : Term n} : Par M M' → Par (.drop (.lift M)) M'

theorem Par.refl : ∀ {n : Nat} (M : Term n), Par M M
  | _, .var i => .var i
  | _, .sym s => .sym s
  | _, .quote M => .quote M
  | _, .lam b => .lam (Par.refl b)
  | _, .app f a => .app (Par.refl f) (Par.refl a)
  | _, .lift M => .lift (Par.refl M)
  | _, .drop K => .drop (Par.refl K)

theorem Step.par {n : Nat} {M N : Term n} (h : Step M N) : Par M N := by
  induction h with
  | beta b a => exact .beta (Par.refl b) (Par.refl a)
  | runQuote M => exact .runQuote M
  | runLift M => exact .runLift (Par.refl M)
  | name M normal => exact .name (Par.refl _) normal
  | lam _ ih => exact .lam ih
  | appL _ ih => exact .app ih (Par.refl _)
  | appR _ ih => exact .app (Par.refl _) ih
  | lift _ ih => exact .lift ih
  | drop _ ih => exact .drop ih

theorem Par.steps {n : Nat} {M N : Term n} (h : Par M N) : Steps M N := by
  induction h with
  | var i => exact .refl
  | sym s => exact .refl
  | quote M => exact .refl
  | lam _ ih => exact ih.lam
  | app _ _ ihf iha => exact Steps.app ihf iha
  | beta _ _ ihb iha => exact (Steps.app ihb.lam iha).tail (.beta _ _)
  | lift _ ih => exact ih.lift
  | name _ normal ih => exact ih.lift.tail (.name _ normal)
  | drop _ ih => exact ih.drop
  | runQuote M => exact .single (.runQuote M)
  | runLift _ ih => exact Relation.ReflTransGen.head (.runLift _) ih

/-! ## Parallel reduction under renaming and substitution -/

theorem Par.rename {n : Nat} {M N : Term n} (h : Par M N) :
    ∀ {m : Nat} (ρ : Ren n m), Par (M.rename ρ) (N.rename ρ) := by
  induction h with
  | var i => intro m ρ; exact .var _
  | sym s => intro m ρ; exact .sym s
  | quote M => intro m ρ; exact .quote M
  | lam _ ih => intro m ρ; exact .lam (ih _)
  | app _ _ ihf iha => intro m ρ; exact .app (ihf ρ) (iha ρ)
  | beta _ _ ihb iha =>
      intro m ρ
      simp only [Term.rename]
      rw [rename_inst]
      exact .beta (ihb _) (iha ρ)
  | lift _ ih => intro m ρ; exact .lift (ih ρ)
  | name _ normal ih =>
      intro m ρ
      have inner := ih ρ
      rw [rename_ofClosed] at inner
      exact .name inner normal
  | drop _ ih => intro m ρ; exact .drop (ih ρ)
  | runQuote M =>
      intro m ρ
      simp only [Term.rename, rename_ofClosed]
      exact .runQuote M
  | runLift _ ih => intro m ρ; exact .runLift (ih ρ)

theorem Par.liftSub {n m : Nat} {σ σ' : Sub n m} (h : ∀ i, Par (σ i) (σ' i)) :
    ∀ i, Par (Term.liftSub σ i) (Term.liftSub σ' i) := by
  intro i
  cases i using Fin.cases with
  | zero => exact .var 0
  | succ i => exact (h i).rename _

theorem Par.subst {n : Nat} {M N : Term n} (h : Par M N) :
    ∀ {m : Nat} {σ σ' : Sub n m}, (∀ i, Par (σ i) (σ' i)) →
      Par (M.subst σ) (N.subst σ') := by
  induction h with
  | var i => intro m σ σ' hσ; exact hσ i
  | sym s => intro m σ σ' hσ; exact .sym s
  | quote M => intro m σ σ' hσ; exact .quote M
  | lam _ ih => intro m σ σ' hσ; exact .lam (ih (Par.liftSub hσ))
  | app _ _ ihf iha => intro m σ σ' hσ; exact .app (ihf hσ) (iha hσ)
  | beta _ _ ihb iha =>
      intro m σ σ' hσ
      simp only [Term.subst]
      rw [subst_inst]
      exact .beta (ihb (Par.liftSub hσ)) (iha hσ)
  | lift _ ih => intro m σ σ' hσ; exact .lift (ih hσ)
  | name _ normal ih =>
      intro m σ σ' hσ
      have inner := ih hσ
      rw [subst_ofClosed] at inner
      exact .name inner normal
  | drop _ ih => intro m σ σ' hσ; exact .drop (ih hσ)
  | runQuote M =>
      intro m σ σ' hσ
      simp only [Term.subst, subst_ofClosed]
      exact .runQuote M
  | runLift _ ih => intro m σ σ' hσ; exact .runLift (ih hσ)

theorem Par.inst {n : Nat} {b b' : Term (n + 1)} {a a' : Term n}
    (hb : Par b b') (ha : Par a a') : Par (b.inst a) (b'.inst a') := by
  unfold Term.inst
  apply hb.subst
  intro i
  cases i using Fin.cases with
  | zero => exact ha
  | succ i => exact .var i

/-- A normal term has no parallel reduct but itself. -/
theorem Normal.par_eq {n : Nat} {M : Term n} (h : Normal M) : ∀ {N}, Par M N → N = M := by
  induction h with
  | var i => intro N p; cases p; rfl
  | sym s => intro N p; cases p; rfl
  | quote M => intro N p; cases p; rfl
  | lam _ ih =>
      intro N p
      cases p with
      | lam inner => rw [ih inner]
  | app _ _ notLam ihf iha =>
      intro N p
      cases p with
      | app pf pa => rw [ihf pf, iha pa]
      | beta => exact (notLam _ rfl).elim
  | lift _ isOpen ih =>
      intro N p
      cases p with
      | lift inner => rw [ih inner]
      | name inner _ =>
          exact (not_open_ofClosed _ (by rw [ih inner]; exact isOpen)).elim
  | drop _ notQuote notLift ih =>
      intro N p
      cases p with
      | drop inner => rw [ih inner]
      | runQuote => exact (notQuote _ rfl).elim
      | runLift => exact (notLift _ rfl).elim

/-! ## The complete development -/

open Classical in
/-- Contract every redex of a term, and name a `lift` whose developed code is
closed and normal. -/
noncomputable def dev : {n : Nat} → Term n → Term n
  | _, .var i => .var i
  | _, .sym s => .sym s
  | _, .quote M => .quote M
  | _, .lam b => .lam (dev b)
  | _, .app (.lam b) a => (dev b).inst (dev a)
  | _, .app f a => .app (dev f) (dev a)
  | _, .lift M =>
      if h : ∃ M₀ : Term 0, dev M = ofClosed M₀ ∧ Normal M₀ then .quote h.choose
      else .lift (dev M)
  | _, .drop (.quote M) => ofClosed M
  | _, .drop (.lift M) => dev M
  | _, .drop K => .drop (dev K)

/-- **Every parallel reduct develops to the complete development.** -/
theorem Par.to_dev {n : Nat} {M N : Term n} (h : Par M N) : Par N (dev M) := by
  induction h with
  | var i => exact .var i
  | sym s => exact .sym s
  | quote M => exact .quote M
  | lam _ ih => exact .lam ih
  | @app n f f' a a' pf _ ihf iha =>
      cases f with
      | lam b =>
          cases pf with
          | @lam _ _ b'' _ =>
              have inner : Par b'' (dev b) := by
                cases ihf with
                | lam inner => exact inner
              exact .beta inner iha
      | var i => exact .app ihf iha
      | sym s => exact .app ihf iha
      | app g c => exact .app ihf iha
      | quote M => exact .app ihf iha
      | lift M => exact .app ihf iha
      | drop K => exact .app ihf iha
  | beta _ _ ihb iha => exact Par.inst ihb iha
  | @lift n M M' _ ih =>
      simp only [dev]
      split
      · next named => exact .name (named.choose_spec.1 ▸ ih) named.choose_spec.2
      · exact .lift ih
  | @name n M M₀ _ normal ih =>
      have developed : dev M = ofClosed M₀ := (normal.ofClosed.par_eq ih)
      have named : ∃ M₁ : Term 0, dev M = ofClosed M₁ ∧ Normal M₁ :=
        ⟨M₀, developed, normal⟩
      simp only [dev, dif_pos named]
      have chosen : named.choose = M₀ :=
        ofClosed_injective (named.choose_spec.1.symm.trans developed)
      rw [chosen]
      exact .quote M₀
  | @drop n K K' pK ih =>
      cases K with
      | quote M =>
          cases pK
          exact .runQuote M
      | lift P =>
          show Par _ (dev P)
          cases pK with
          | lift _ =>
              simp only [dev] at ih
              split at ih
              · next named =>
                  cases ih with
                  | name inner _ =>
                      exact .runLift (named.choose_spec.1 ▸ inner)
              · cases ih with
                | lift inner => exact .runLift inner
          | @name _ _ P₀ _ _ =>
              simp only [dev] at ih
              split at ih
              · next named =>
                  cases ih
                  obtain ⟨developed, _⟩ := named.choose_spec
                  generalize named.choose = c at developed ⊢
                  rw [developed]
                  exact .runQuote c
              · cases ih
      | var i => exact .drop ih
      | sym s => exact .drop ih
      | lam b => exact .drop ih
      | app g c => exact .drop ih
      | drop K => exact .drop ih
  | runQuote M => exact Par.refl _
  | runLift _ ih => exact ih

/-- **Parallel reduction has the diamond property.** -/
theorem Par.diamond {n : Nat} {M N₁ N₂ : Term n} (h₁ : Par M N₁) (h₂ : Par M N₂) :
    ∃ D, Par N₁ D ∧ Par N₂ D :=
  ⟨dev M, h₁.to_dev, h₂.to_dev⟩

/-! ## Confluence and unique normal forms -/

theorem steps_of_parSteps {n : Nat} {M N : Term n}
    (h : Relation.ReflTransGen (@Par n) M N) : Steps M N := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans step.steps

theorem parSteps_of_steps {n : Nat} {M N : Term n} (h : Steps M N) :
    Relation.ReflTransGen (@Par n) M N := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.par

/-- **Reduction is confluent.** -/
theorem church_rosser {n : Nat} {M N₁ N₂ : Term n} (h₁ : Steps M N₁) (h₂ : Steps M N₂) :
    Relation.Join Steps N₁ N₂ := by
  obtain ⟨D, h₁D, h₂D⟩ := Relation.church_rosser (r := @Par n)
    (fun _ _ _ hb hc =>
      let ⟨d, hbd, hcd⟩ := Par.diamond hb hc
      ⟨d, .single hbd, .single hcd⟩)
    (parSteps_of_steps h₁) (parSteps_of_steps h₂)
  exact ⟨D, steps_of_parSteps h₁D, steps_of_parSteps h₂D⟩

theorem steps_eq_of_irreducible {n : Nat} {M N : Term n} (irreducible : ∀ P, ¬ Step M P)
    (h : Steps M N) : N = M := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨P, step, _⟩
  · rfl
  · exact (irreducible P step).elim

/-- **A term has at most one normal form.** -/
theorem normal_form_unique {n : Nat} {M N₁ N₂ : Term n} (h₁ : Steps M N₁) (h₂ : Steps M N₂)
    (irreducible₁ : ∀ P, ¬ Step N₁ P) (irreducible₂ : ∀ P, ¬ Step N₂ P) : N₁ = N₂ := by
  obtain ⟨D, h₁D, h₂D⟩ := church_rosser h₁ h₂
  exact (steps_eq_of_irreducible irreducible₁ h₁D).symm.trans
    (steps_eq_of_irreducible irreducible₂ h₂D)

/-- **Names do not depend on the route.** Every evaluation of a program that
ends in a name ends in the same name. -/
theorem name_unique {n : Nat} {M : Term n} {A B : Term 0} (h₁ : Steps M (.quote A))
    (h₂ : Steps M (.quote B)) : A = B := by
  have := normal_form_unique h₁ h₂ (quote_no_step A) (quote_no_step B)
  injection this

end Mettapedia.TypeTheory.Calculi.SealedCode
