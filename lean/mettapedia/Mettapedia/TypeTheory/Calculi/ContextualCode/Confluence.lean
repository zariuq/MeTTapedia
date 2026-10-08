import Mettapedia.TypeTheory.Calculi.ContextualCode.Reduction

/-!
# Confluence of contextual code

Parallel reduction contracts any set of redexes at once. Its complete
development `dev` contracts all of them, every parallel reduct develops
further to it, so parallel reduction has the diamond property and reduction is
confluent (`church_rosser`).

Consequently a term has at most one normal form, and every route by which a
program becomes a template reaches the same template (`template_unique`, and
`name_unique` for names). A match fires on the code of a template, which never
reduces, and a pattern that covers its holes determines how they were filled
(`Pat.fill_injective`), so matching is deterministic and fits the same proof.

`instAll_iff` characterizes the bracket exactly: it names `W` if and only if
`W` is normal and the filled code reduces to `W`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ContextualCode

open Term

/-- Parallel reduction. -/
inductive Par : {n : Nat} → Term n → Term n → Prop where
  | var {n : Nat} (i : Fin n) : Par (.var i) (.var i)
  | sym {n : Nat} (s : String) : Par (.sym s : Term n) (.sym s)
  | cquote {n : Nat} (k : Nat) (M : Term k) : Par (.cquote k M : Term n) (.cquote k M)
  | lam {n : Nat} {b b' : Term (n + 1)} : Par b b' → Par (.lam b) (.lam b')
  | app {n : Nat} {f f' a a' : Term n} : Par f f' → Par a a' → Par (.app f a) (.app f' a')
  | beta {n : Nat} {b b' : Term (n + 1)} {a a' : Term n} :
      Par b b' → Par a a' → Par (.app (.lam b) a) (b'.subst1 a')
  | lift {n : Nat} {M M' : Term n} : Par M M' → Par (.lift M) (.lift M')
  | name {n : Nat} {M : Term n} {V : Term 0} :
      Par M (ofClosed V) → Normal V → Par (.lift M) (.cquote 0 V)
  | drop {n : Nat} {K K' : Term n} : Par K K' → Par (.drop K) (.drop K')
  | run {n : Nat} (k : Nat) (M : Term k) :
      Par (.drop (.cquote k M) : Term n) (ofClosed (lamN k M))
  | runLift {n : Nat} {M M' : Term n} : Par M M' → Par (.drop (.lift M)) M'
  | cmatch {n m k : Nat} {K K' F F' : Term n} {P : Pat m k} :
      Par K K' → Par F F' → Par (.cmatch k K P F) (.cmatch k K' P F')
  | cmatchRedex {n m k : Nat} (P : Pat m k) (σ : Fin m → Term 0) {F F' : Term n} :
      P.Covers → Par F F' →
        Par (.cmatch k (.cquote k (P.fill σ)) P F) (appsN F' (fun j => .cquote 0 (σ j)))

theorem Par.refl : ∀ {n : Nat} (M : Term n), Par M M
  | _, .var i => .var i
  | _, .sym s => .sym s
  | _, .lam b => .lam (Par.refl b)
  | _, .app f a => .app (Par.refl f) (Par.refl a)
  | _, .cquote k M => .cquote k M
  | _, .lift M => .lift (Par.refl M)
  | _, .drop K => .drop (Par.refl K)
  | _, .cmatch _ K _ F => .cmatch (Par.refl K) (Par.refl F)

theorem Step.par {n : Nat} {M N : Term n} (h : Step M N) : Par M N := by
  induction h with
  | beta b a => exact .beta (Par.refl b) (Par.refl a)
  | run k M => exact .run k M
  | runLift M => exact .runLift (Par.refl M)
  | name V normal => exact .name (Par.refl _) normal
  | cmatch P σ F covers => exact .cmatchRedex P σ covers (Par.refl F)
  | lam _ ih => exact .lam ih
  | appL _ ih => exact .app ih (Par.refl _)
  | appR _ ih => exact .app (Par.refl _) ih
  | lift _ ih => exact .lift ih
  | drop _ ih => exact .drop ih
  | cmatchL _ ih => exact .cmatch ih (Par.refl _)
  | cmatchR _ ih => exact .cmatch (Par.refl _) ih

theorem Par.steps {n : Nat} {M N : Term n} (h : Par M N) : Steps M N := by
  induction h with
  | var i => exact .refl
  | sym s => exact .refl
  | cquote k M => exact .refl
  | lam _ ih => exact ih.lam
  | app _ _ ihf iha => exact Steps.app ihf iha
  | beta _ _ ihb iha => exact (Steps.app ihb.lam iha).tail (.beta _ _)
  | lift _ ih => exact ih.lift
  | name _ normal ih => exact ih.lift.tail (.name _ normal)
  | drop _ ih => exact ih.drop
  | run k M => exact .single (.run k M)
  | runLift _ ih => exact Relation.ReflTransGen.head (.runLift _) ih
  | cmatch _ _ ihK ihF => exact Steps.cmatch ihK ihF
  | cmatchRedex P σ covers _ ih =>
      exact (Steps.cmatch .refl ih).tail (.cmatch P σ _ covers)

theorem Par.appsN {n k : Nat} {F F' : Term n} (h : Par F F') (a : Fin k → Term n) :
    Par (appsN F a) (appsN F' a) := by
  induction k with
  | zero => exact h
  | succ k ih => exact .app (ih _) (Par.refl _)

/-! ## Parallel reduction under renaming and substitution -/

theorem Par.rename {n : Nat} {M N : Term n} (h : Par M N) :
    ∀ {m : Nat} (ρ : Ren n m), Par (M.rename ρ) (N.rename ρ) := by
  induction h with
  | var i => intro m ρ; exact .var _
  | sym s => intro m ρ; exact .sym s
  | cquote k M => intro m ρ; exact .cquote k M
  | lam _ ih => intro m ρ; exact .lam (ih _)
  | app _ _ ihf iha => intro m ρ; exact .app (ihf ρ) (iha ρ)
  | beta _ _ ihb iha =>
      intro m ρ
      simp only [Term.rename]
      rw [rename_subst1]
      exact .beta (ihb _) (iha ρ)
  | lift _ ih => intro m ρ; exact .lift (ih ρ)
  | name _ normal ih =>
      intro m ρ
      have inner := ih ρ
      rw [rename_ofClosed] at inner
      exact .name inner normal
  | drop _ ih => intro m ρ; exact .drop (ih ρ)
  | run k M =>
      intro m ρ
      simp only [Term.rename, rename_ofClosed]
      exact .run k M
  | runLift _ ih => intro m ρ; exact .runLift (ih ρ)
  | cmatch _ _ ihK ihF => intro m ρ; exact .cmatch (ihK ρ) (ihF ρ)
  | cmatchRedex P σ covers _ ih =>
      intro m ρ
      rw [rename_appsN]
      exact .cmatchRedex P σ covers (ih ρ)

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
  | cquote k M => intro m σ σ' hσ; exact .cquote k M
  | lam _ ih => intro m σ σ' hσ; exact .lam (ih (Par.liftSub hσ))
  | app _ _ ihf iha => intro m σ σ' hσ; exact .app (ihf hσ) (iha hσ)
  | beta _ _ ihb iha =>
      intro m σ σ' hσ
      simp only [Term.subst]
      rw [subst_subst1]
      exact .beta (ihb (Par.liftSub hσ)) (iha hσ)
  | lift _ ih => intro m σ σ' hσ; exact .lift (ih hσ)
  | name _ normal ih =>
      intro m σ σ' hσ
      have inner := ih hσ
      rw [subst_ofClosed] at inner
      exact .name inner normal
  | drop _ ih => intro m σ σ' hσ; exact .drop (ih hσ)
  | run k M =>
      intro m σ σ' hσ
      simp only [Term.subst, subst_ofClosed]
      exact .run k M
  | runLift _ ih => intro m σ σ' hσ; exact .runLift (ih hσ)
  | cmatch _ _ ihK ihF => intro m σ σ' hσ; exact .cmatch (ihK hσ) (ihF hσ)
  | cmatchRedex P τ covers _ ih =>
      intro m σ σ' hσ
      rw [subst_appsN]
      exact .cmatchRedex P τ covers (ih hσ)

theorem Par.subst1 {n : Nat} {b b' : Term (n + 1)} {a a' : Term n}
    (hb : Par b b') (ha : Par a a') : Par (b.subst1 a) (b'.subst1 a') := by
  unfold Term.subst1
  apply hb.subst
  intro i
  cases i using Fin.cases with
  | zero => exact ha
  | succ i => exact .var i

/-! ## Inversion and normal forms -/

theorem Par.cquote_inv {n k : Nat} {M : Term k} {N : Term n} (h : Par (.cquote k M) N) :
    N = .cquote k M := by
  cases h
  rfl

theorem Par.lift_inv {n : Nat} {M N : Term n} (h : Par (.lift M) N) :
    (∃ M', N = .lift M' ∧ Par M M') ∨ (∃ V, N = .cquote 0 V ∧ Par M (ofClosed V) ∧ Normal V) := by
  cases h with
  | lift inner => exact .inl ⟨_, rfl, inner⟩
  | name inner normal => exact .inr ⟨_, rfl, inner, normal⟩

/-- A normal term has no parallel reduct but itself. -/
theorem Normal.par_eq {n : Nat} {M : Term n} (h : Normal M) : ∀ {N}, Par M N → N = M := by
  induction h with
  | var i => intro N p; cases p; rfl
  | sym s => intro N p; cases p; rfl
  | cquote k M => intro N p; cases p; rfl
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
          have closed := ih inner
          rw [← closed] at isOpen
          exact (not_open_ofClosed _ isOpen).elim
  | drop _ notQuote notLift ih =>
      intro N p
      cases p with
      | drop inner => rw [ih inner]
      | run => exact (notQuote _ _ rfl).elim
      | runLift => exact (notLift _ rfl).elim
  | cmatch _ _ noMatch ihK ihF =>
      intro N p
      cases p with
      | cmatch pK pF => rw [ihK pK, ihF pF]
      | cmatchRedex P σ covers _ => exact (noMatch σ covers rfl).elim

/-! ## The complete development -/

open Classical in
/-- Contract every redex of a term, and name a `lift` whose developed code is
closed and normal. -/
noncomputable def dev : {n : Nat} → Term n → Term n
  | _, .var i => .var i
  | _, .sym s => .sym s
  | _, .cquote k M => .cquote k M
  | _, .lam b => .lam (dev b)
  | _, .app (.lam b) a => (dev b).subst1 (dev a)
  | _, .app f a => .app (dev f) (dev a)
  | _, .lift M =>
      if h : ∃ V : Term 0, dev M = ofClosed V ∧ Normal V then .cquote 0 h.choose
      else .lift (dev M)
  | _, .drop (.cquote k M) => ofClosed (lamN k M)
  | _, .drop (.lift M) => dev M
  | _, .drop K => .drop (dev K)
  | _, .cmatch k K P F =>
      if h : ∃ σ, P.Covers ∧ K = .cquote k (P.fill σ) then
        appsN (dev F) (fun j => .cquote 0 (h.choose j))
      else .cmatch k (dev K) P (dev F)

theorem dev_lift {n : Nat} (M : Term n) :
    (∃ V, dev M = ofClosed V ∧ Normal V ∧ dev (.lift M) = .cquote 0 V) ∨
      ((¬ ∃ V : Term 0, dev M = ofClosed V ∧ Normal V) ∧ dev (.lift M) = .lift (dev M)) := by
  by_cases named : ∃ V : Term 0, dev M = ofClosed V ∧ Normal V
  · refine .inl ⟨named.choose, named.choose_spec.1, named.choose_spec.2, ?_⟩
    simp only [dev, dif_pos named]
  · exact .inr ⟨named, by simp only [dev, dif_neg named]⟩

theorem dev_lift_named {n : Nat} {M : Term n} {V : Term 0} (hdev : dev M = ofClosed V)
    (normal : Normal V) : dev (.lift M) = .cquote 0 V := by
  rcases dev_lift M with ⟨W, hW, _, heq⟩ | ⟨notNamed, _⟩
  · rw [heq, ofClosed_injective (hW.symm.trans hdev)]
  · exact (notNamed ⟨V, hdev, normal⟩).elim

theorem dev_drop {n : Nat} {K : Term n} (notQuote : ∀ (k : Nat) (M : Term k), K ≠ .cquote k M)
    (notLift : ∀ M, K ≠ .lift M) : dev (.drop K) = .drop (dev K) := by
  cases K with
  | cquote k M => exact (notQuote k M rfl).elim
  | lift M => exact (notLift M rfl).elim
  | _ => rfl

theorem dev_cmatch_redex {n m k : Nat} (P : Pat m k) (σ : Fin m → Term 0) (F : Term n)
    (covers : P.Covers) :
    dev (.cmatch k (.cquote k (P.fill σ)) P F) = appsN (dev F) (fun j => .cquote 0 (σ j)) := by
  have redex : ∃ τ, P.Covers ∧ (.cquote k (P.fill σ) : Term n) = .cquote k (P.fill τ) :=
    ⟨σ, covers, rfl⟩
  simp only [dev, dif_pos redex]
  have chosen : redex.choose = σ :=
    Pat.fill_injective covers (cquote_inj redex.choose_spec.2).symm
  rw [chosen]

theorem dev_cmatch_other {n m k : Nat} {K F : Term n} {P : Pat m k}
    (h : ¬ ∃ σ, P.Covers ∧ K = .cquote k (P.fill σ)) :
    dev (.cmatch k K P F) = .cmatch k (dev K) P (dev F) := by
  simp only [dev, dif_neg h]

/-- **Every parallel reduct develops to the complete development.** -/
theorem Par.to_dev {n : Nat} {M N : Term n} (h : Par M N) : Par N (dev M) := by
  induction h with
  | var i => exact .var i
  | sym s => exact .sym s
  | cquote k M => exact .cquote k M
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
      | cquote k M => exact .app ihf iha
      | lift M => exact .app ihf iha
      | drop K => exact .app ihf iha
      | cmatch k K P F => exact .app ihf iha
  | beta _ _ ihb iha => exact Par.subst1 ihb iha
  | @lift n M M' _ ih =>
      rcases dev_lift M with ⟨V, hdev, normal, heq⟩ | ⟨_, heq⟩
      · rw [heq]
        exact .name (hdev ▸ ih) normal
      · rw [heq]
        exact .lift ih
  | @name n M V _ normal ih =>
      rw [dev_lift_named (normal.ofClosed.par_eq ih) normal]
      exact .cquote 0 V
  | @drop n K K' pK ih =>
      by_cases hq : ∃ (k : Nat) (M : Term k), K = .cquote k M
      · obtain ⟨k, M, rfl⟩ := hq
        rw [Par.cquote_inv pK]
        exact .run k M
      · by_cases hl : ∃ P, K = .lift P
        · obtain ⟨P, rfl⟩ := hl
          show Par (.drop K') (dev P)
          rcases Par.lift_inv pK with ⟨P', rfl, _⟩ | ⟨V, rfl, _, _⟩
          · rcases dev_lift P with ⟨c, hdev, _, heq⟩ | ⟨_, heq⟩
            · rw [heq] at ih
              rcases Par.lift_inv ih with ⟨_, h, _⟩ | ⟨c', h, inner, _⟩
              · cases h
              · rw [hdev, cquote_inj h]
                exact .runLift inner
            · rw [heq] at ih
              rcases Par.lift_inv ih with ⟨M'', h, inner⟩ | ⟨_, h, _, _⟩
              · cases h
                exact .runLift inner
              · cases h
          · have hdl := Par.cquote_inv ih
            rcases dev_lift P with ⟨c, hdev, _, heq⟩ | ⟨_, heq⟩
            · rw [heq] at hdl
              rw [hdev, ← cquote_inj hdl]
              exact .run 0 c
            · rw [heq] at hdl
              cases hdl
        · rw [dev_drop (fun k M h => hq ⟨k, M, h⟩) (fun P h => hl ⟨P, h⟩)]
          exact .drop ih
  | run k M => exact Par.refl _
  | runLift _ ih => exact ih
  | @cmatch n m k K K' F F' P pK _ ihK ihF =>
      by_cases redex : ∃ σ, P.Covers ∧ K = .cquote k (P.fill σ)
      · obtain ⟨σ, covers, rfl⟩ := redex
        rw [Par.cquote_inv pK, dev_cmatch_redex P σ F covers]
        exact .cmatchRedex P σ covers ihF
      · rw [dev_cmatch_other redex]
        exact .cmatch ihK ihF
  | cmatchRedex P σ covers _ ih =>
      rw [dev_cmatch_redex P σ _ covers]
      exact Par.appsN ih _

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

/-- **Templates do not depend on the route.** Every evaluation of a program
that ends in a template ends in the same template, with the same number of
parameters. -/
theorem template_unique {n k k' : Nat} {M : Term n} {A : Term k} {B : Term k'}
    (h₁ : Steps M (.cquote k A)) (h₂ : Steps M (.cquote k' B)) :
    (⟨k, A⟩ : (j : Nat) × Term j) = ⟨k', B⟩ := by
  have := normal_form_unique h₁ h₂ (cquote_no_step A) (cquote_no_step B)
  simp only [Term.cquote.injEq] at this
  obtain ⟨rfl, h⟩ := this
  rw [eq_of_heq h]

/-- **Names do not depend on the route.** -/
theorem name_unique {n : Nat} {M : Term n} {A B : Term 0} (h₁ : Steps M (.cquote 0 A))
    (h₂ : Steps M (.cquote 0 B)) : A = B :=
  cquote_inj (normal_form_unique h₁ h₂ (cquote_no_step A) (cquote_no_step B))

/-! ## The bracket, exactly -/

/-- Every reduct of `lift X`, with the reduction of its code. -/
theorem lift_reducts_steps {n : Nat} {X N : Term n} (h : Steps (.lift X) N) :
    (∃ X', N = .lift X' ∧ Steps X X') ∨
      (∃ W, N = .cquote 0 W ∧ Normal W ∧ Steps X (ofClosed W)) := by
  induction h with
  | refl => exact .inl ⟨X, rfl, .refl⟩
  | tail _ step ih =>
      rcases ih with ⟨X', rfl, hX⟩ | ⟨W, rfl, _, _⟩
      · cases step with
        | name V normal => exact .inr ⟨V, rfl, normal, hX⟩
        | lift inner => exact .inl ⟨_, rfl, hX.tail inner⟩
      · exact absurd step (cquote_no_step W _)

/-- **The bracket names `W` exactly when `W` is normal and the code filled as
written reduces to it.** -/
theorem instAll_iff {n k : Nat} (M : Term k) (V : Fin k → Term 0) (W : Term 0) :
    Steps (instAll (.cquote k M : Term n) (fun i => .cquote 0 (V i))) (.cquote 0 W) ↔
      Normal W ∧ Steps (ofClosed (M.subst (fillSub V)) : Term n) (ofClosed W) := by
  constructor
  · intro h
    obtain ⟨D, hD, hW⟩ := church_rosser (instAll_template M V) h
    rw [steps_eq_of_irreducible (cquote_no_step W) hW] at hD
    rcases lift_reducts_steps hD with ⟨_, h', _⟩ | ⟨W', h', normal, hX⟩
    · cases h'
    · rw [← cquote_inj h'] at normal hX
      exact ⟨normal, hX⟩
  · rintro ⟨normal, h⟩
    exact ((instAll_template M V).trans h.lift).tail (.name W normal)

end Mettapedia.TypeTheory.Calculi.ContextualCode
