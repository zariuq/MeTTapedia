import Mettapedia.TypeTheory.Calculi.SealedCode.Reduction
import Mettapedia.TypeTheory.Calculi.ContextualCode.Reduction

/-!
# The sealed-code calculus inside contextual code

A sealed name `quote M` of the sealed-code calculus is a template without
parameters, `cquote 0 M`. The embedding `embed` commutes with renaming and
substitution, keeps and reflects normal forms, and keeps and reflects single
steps: the sealed-code calculus is exactly the fragment of contextual code
without parameters and without matching, and that fragment is closed under
reduction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ContextualCode

open Term

/-- A sealed name is a template without parameters. -/
def embed : {n : Nat} → SealedCode.Term n → Term n
  | _, .var i => .var i
  | _, .sym s => .sym s
  | _, .lam b => .lam (embed b)
  | _, .app f a => .app (embed f) (embed a)
  | _, .quote M => .cquote 0 (embed M)
  | _, .lift M => .lift (embed M)
  | _, .drop K => .drop (embed K)

theorem embed_rename : ∀ {n m : Nat} (ρ : Ren n m) (M : SealedCode.Term n),
    embed (M.rename ρ) = (embed M).rename ρ
  | _, _, _, .var _ => rfl
  | _, _, _, .sym _ => rfl
  | _, _, ρ, .lam b => by
      simp only [SealedCode.Term.rename, embed, Term.rename]
      exact congrArg Term.lam (embed_rename (liftRen ρ) b)
  | _, _, ρ, .app f a => by
      simp only [SealedCode.Term.rename, embed, Term.rename]
      rw [embed_rename ρ f, embed_rename ρ a]
  | _, _, _, .quote _ => rfl
  | _, _, ρ, .lift M => by
      simp only [SealedCode.Term.rename, embed, Term.rename]
      rw [embed_rename ρ M]
  | _, _, ρ, .drop K => by
      simp only [SealedCode.Term.rename, embed, Term.rename]
      rw [embed_rename ρ K]

theorem embed_subst : ∀ {n m : Nat} (σ : SealedCode.Term.Sub n m) (M : SealedCode.Term n),
    embed (M.subst σ) = (embed M).subst (fun i => embed (σ i))
  | _, _, _, .var _ => rfl
  | _, _, _, .sym _ => rfl
  | _, _, σ, .lam b => by
      simp only [SealedCode.Term.subst, embed, Term.subst]
      rw [embed_subst (SealedCode.Term.liftSub σ) b]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact embed_rename Fin.succ (σ i)
  | _, _, σ, .app f a => by
      simp only [SealedCode.Term.subst, embed, Term.subst]
      rw [embed_subst σ f, embed_subst σ a]
  | _, _, _, .quote _ => rfl
  | _, _, σ, .lift M => by
      simp only [SealedCode.Term.subst, embed, Term.subst]
      rw [embed_subst σ M]
  | _, _, σ, .drop K => by
      simp only [SealedCode.Term.subst, embed, Term.subst]
      rw [embed_subst σ K]

theorem embed_inst {n : Nat} (b : SealedCode.Term (n + 1)) (a : SealedCode.Term n) :
    embed (b.inst a) = (embed b).subst1 (embed a) := by
  unfold SealedCode.Term.inst subst1
  rw [embed_subst]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

theorem embed_ofClosed {n : Nat} (M : SealedCode.Term 0) :
    embed (SealedCode.Term.ofClosed M : SealedCode.Term n) = ofClosed (embed M) :=
  embed_rename _ M

theorem mentions_embed : ∀ {n : Nat} (M : SealedCode.Term n) (i : Fin n),
    Mentions (embed M) i ↔ SealedCode.Term.Mentions M i
  | _, .var _, _ => Iff.rfl
  | _, .sym _, _ => Iff.rfl
  | _, .lam b, i => mentions_embed b i.succ
  | _, .app f a, i => or_congr (mentions_embed f i) (mentions_embed a i)
  | _, .quote _, _ => Iff.rfl
  | _, .lift M, i => mentions_embed M i
  | _, .drop K, i => mentions_embed K i

theorem open_embed {n : Nat} (M : SealedCode.Term n) :
    Open (embed M) ↔ SealedCode.Term.Open M := by
  unfold Open SealedCode.Term.Open
  simp only [mentions_embed]

/-! ## Shapes of embedded terms -/

theorem embed_eq_lam {n : Nat} {f : SealedCode.Term n} {b : Term (n + 1)}
    (h : embed f = .lam b) : ∃ b₀, f = .lam b₀ ∧ b = embed b₀ := by
  cases f with
  | lam b₀ =>
      simp only [embed, Term.lam.injEq] at h
      exact ⟨b₀, rfl, h.symm⟩
  | _ => simp [embed] at h

theorem embed_eq_cquote {n k : Nat} {K : SealedCode.Term n} {M : Term k}
    (h : embed K = .cquote k M) : ∃ M₀, K = .quote M₀ ∧ k = 0 ∧ HEq M (embed M₀) := by
  cases K with
  | quote M₀ =>
      simp only [embed, Term.cquote.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨M₀, rfl, rfl, h.symm⟩
  | _ => simp [embed] at h

theorem embed_eq_lift {n : Nat} {K : SealedCode.Term n} {M : Term n}
    (h : embed K = .lift M) : ∃ M₀, K = .lift M₀ ∧ M = embed M₀ := by
  cases K with
  | lift M₀ =>
      simp only [embed, Term.lift.injEq] at h
      exact ⟨M₀, rfl, h.symm⟩
  | _ => simp [embed] at h

/-- The embedding reflects renaming: an embedded term that is a renaming is
the embedding of a renaming. -/
theorem embed_eq_rename : ∀ {n m : Nat} (M : SealedCode.Term m) {ρ : Ren n m} {X : Term n},
    embed M = X.rename ρ → ∃ Y, M = Y.rename ρ ∧ X = embed Y
  | _, _, .var i, ρ, X, h => by
      cases X with
      | var j =>
          simp only [embed, Term.rename, Term.var.injEq] at h
          exact ⟨.var j, by rw [h]; rfl, rfl⟩
      | _ => simp [embed, Term.rename] at h
  | _, _, .sym s, ρ, X, h => by
      cases X with
      | sym t =>
          simp only [embed, Term.rename, Term.sym.injEq] at h
          exact ⟨.sym t, by rw [h]; rfl, rfl⟩
      | _ => simp [embed, Term.rename] at h
  | _, _, .lam b, ρ, X, h => by
      cases X with
      | lam X' =>
          simp only [embed, Term.rename, Term.lam.injEq] at h
          obtain ⟨Y, rfl, rfl⟩ := embed_eq_rename b h
          exact ⟨.lam Y, rfl, rfl⟩
      | _ => simp [embed, Term.rename] at h
  | _, _, .app f a, ρ, X, h => by
      cases X with
      | app X₁ X₂ =>
          simp only [embed, Term.rename, Term.app.injEq] at h
          obtain ⟨Y₁, rfl, rfl⟩ := embed_eq_rename f h.1
          obtain ⟨Y₂, rfl, rfl⟩ := embed_eq_rename a h.2
          exact ⟨.app Y₁ Y₂, rfl, rfl⟩
      | _ => simp [embed, Term.rename] at h
  | _, _, .quote M₀, ρ, X, h => by
      cases X with
      | cquote k X' =>
          simp only [embed, Term.rename, Term.cquote.injEq] at h
          obtain ⟨rfl, h⟩ := h
          rw [← eq_of_heq h]
          exact ⟨.quote M₀, rfl, rfl⟩
      | _ => simp [embed, Term.rename] at h
  | _, _, .lift M, ρ, X, h => by
      cases X with
      | lift X' =>
          simp only [embed, Term.rename, Term.lift.injEq] at h
          obtain ⟨Y, rfl, rfl⟩ := embed_eq_rename M h
          exact ⟨.lift Y, rfl, rfl⟩
      | _ => simp [embed, Term.rename] at h
  | _, _, .drop K, ρ, X, h => by
      cases X with
      | drop X' =>
          simp only [embed, Term.rename, Term.drop.injEq] at h
          obtain ⟨Y, rfl, rfl⟩ := embed_eq_rename K h
          exact ⟨.drop Y, rfl, rfl⟩
      | _ => simp [embed, Term.rename] at h

theorem embed_eq_ofClosed {n : Nat} {M : SealedCode.Term n} {V : Term 0}
    (h : embed M = ofClosed V) : ∃ M₀, M = SealedCode.Term.ofClosed M₀ ∧ V = embed M₀ :=
  embed_eq_rename M h

/-! ## Normal forms -/

theorem normal_embed {n : Nat} {M : SealedCode.Term n} (h : SealedCode.Normal M) :
    Normal (embed M) := by
  induction h with
  | var i => exact .var i
  | sym s => exact .sym s
  | quote M => exact .cquote 0 _
  | lam _ ih => exact .lam ih
  | app _ _ notLam ihf iha =>
      refine .app ihf iha ?_
      intro b hb
      obtain ⟨b₀, rfl, _⟩ := embed_eq_lam hb
      exact notLam b₀ rfl
  | lift _ isOpen ih => exact .lift ih ((open_embed _).mpr isOpen)
  | drop _ notQuote notLift ih =>
      refine .drop ih ?_ ?_
      · intro k M hM
        obtain ⟨M₀, rfl, _, _⟩ := embed_eq_cquote hM
        exact notQuote M₀ rfl
      · intro M hM
        obtain ⟨M₀, rfl, _⟩ := embed_eq_lift hM
        exact notLift M₀ rfl

theorem normal_of_embed : ∀ {n : Nat} {M : SealedCode.Term n}, Normal (embed M) →
    SealedCode.Normal M
  | _, .var i, _ => .var i
  | _, .sym s, _ => .sym s
  | _, .quote M, _ => .quote M
  | _, .lam b, h => by
      cases h with
      | lam inner => exact .lam (normal_of_embed inner)
  | _, .app f a, h => by
      cases h with
      | app hf ha notLam =>
          refine .app (normal_of_embed hf) (normal_of_embed ha) ?_
          intro b hb
          subst hb
          exact notLam _ rfl
  | _, .lift M, h => by
      cases h with
      | lift inner isOpen => exact .lift (normal_of_embed inner) ((open_embed M).mp isOpen)
  | _, .drop K, h => by
      cases h with
      | drop inner notQuote notLift =>
          refine .drop (normal_of_embed inner) ?_ ?_
          · intro M hM
            subst hM
            exact notQuote 0 _ rfl
          · intro M hM
            subst hM
            exact notLift _ rfl

/-! ## Steps -/

/-- **The embedding keeps steps.** -/
theorem step_embed {n : Nat} {M N : SealedCode.Term n} (h : SealedCode.Step M N) :
    Step (embed M) (embed N) := by
  induction h with
  | beta b a =>
      rw [embed_inst]
      exact .beta _ _
  | runQuote M =>
      rw [embed_ofClosed]
      exact .run 0 (embed M)
  | runLift M => exact .runLift _
  | name M normal =>
      show Step (.lift (embed (SealedCode.Term.ofClosed M))) _
      rw [embed_ofClosed]
      exact .name _ (normal_embed normal)
  | lam _ ih => exact .lam ih
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih
  | lift _ ih => exact .lift ih
  | drop _ ih => exact .drop ih

theorem steps_embed {n : Nat} {M N : SealedCode.Term n} (h : SealedCode.Steps M N) :
    Steps (embed M) (embed N) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step_embed step)

/-- **The embedding reflects steps**: every step of an embedded term is the
embedding of a step. -/
theorem step_of_embed : ∀ {n : Nat} {M : SealedCode.Term n} {N' : Term n},
    Step (embed M) N' → ∃ N, SealedCode.Step M N ∧ N' = embed N
  | _, .var _, _, h => by cases h
  | _, .sym _, _, h => by cases h
  | _, .quote _, _, h => by cases h
  | _, .lam b, _, h => by
      cases h with
      | lam inner =>
          obtain ⟨N, step, rfl⟩ := step_of_embed inner
          exact ⟨.lam N, .lam step, rfl⟩
  | _, .app f a, N', h => by
      have h' : Step (.app (embed f) (embed a)) N' := h
      generalize hf : embed f = F at h'
      cases h' with
      | beta b' a' =>
          obtain ⟨b₀, rfl, hb⟩ := embed_eq_lam hf
          exact ⟨b₀.inst a, .beta b₀ a, by rw [hb, embed_inst]⟩
      | appL inner =>
          subst hf
          obtain ⟨N, step, rfl⟩ := step_of_embed inner
          exact ⟨.app N a, .appL step, rfl⟩
      | appR inner =>
          subst hf
          obtain ⟨N, step, rfl⟩ := step_of_embed inner
          exact ⟨.app f N, .appR step, rfl⟩
  | _, .lift M, N', h => by
      have h' : Step (.lift (embed M)) N' := h
      generalize hM : embed M = X at h'
      cases h' with
      | name V normal =>
          obtain ⟨M₀, rfl, rfl⟩ := embed_eq_ofClosed hM
          exact ⟨.quote M₀, .name M₀ (normal_of_embed normal), rfl⟩
      | lift inner =>
          subst hM
          obtain ⟨N, step, rfl⟩ := step_of_embed inner
          exact ⟨.lift N, .lift step, rfl⟩
  | _, .drop K, N', h => by
      have h' : Step (.drop (embed K)) N' := h
      generalize hK : embed K = X at h'
      cases h' with
      | run k M' =>
          obtain ⟨M₀, rfl, rfl, hM⟩ := embed_eq_cquote hK
          refine ⟨SealedCode.Term.ofClosed M₀, .runQuote M₀, ?_⟩
          rw [eq_of_heq hM, embed_ofClosed]
          rfl
      | runLift M' =>
          obtain ⟨M₀, rfl, rfl⟩ := embed_eq_lift hK
          exact ⟨M₀, .runLift M₀, rfl⟩
      | drop inner =>
          subst hK
          obtain ⟨N, step, rfl⟩ := step_of_embed inner
          exact ⟨.drop N, .drop step, rfl⟩

end Mettapedia.TypeTheory.Calculi.ContextualCode
