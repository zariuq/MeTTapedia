import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.RigidHeads

/-!
# Neutral terms with different heads are different terms

A neutral term is stuck forever: an elimination of a variable, of a rigid constant, or of a
computing constant whose inspected argument is itself neutral. Its **head**
(`eliminationHead`) is the variable or the constant at the bottom of its elimination spine,
through applications and projections.

The algorithmic equality never relates two neutral terms with different heads
(`Algorithmic.neutralHeadsAgree`). A neutral term is a weak-head normal form, so the
typed reductions the algorithm starts from leave it as it is; η applies both sides to one
fresh variable and Σ-η projects both, and neither changes the head or neutrality; at the
remaining types two neutral terms are compared as spines, head first, and the rules for
heads require one variable or one constant. So, where the algorithm is complete, two
neutral terms with different heads are **equal at no type** (`not_equal_of_neutral_heads`).

This is how the judgment, which has η for functions and pairs, separates terms. Different
normal forms of the rewriting do not separate them: a variable `f` of a function type and
its η-expansion `λ x. f x` are different terms that take no step where no rule starts at a
variable, and they are equal. Neutral heads are η-invariant, which is why they are the
right observation. A substitution keeps the constant heading a spine (`spineConst_subst`),
so an instance of a rule's left side is headed by the rule's constant.

Positive examples: a variable and a spine stuck on it, such as `add zero n` and `n` where
`add` inspects its second argument; two spines stuck on one variable under different
constants. Spines of two different rigid constants are neutral with different heads, so
`not_equal_of_rigid_heads` is a case of this statement; that case, and a variable against a
rigid constant applied to it, are checked below.

Negative examples: a term that computes is not neutral, so nothing is said about it, and
neither is an abstraction, so `f` and `λ x. f x` are not separated (below). Neutrality
cannot be dropped: a defined constant applied to its arguments is equal to its unfolding,
whose head is another constant. Nor can heads be compared before reducing: `rev-onto acc l`
unfolds to `rev-onto~scrutinee-first l acc`, and only the second is neutral.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## The head of a spine -/

/-- **The head of an elimination spine** of applications and projections: the term at its
bottom. A term that is not an elimination is its own head. -/
def eliminationHead {n : Nat} : Tm Head n → Tm Head n
  | .app f _ => eliminationHead f
  | .fst p => eliminationHead p
  | .snd p => eliminationHead p
  | t => t

theorem eliminationHead_appSpine {n : Nat} :
    ∀ (args : List (Tm Head n)) (f : Tm Head n),
      eliminationHead (appSpine f args) = eliminationHead f
  | [], _ => rfl
  | a :: args, f => eliminationHead_appSpine args (.app f a)

/-- The head of a renamed term is the renamed head. -/
theorem eliminationHead_rename {n : Nat} (t : Tm Head n) :
    ∀ {m : Nat} (ρ : Ren n m), eliminationHead (Presentation.rename ρ t) =
      Presentation.rename ρ (eliminationHead t) := by
  induction t with
  | app f a ihf _ => intro m ρ; simpa [Presentation.rename, eliminationHead] using ihf ρ
  | fst p ih => intro m ρ; simpa [Presentation.rename, eliminationHead] using ih ρ
  | snd p ih => intro m ρ; simpa [Presentation.rename, eliminationHead] using ih ρ
  | var _ => intro m ρ; rfl
  | const _ => intro m ρ; rfl
  | head _ => intro m ρ; rfl
  | pi _ _ _ _ => intro m ρ; rfl
  | sigma _ _ _ _ => intro m ρ; rfl
  | id _ _ _ _ _ _ => intro m ρ; rfl
  | lam _ _ => intro m ρ; rfl
  | pair _ _ _ _ => intro m ρ; rfl
  | refl _ _ => intro m ρ; rfl

/-- A substitution keeps the constant heading a spine. -/
theorem spineConst_subst {n m : Nat} (σ : Sub Head n m) :
    ∀ {t : Tm Head n} {c : DeclName}, spineConst t = some c →
      spineConst (Presentation.subst σ t) = some c
  | .const _, _, h => h
  | .app f _, _, h => spineConst_subst σ (t := f) h
  | .fst p, _, h => spineConst_subst σ (t := p) h
  | .snd p, _, h => spineConst_subst σ (t := p) h
  | .var _, _, h => nomatch h
  | .head _, _, h => nomatch h
  | .pi _ _, _, h => nomatch h
  | .sigma _ _, _, h => nomatch h
  | .id _ _ _, _, h => nomatch h
  | .lam _, _, h => nomatch h
  | .pair _ _, _, h => nomatch h
  | .refl _, _, h => nomatch h

/-- The head of a neutral term is a variable or a constant. -/
theorem Neutral.eliminationHead_cases {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) :
    (∃ i, eliminationHead t = .var i) ∨ ∃ c, eliminationHead t = .const c := by
  induction neutral with
  | var i => exact .inl ⟨i, rfl⟩
  | app _ ih => exact ih
  | fst _ ih => exact ih
  | snd _ ih => exact ih
  | rigid args _ => exact .inr ⟨_, eliminationHead_appSpine args _⟩
  | stuck _ _ _ _ _ _ => exact .inr ⟨_, eliminationHead_appSpine _ _⟩

/-- Weakening does not identify the heads of two neutral terms. -/
theorem Neutral.eliminationHead_wk_inj {roles : Roles Head} {n : Nat} {t u : Tm Head n}
    (nt : Neutral roles t) (nu : Neutral roles u)
    (same : Presentation.rename wk (eliminationHead t) =
      Presentation.rename wk (eliminationHead u)) :
    eliminationHead t = eliminationHead u := by
  rcases nt.eliminationHead_cases with ⟨i, hi⟩ | ⟨c, hc⟩ <;>
    rcases nu.eliminationHead_cases with ⟨j, hj⟩ | ⟨d, hd⟩
  · rw [hi, hj] at same ⊢
    simpa [Presentation.rename, wk] using same
  · rw [hi, hd] at same
    simp [Presentation.rename] at same
  · rw [hc, hj] at same
    simp [Presentation.rename] at same
  · rw [hc, hd] at same ⊢
    simpa [Presentation.rename] using same

/-! ## The algorithm keeps neutral heads -/

/-- **The heads of the two sides agree**: for the terms and types a statement compares,
whenever both are neutral; for the spines it compares, always. -/
def AlgorithmicStatement.neutralHeadsAgree (roles : Roles Head) :
    AlgorithmicStatement Head → Prop
  | .types _ left right => Neutral roles left → Neutral roles right →
      eliminationHead left = eliminationHead right
  | .typesW _ left right => Neutral roles left → Neutral roles right →
      eliminationHead left = eliminationHead right
  | .terms _ left right _ => Neutral roles left → Neutral roles right →
      eliminationHead left = eliminationHead right
  | .termsW _ left right _ => Neutral roles left → Neutral roles right →
      eliminationHead left = eliminationHead right
  | .spines _ left right _ => eliminationHead left = eliminationHead right
  | .spinesW _ left right _ => eliminationHead left = eliminationHead right

variable {S : Setting Head L}

/-- **The algorithmic equality relates neutral terms only at one head.** -/
theorem Algorithmic.neutralHeadsAgree {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) : st.neutralHeadsAgree S.roles := by
  induction derivation with
  | types redA redB _ _ _ ih =>
      intro nA nB
      have eA := WhRed.eq_of_whnf (S := S) (nA.whnf S.shape) redA.red
      have eB := WhRed.eq_of_whnf (S := S) (nB.whnf S.shape) redB.red
      subst eA
      subst eB
      exact ih nA nB
  | heads _ _ _ _ => intro nA; exact absurd rfl (nA.not_former.1 _)
  | pi _ _ _ _ _ => intro nA; exact absurd rfl (nA.not_former.2.1 _ _)
  | sigma _ _ _ _ _ => intro nA; exact absurd rfl (nA.not_former.2.2.1 _ _)
  | id _ _ _ _ _ _ => intro nA; exact absurd rfl (nA.not_former.2.2.2 _ _ _)
  | inductiveType _ _ => intro _ _; rfl
  | neutralTypes _ _ _ _ ih => exact fun _ _ => ih
  | terms _ _ redT redU _ ih =>
      intro nT nU
      have eT := WhRed.eq_of_whnf (S := S) (nT.whnf S.shape) redT.red
      have eU := WhRed.eq_of_whnf (S := S) (nU.whnf S.shape) redU.red
      subst eT
      subst eU
      exact ih nT nU
  | univ _ _ _ _ ih => exact ih
  | eta _ _ _ _ _ _ ih =>
      intro nf ng
      have applied := ih (.app (nf.rename wk)) (.app (ng.rename wk))
      simp only [eliminationHead, eliminationHead_rename] at applied
      exact nf.eliminationHead_wk_inj ng applied
  | sigmaEta _ _ _ _ _ _ ihFst _ =>
      intro np nq
      simpa [eliminationHead] using ihFst np.fst nq.fst
  | refl _ _ _ _ => intro nA; exact absurd rfl nA.ne_refl
  | spine _ _ _ _ _ _ ih => exact fun _ _ => ih
  | var i => rfl
  | const _ _ => rfl
  | app _ _ ihf _ => simpa [AlgorithmicStatement.neutralHeadsAgree, eliminationHead] using ihf
  | fst _ ih => simpa [AlgorithmicStatement.neutralHeadsAgree, eliminationHead] using ih
  | snd _ ih => simpa [AlgorithmicStatement.neutralHeadsAgree, eliminationHead] using ih
  | spinesW _ _ _ ih => exact ih

section Discrimination

variable (complete : AlgorithmicComplete S.R S.roles)
include complete

/-- **Neutral terms with different heads are equal at no type**, where the algorithmic
equality is complete. -/
theorem not_equal_of_neutral_heads {n : Nat} {Γ : Ctx Head n} {t u C : Tm Head n}
    (formed : CtxFormed S.R Γ) (neutralT : Neutral S.roles t) (neutralU : Neutral S.roles u)
    (different : eliminationHead t ≠ eliminationHead u) : ¬ Equal S.R Γ t u C := fun equal =>
  different ((complete formed equal).neutralHeadsAgree neutralT neutralU)

/-- Positive example: two spines of different rigid constants, the case of
`not_equal_of_rigid_heads`. -/
example {n : Nat} {Γ : Ctx Head n} {C : Tm Head n} {c d : DeclName}
    (formed : CtxFormed S.R Γ) (distinct : c ≠ d) (rigidC : S.roles c = .rigid)
    (rigidD : S.roles d = .rigid) (args args' : List (Tm Head n)) :
    ¬ Equal S.R Γ (appSpine (.const c) args) (appSpine (.const d) args') C :=
  not_equal_of_neutral_heads complete formed (.rigid args rigidC) (.rigid args' rigidD)
    (by
      rw [eliminationHead_appSpine, eliminationHead_appSpine]
      exact fun h => distinct (Tm.const.inj h))

/-- Positive example: a variable and a spine of a rigid constant applied to it. -/
example {n : Nat} {Γ : Ctx Head (n + 1)} {C : Tm Head (n + 1)} {c : DeclName}
    (formed : CtxFormed S.R Γ) (rigidC : S.roles c = .rigid) :
    ¬ Equal S.R Γ (.var 0) (.app (.const c) (.var 0)) C :=
  not_equal_of_neutral_heads complete formed (.var 0) (.rigid [.var 0] rigidC) nofun

end Discrimination

/-- Negative example: an abstraction is not neutral. So the statement does not separate a
function `f` from its η-expansion `λ x. f x`, which the judgment equates. -/
example {roles : Roles Head} {n : Nat} (body : Tm Head (n + 1)) :
    ¬ Neutral roles (.lam body) := fun neutral => neutral.ne_lam rfl

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
