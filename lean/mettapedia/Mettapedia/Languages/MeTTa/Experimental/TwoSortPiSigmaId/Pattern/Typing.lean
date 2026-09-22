import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.BinderOps
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Fragment
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# the two-sort experiment: Typing and Conversion (Locally Nameless)

Defines the **dependent typing judgment** `TwoSortHasType Γ t A` and the
**definitional equality** `TwoSortConv t₁ t₂` for the two-sort experiment.

## Design Decisions

- **Fixed heads**: ground `U0 : U1`, with untyped formation marker `U1`;
  this is not a cumulative hierarchy or quantification over types.
- **Intensional**: `TwoSortConv` is β only — no functional extensionality
- **Declarative**: this module states the Pattern judgment, not a checking algorithm.
- **Locally nameless with cofinite quantification**: binder rules open with
  fresh `fvar x` and universally quantify over all sufficiently fresh names.
  This follows Aydemir et al., "Engineering Formal Metatheory" (POPL 2008).
- **Identity formation/reflexivity only**: the calculus has no J eliminator.

## Context Convention

Contexts are association lists mapping free variable names to their types:
  `Γ = [(xₙ, Aₙ), ..., (x₁, A₁), (x₀, A₀)]`
Most recently bound variable is at the head.

## References

- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
- Martin-Löf, "Intuitionistic Type Theory" (1984)
- Adjedj et al., "Martin-Löf à la Coq" (2023, arXiv:2310.06376)
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Typing

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.BinderOps
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Fragment

/-! ## Contexts -/

/-- A the two-sort experiment context: an association list mapping free variable names
    to their types. Most recently bound at the head. -/
abbrev TwoSortCtx := List (String × Pattern)

/-- Domain of a context (the set of bound variable names). -/
def ctxDom (Γ : TwoSortCtx) : List String := Γ.map Prod.fst

/-! ## Definitional Equality (Conversion)

`TwoSortConv t₁ t₂` is the reflexive-symmetric-transitive closure of the three
β-rules, plus congruence in all type/term formers.

This is intensional: no η, no functional extensionality, no UIP. -/

/-- Definitional equality for the two-sort experiment.
    This relation is restricted to the explicit two-sort fragment, so the
    metatheory never has to invent fragment-membership witnesses later. -/
inductive TwoSortConv : Pattern → Pattern → Prop where
  -- Equivalence
  | refl (t : Pattern) (htwoSort : TwoSortTermPattern t) : TwoSortConv t t
  | symm : TwoSortConv t₁ t₂ → TwoSortConv t₂ t₁
  | trans : TwoSortConv t₁ t₂ → TwoSortConv t₂ t₃ → TwoSortConv t₁ t₃

  -- β-rules (require lc so TwoSortConv preserves local closure in both directions)
  | betaPi (body a : Pattern)
      (hbodyTwoSort : TwoSortTermPattern body) (haTwoSort : TwoSortTermPattern a)
      (hlcBody : lc_at 1 body = true) (hlcA : lc_at 0 a = true) :
      TwoSortConv (mkApp (mkLam body) a) (openBVar 0 a body)
  | betaSigmaFst (a b : Pattern)
      (haTwoSort : TwoSortTermPattern a) (hbTwoSort : TwoSortTermPattern b)
      (hlcA : lc_at 0 a = true) (hlcB : lc_at 0 b = true) :
      TwoSortConv (mkFst (mkPair a b)) a
  | betaSigmaSnd (a b : Pattern)
      (haTwoSort : TwoSortTermPattern a) (hbTwoSort : TwoSortTermPattern b)
      (hlcA : lc_at 0 a = true) (hlcB : lc_at 0 b = true) :
      TwoSortConv (mkSnd (mkPair a b)) b

  -- Congruence: Pi (cofinite for codomain — under binder)
  | congPi (L : Finset String) :
      TwoSortConv A₁ A₂ →
      (∀ x, x ∉ L → TwoSortConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) →
      TwoSortConv (mkPi A₁ B₁) (mkPi A₂ B₂)
  -- Congruence: Sigma (cofinite for codomain — under binder)
  | congSigma (L : Finset String) :
      TwoSortConv A₁ A₂ →
      (∀ x, x ∉ L → TwoSortConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) →
      TwoSortConv (mkSigma A₁ B₁) (mkSigma A₂ B₂)
  -- Congruence: Id
  | congId : TwoSortConv A₁ A₂ → TwoSortConv a₁ a₂ → TwoSortConv b₁ b₂ →
      TwoSortConv (mkId A₁ a₁ b₁) (mkId A₂ a₂ b₂)
  -- Congruence: Lam (cofinite — under binder)
  | congLam (L : Finset String) :
      (∀ x, x ∉ L → TwoSortConv (openBVar 0 (.fvar x) body₁) (openBVar 0 (.fvar x) body₂)) →
      TwoSortConv (mkLam body₁) (mkLam body₂)
  -- Congruence: App
  | congApp : TwoSortConv f₁ f₂ → TwoSortConv a₁ a₂ →
      TwoSortConv (mkApp f₁ a₁) (mkApp f₂ a₂)
  -- Congruence: Pair
  | congPair : TwoSortConv a₁ a₂ → TwoSortConv b₁ b₂ →
      TwoSortConv (mkPair a₁ b₁) (mkPair a₂ b₂)
  -- Congruence: Fst
  | congFst : TwoSortConv p₁ p₂ →
      TwoSortConv (mkFst p₁) (mkFst p₂)
  -- Congruence: Snd
  | congSnd : TwoSortConv p₁ p₂ →
      TwoSortConv (mkSnd p₁) (mkSnd p₂)
  -- Congruence: Refl
  | congRefl : TwoSortConv a₁ a₂ →
      TwoSortConv (mkRefl a₁) (mkRefl a₂)
/-! ## Typing Judgment

`TwoSortHasType Γ t A` — "in context Γ, term t has type A."

Uses **cofinite quantification** for binder rules: rather than picking a
specific fresh name, we require the body to type-check for ALL names
outside a finite "bad" set L. This is the standard locally nameless
technique that makes the substitution lemma provable.

Key property: terms in the typing judgment are **locally closed** —
no bare `bvar` at the top level. Under a binder, `bvar 0` is opened
with a fresh `fvar x`, and `x` is added to the context. -/

inductive TwoSortHasType : TwoSortCtx → Pattern → Pattern → Prop where
  /-- Universe formation: `U0 : U1` in any context. -/
  | u0_type (Γ : TwoSortCtx) :
      TwoSortHasType Γ u0 u1

  /-- Free variable: `fvar x : A` when `(x, A) ∈ Γ` and `A` is locally closed.
      The `hA_lc` premise ensures contexts only assign locally closed types,
      while `hA_twoSort` keeps the legacy typed layer inside the explicit two-sort
      fragment. -/
  | fvar (Γ : TwoSortCtx) (x : String) (A : Pattern)
      (hmem : (x, A) ∈ Γ)
      (hA_twoSort : TwoSortTermPattern A)
      (hA_lc : lc_at 0 A = true) :
      TwoSortHasType Γ (.fvar x) A

  /-- Π-formation: if `A : U` and for all fresh `x`, `B[x] : U` in
      context extended with `x : A`, then `Π(A, B) : U`. -/
  | pi_form (Γ : TwoSortCtx) (L : Finset String) (A B : Pattern) (U : Pattern)
      (hA : TwoSortHasType Γ A U)
      (hB : ∀ x, x ∉ L →
        TwoSortHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      TwoSortHasType Γ (mkPi A B) U

  /-- Π-introduction: `λ.body : Π(A, B)` when for all fresh `x`,
      `body[x] : B[x]` in extended context. -/
  | lam_intro (Γ : TwoSortCtx) (L : Finset String)
      (A body B : Pattern) (U : Pattern)
      (hA : TwoSortHasType Γ A U)
      (hBody : ∀ x, x ∉ L →
        TwoSortHasType ((x, A) :: Γ)
          (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) B)) :
      TwoSortHasType Γ (mkLam body) (mkPi A B)

  /-- Π-elimination: if `f : Π(A, B)` and `a : A`, then `f a : B[a]`.
      The codomain witness `hB` records that `B` is well-formed — standard
      practice in DTT formalizations to support the subject reduction proof. -/
  | app (Γ : TwoSortCtx) (L : Finset String) (f a A B : Pattern) (U : Pattern)
      (hf : TwoSortHasType Γ f (mkPi A B))
      (ha : TwoSortHasType Γ a A)
      (hB : ∀ x, x ∉ L →
        TwoSortHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      TwoSortHasType Γ (mkApp f a) (openBVar 0 a B)

  /-- Σ-formation: analogous to Π-formation. -/
  | sigma_form (Γ : TwoSortCtx) (L : Finset String) (A B : Pattern) (U : Pattern)
      (hA : TwoSortHasType Γ A U)
      (hB : ∀ x, x ∉ L →
        TwoSortHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      TwoSortHasType Γ (mkSigma A B) U

  /-- Σ-introduction: `(a, b) : Σ(A, B)` when `a : A`, `b : B[a]`, and `B` is
      well-formed. The codomain witness `hB` is standard practice in DTT
      formalizations to support subject reduction (cf. Adjedj et al. 2023). -/
  | pair_intro (Γ : TwoSortCtx) (L : Finset String) (a b A B : Pattern) (U : Pattern)
      (ha : TwoSortHasType Γ a A)
      (hb : TwoSortHasType Γ b (openBVar 0 a B))
      (hB : ∀ x, x ∉ L →
        TwoSortHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      TwoSortHasType Γ (mkPair a b) (mkSigma A B)

  /-- Σ-elimination (fst): `fst p : A` when `p : Σ(A, B)`. -/
  | fst_elim (Γ : TwoSortCtx) (L : Finset String) (p A B : Pattern) (U : Pattern)
      (hp : TwoSortHasType Γ p (mkSigma A B))
      (hB : ∀ x, x ∉ L →
        TwoSortHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      TwoSortHasType Γ (mkFst p) A

  /-- Σ-elimination (snd): `snd p : B[fst p]` when `p : Σ(A, B)`. -/
  | snd_elim (Γ : TwoSortCtx) (L : Finset String) (p A B : Pattern) (U : Pattern)
      (hp : TwoSortHasType Γ p (mkSigma A B))
      (hB : ∀ x, x ∉ L →
        TwoSortHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      TwoSortHasType Γ (mkSnd p) (openBVar 0 (mkFst p) B)

  /-- Id-formation: `Id(A, a, b) : U` when `A : U`, `a : A`, `b : A`. -/
  | id_form (Γ : TwoSortCtx) (A a b : Pattern) (U : Pattern)
      (hA : TwoSortHasType Γ A U)
      (ha : TwoSortHasType Γ a A)
      (hb : TwoSortHasType Γ b A) :
      TwoSortHasType Γ (mkId A a b) U

  /-- Id-introduction: `refl a : Id(A, a, a)` when `a : A`. -/
  | refl_intro (Γ : TwoSortCtx) (a A : Pattern)
      (ha : TwoSortHasType Γ a A) :
      TwoSortHasType Γ (mkRefl a) (mkId A a a)

  /-- Conversion: change type along definitional equality. -/
  | conv (Γ : TwoSortCtx) (t A B : Pattern)
      (ht : TwoSortHasType Γ t A)
      (hconv : TwoSortConv A B) :
      TwoSortHasType Γ t B

/-- Fragment membership on both sides of conversion. -/
theorem TwoSortConv_twoSort_both : {s t : Pattern} → TwoSortConv s t → TwoSortTermPattern s ∧ TwoSortTermPattern t
  | _, _, .refl _ htwoSort =>
      ⟨htwoSort, htwoSort⟩
  | _, _, .symm h =>
      let ih := TwoSortConv_twoSort_both h
      ⟨ih.2, ih.1⟩
  | _, _, .trans h₁ h₂ =>
      let ih₁ := TwoSortConv_twoSort_both h₁
      let ih₂ := TwoSortConv_twoSort_both h₂
      ⟨ih₁.1, ih₂.2⟩
  | _, _, .betaPi body a hbodyTwoSort haTwoSort _ _ =>
      ⟨.app (.lam hbodyTwoSort) haTwoSort, twoSortTm_openBVar haTwoSort hbodyTwoSort⟩
  | _, _, .betaSigmaFst a b haTwoSort hbTwoSort _ _ =>
      ⟨.fst (.pair haTwoSort hbTwoSort), haTwoSort⟩
  | _, _, .betaSigmaSnd a b haTwoSort hbTwoSort _ _ =>
      ⟨.snd (.pair haTwoSort hbTwoSort), hbTwoSort⟩
  | _, _, @TwoSortConv.congPi A₁ A₂ B₁ B₂ L hA hB =>
      let ihA := TwoSortConv_twoSort_both hA
      have ihB : ∀ x, x ∉ L →
          TwoSortTermPattern (openBVar 0 (.fvar x) B₁) ∧ TwoSortTermPattern (openBVar 0 (.fvar x) B₂) := by
        intro x hx
        exact TwoSortConv_twoSort_both (hB x hx)
      have hB₁ : TwoSortTermPattern B₁ := by
        let S := L ∪ listToFinset (freeVars B₁)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B₁) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (ihB x hxL |>.1) (isFresh_of_not_in_freeVars_finset hxB)
      have hB₂ : TwoSortTermPattern B₂ := by
        let S := L ∪ listToFinset (freeVars B₂)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B₂) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (ihB x hxL |>.2) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.pi ihA.1 hB₁, .pi ihA.2 hB₂⟩
  | _, _, @TwoSortConv.congSigma A₁ A₂ B₁ B₂ L hA hB =>
      let ihA := TwoSortConv_twoSort_both hA
      have ihB : ∀ x, x ∉ L →
          TwoSortTermPattern (openBVar 0 (.fvar x) B₁) ∧ TwoSortTermPattern (openBVar 0 (.fvar x) B₂) := by
        intro x hx
        exact TwoSortConv_twoSort_both (hB x hx)
      have hB₁ : TwoSortTermPattern B₁ := by
        let S := L ∪ listToFinset (freeVars B₁)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B₁) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (ihB x hxL |>.1) (isFresh_of_not_in_freeVars_finset hxB)
      have hB₂ : TwoSortTermPattern B₂ := by
        let S := L ∪ listToFinset (freeVars B₂)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B₂) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (ihB x hxL |>.2) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.sigma ihA.1 hB₁, .sigma ihA.2 hB₂⟩
  | _, _, @TwoSortConv.congId A₁ A₂ a₁ a₂ b₁ b₂ hA ha hb =>
      let ihA := TwoSortConv_twoSort_both hA
      let iha := TwoSortConv_twoSort_both ha
      let ihb := TwoSortConv_twoSort_both hb
      ⟨.id ihA.1 iha.1 ihb.1, .id ihA.2 iha.2 ihb.2⟩
  | _, _, @TwoSortConv.congLam body₁ body₂ L h =>
      have ih : ∀ x, x ∉ L →
          TwoSortTermPattern (openBVar 0 (.fvar x) body₁) ∧ TwoSortTermPattern (openBVar 0 (.fvar x) body₂) := by
        intro x hx
        exact TwoSortConv_twoSort_both (h x hx)
      have hBody₁ : TwoSortTermPattern body₁ := by
        let S := L ∪ listToFinset (freeVars body₁)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars body₁) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (ih x hxL |>.1) (isFresh_of_not_in_freeVars_finset hxB)
      have hBody₂ : TwoSortTermPattern body₂ := by
        let S := L ∪ listToFinset (freeVars body₂)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars body₂) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (ih x hxL |>.2) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.lam hBody₁, .lam hBody₂⟩
  | _, _, @TwoSortConv.congApp f₁ f₂ a₁ a₂ hf ha =>
      let ihf := TwoSortConv_twoSort_both hf
      let iha := TwoSortConv_twoSort_both ha
      ⟨.app ihf.1 iha.1, .app ihf.2 iha.2⟩
  | _, _, @TwoSortConv.congPair a₁ a₂ b₁ b₂ ha hb =>
      let iha := TwoSortConv_twoSort_both ha
      let ihb := TwoSortConv_twoSort_both hb
      ⟨.pair iha.1 ihb.1, .pair iha.2 ihb.2⟩
  | _, _, @TwoSortConv.congFst p₁ p₂ hp =>
      let ih := TwoSortConv_twoSort_both hp
      ⟨.fst ih.1, .fst ih.2⟩
  | _, _, @TwoSortConv.congSnd p₁ p₂ hp =>
      let ih := TwoSortConv_twoSort_both hp
      ⟨.snd ih.1, .snd ih.2⟩
  | _, _, @TwoSortConv.congRefl a₁ a₂ ha =>
      let ih := TwoSortConv_twoSort_both ha
      ⟨.refl ih.1, .refl ih.2⟩

theorem TwoSortConv_leftTwoSort {s t : Pattern} (h : TwoSortConv s t) : TwoSortTermPattern s :=
  (TwoSortConv_twoSort_both h).1

theorem TwoSortConv_rightTwoSort {s t : Pattern} (h : TwoSortConv s t) : TwoSortTermPattern t :=
  (TwoSortConv_twoSort_both h).2

/-- Well-typed legacy two-sort terms stay inside the explicit two-sort fragment,
    and so do their types. -/
theorem typing_twoSort_both : {Γ : TwoSortCtx} → {t A : Pattern} →
    TwoSortHasType Γ t A → TwoSortTermPattern t ∧ TwoSortTermPattern A
  | _, _, _, .u0_type _ =>
      ⟨.u0, .u1⟩
  | _, _, _, .fvar _ x _ _ hA_twoSort _ =>
      ⟨.fvar x, hA_twoSort⟩
  | _, _, _, .pi_form _ L A B U hA hB =>
      let ihA := typing_twoSort_both hA
      have hOpenB : ∀ x, x ∉ L → TwoSortTermPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_twoSort_both (hB x hx)).1
      have hBtwoSort : TwoSortTermPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.pi ihA.1 hBtwoSort, ihA.2⟩
  | _, _, _, .lam_intro _ L A body B U hA hBody =>
      let ihA := typing_twoSort_both hA
      have hOpenBody : ∀ x, x ∉ L → TwoSortTermPattern (openBVar 0 (.fvar x) body) := by
        intro x hx
        exact (typing_twoSort_both (hBody x hx)).1
      have hOpenB : ∀ x, x ∉ L → TwoSortTermPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_twoSort_both (hBody x hx)).2
      have hBodyTwoSort : TwoSortTermPattern body := by
        let S := L ∪ listToFinset (freeVars body)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars body) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (hOpenBody x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      have hBTwoSort : TwoSortTermPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.lam hBodyTwoSort, .pi ihA.1 hBTwoSort⟩
  | _, _, _, .app _ L f a A B _ hf ha hB =>
      let ihf := typing_twoSort_both hf
      let iha := typing_twoSort_both ha
      have hOpenB : ∀ x, x ∉ L → TwoSortTermPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_twoSort_both (hB x hx)).1
      have hBTwoSort : TwoSortTermPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.app ihf.1 iha.1, twoSortTm_openBVar iha.1 hBTwoSort⟩
  | _, _, _, .sigma_form _ L A B U hA hB =>
      let ihA := typing_twoSort_both hA
      have hOpenB : ∀ x, x ∉ L → TwoSortTermPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_twoSort_both (hB x hx)).1
      have hBtwoSort : TwoSortTermPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.sigma ihA.1 hBtwoSort, ihA.2⟩
  | _, _, _, .pair_intro _ L a b A B _ ha hb hB =>
      let iha := typing_twoSort_both ha
      let ihb := typing_twoSort_both hb
      have hOpenB : ∀ x, x ∉ L → TwoSortTermPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_twoSort_both (hB x hx)).1
      have hBTwoSort : TwoSortTermPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.pair iha.1 ihb.1, .sigma iha.2 hBTwoSort⟩
  | _, _, _, .fst_elim _ _ _ _ _ _ hp _ =>
      let ihp := typing_twoSort_both hp
      let hAB := twoSort_sigma_inv ihp.2
      ⟨.fst ihp.1, hAB.1⟩
  | _, _, _, .snd_elim _ L p A B _ hp hB =>
      let ihp := typing_twoSort_both hp
      have hOpenB : ∀ x, x ∉ L → TwoSortTermPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_twoSort_both (hB x hx)).1
      have hBTwoSort : TwoSortTermPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact twoSortTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.snd ihp.1, twoSortTm_openBVar (.fst ihp.1) hBTwoSort⟩
  | _, _, _, .id_form _ _ _ _ _ hA ha hb =>
      let ihA := typing_twoSort_both hA
      let iha := typing_twoSort_both ha
      let ihb := typing_twoSort_both hb
      ⟨.id ihA.1 iha.1 ihb.1, ihA.2⟩
  | _, _, _, .refl_intro _ _ _ ha =>
      let iha := typing_twoSort_both ha
      ⟨.refl iha.1, .id iha.2 iha.1 iha.1⟩
  | _, _, _, .conv _ _ _ _ ht hconv =>
      let iht := typing_twoSort_both ht
      ⟨iht.1, TwoSortConv_rightTwoSort hconv⟩

theorem typing_term_twoSort {Γ : TwoSortCtx} {t A : Pattern}
    (ht : TwoSortHasType Γ t A) : TwoSortTermPattern t :=
  (typing_twoSort_both ht).1

theorem typing_type_twoSort {Γ : TwoSortCtx} {t A : Pattern}
    (ht : TwoSortHasType Γ t A) : TwoSortTermPattern A :=
  (typing_twoSort_both ht).2

/-! ## Concrete Typing Examples -/

/-- U0 : U1 in the empty context. -/
theorem u0_has_type_u1 : TwoSortHasType [] u0 u1 :=
  .u0_type []

/-- The identity function λx.x has type Π(U0, U0).
    The body `.bvar 0` is opened with fresh `fvar x`, yielding `fvar x`,
    which has type U0 in context `[(x, U0)]`. -/
theorem identity_type : TwoSortHasType [] (mkLam (.bvar 0)) (mkPi u0 u0) :=
  .lam_intro [] ∅ u0 (.bvar 0) u0 u1 (.u0_type [])
    (fun x _ => by
      simp only [openBVar, u0]
      exact .fvar [(x, .apply "U0" [])] x (.apply "U0" [])
        List.mem_cons_self TwoSortTermPattern.u0 (by simp [lc_at, lc_at_list]))

/-- First projection λA.λB.A : Π(U0, Π(U0, U0)).
    Takes two type arguments and returns the first. -/
theorem fst_proj_type :
    TwoSortHasType [] (mkLam (mkLam (.bvar 1))) (mkPi u0 (mkPi u0 u0)) := by
  apply TwoSortHasType.lam_intro [] ∅ u0 (mkLam (.bvar 1)) (mkPi u0 u0) u1
    (.u0_type [])
  intro x _
  -- Reduce: openBVar 0 (fvar x) (mkLam (bvar 1)) = mkLam (fvar x)
  --         openBVar 0 (fvar x) (mkPi u0 u0) = mkPi u0 u0
  simp only [openBVar, mkLam, mkPi, u0, List.map]
  apply TwoSortHasType.lam_intro _ ∅
    (.apply "U0" []) (.fvar x) (.apply "U0" []) (.apply "U1" [])
    (.u0_type _)
  intro y _
  simp only [openBVar]
  exact .fvar _ x (.apply "U0" [])
    (List.mem_cons_of_mem _ List.mem_cons_self) TwoSortTermPattern.u0 (by simp [lc_at, lc_at_list])

/-! ## Summary

**0 sorries. 0 axioms.**

Defines:
- `TwoSortConv` — intensional definitional equality (3 β-rules + congruence)
- `TwoSortHasType` — dependent typing judgment (12 rules) with cofinite quantification
- Three concrete typing examples (U0 : U1, identity, first projection)

**Next**: `Reduction.lean` defines `TwoSortReduces` and proves `TwoSortReduces → TwoSortConv`.
-/

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Typing
