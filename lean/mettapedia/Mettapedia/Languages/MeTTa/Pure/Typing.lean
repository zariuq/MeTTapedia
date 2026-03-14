import Mettapedia.Languages.MeTTa.Pure.Core
import Mettapedia.Languages.MeTTa.Pure.BinderOps
import Mettapedia.Languages.MeTTa.Pure.Fragment
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# MeTTa-Pure: Typing and Conversion (Locally Nameless)

Defines the **dependent typing judgment** `PureHasType Γ t A` and the
**definitional equality** `PureConv t₁ t₂` for MeTTa-Pure.

## Design Decisions

- **Russell-style**: `U0 : U1` — no separate Type/Kind judgment
- **Intensional**: `PureConv` is β only — no functional extensionality
- **Declarative**: no bidirectional checking yet (that's future work)
- **Locally nameless with cofinite quantification**: binder rules open with
  fresh `fvar x` and universally quantify over all sufficiently fresh names.
  This follows Aydemir et al., "Engineering Formal Metatheory" (POPL 2008).
- **No J-eliminator initially**: just `Refl`; J is a later extension

## Context Convention

Contexts are association lists mapping free variable names to their types:
  `Γ = [(xₙ, Aₙ), ..., (x₁, A₁), (x₀, A₀)]`
Most recently bound variable is at the head.

## References

- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
- Martin-Löf, "Intuitionistic Type Theory" (1984)
- Adjedj et al., "Martin-Löf à la Coq" (2023, arXiv:2310.06376)
-/

namespace Mettapedia.Languages.MeTTa.Pure.Typing

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.BinderOps
open Mettapedia.Languages.MeTTa.Pure.Fragment

/-! ## Contexts -/

/-- A MeTTa-Pure context: an association list mapping free variable names
    to their types. Most recently bound at the head. -/
abbrev PureCtx := List (String × Pattern)

/-- Domain of a context (the set of bound variable names). -/
def ctxDom (Γ : PureCtx) : List String := Γ.map Prod.fst

/-! ## Definitional Equality (Conversion)

`PureConv t₁ t₂` is the reflexive-symmetric-transitive closure of the three
β-rules, plus congruence in all type/term formers.

This is intensional: no η, no functional extensionality, no UIP. -/

/-- Definitional equality for MeTTa-Pure.
    This relation is restricted to the explicit pure fragment, so the
    metatheory never has to invent fragment-membership witnesses later. -/
inductive PureConv : Pattern → Pattern → Prop where
  -- Equivalence
  | refl (t : Pattern) (hpure : PureTmPattern t) : PureConv t t
  | symm : PureConv t₁ t₂ → PureConv t₂ t₁
  | trans : PureConv t₁ t₂ → PureConv t₂ t₃ → PureConv t₁ t₃

  -- β-rules (require lc so PureConv preserves local closure in both directions)
  | betaPi (body a : Pattern)
      (hbodyPure : PureTmPattern body) (haPure : PureTmPattern a)
      (hlcBody : lc_at 1 body = true) (hlcA : lc_at 0 a = true) :
      PureConv (mkApp (mkLam body) a) (openBVar 0 a body)
  | betaSigmaFst (a b : Pattern)
      (haPure : PureTmPattern a) (hbPure : PureTmPattern b)
      (hlcA : lc_at 0 a = true) (hlcB : lc_at 0 b = true) :
      PureConv (mkFst (mkPair a b)) a
  | betaSigmaSnd (a b : Pattern)
      (haPure : PureTmPattern a) (hbPure : PureTmPattern b)
      (hlcA : lc_at 0 a = true) (hlcB : lc_at 0 b = true) :
      PureConv (mkSnd (mkPair a b)) b

  -- Congruence: Pi (cofinite for codomain — under binder)
  | congPi (L : Finset String) :
      PureConv A₁ A₂ →
      (∀ x, x ∉ L → PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) →
      PureConv (mkPi A₁ B₁) (mkPi A₂ B₂)
  -- Congruence: Sigma (cofinite for codomain — under binder)
  | congSigma (L : Finset String) :
      PureConv A₁ A₂ →
      (∀ x, x ∉ L → PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) →
      PureConv (mkSigma A₁ B₁) (mkSigma A₂ B₂)
  -- Congruence: Id
  | congId : PureConv A₁ A₂ → PureConv a₁ a₂ → PureConv b₁ b₂ →
      PureConv (mkId A₁ a₁ b₁) (mkId A₂ a₂ b₂)
  -- Congruence: Lam (cofinite — under binder)
  | congLam (L : Finset String) :
      (∀ x, x ∉ L → PureConv (openBVar 0 (.fvar x) body₁) (openBVar 0 (.fvar x) body₂)) →
      PureConv (mkLam body₁) (mkLam body₂)
  -- Congruence: App
  | congApp : PureConv f₁ f₂ → PureConv a₁ a₂ →
      PureConv (mkApp f₁ a₁) (mkApp f₂ a₂)
  -- Congruence: Pair
  | congPair : PureConv a₁ a₂ → PureConv b₁ b₂ →
      PureConv (mkPair a₁ b₁) (mkPair a₂ b₂)
  -- Congruence: Fst
  | congFst : PureConv p₁ p₂ →
      PureConv (mkFst p₁) (mkFst p₂)
  -- Congruence: Snd
  | congSnd : PureConv p₁ p₂ →
      PureConv (mkSnd p₁) (mkSnd p₂)
  -- Congruence: Refl
  | congRefl : PureConv a₁ a₂ →
      PureConv (mkRefl a₁) (mkRefl a₂)
/-! ## Typing Judgment

`PureHasType Γ t A` — "in context Γ, term t has type A."

Uses **cofinite quantification** for binder rules: rather than picking a
specific fresh name, we require the body to type-check for ALL names
outside a finite "bad" set L. This is the standard locally nameless
technique that makes the substitution lemma provable.

Key property: terms in the typing judgment are **locally closed** —
no bare `bvar` at the top level. Under a binder, `bvar 0` is opened
with a fresh `fvar x`, and `x` is added to the context. -/

inductive PureHasType : PureCtx → Pattern → Pattern → Prop where
  /-- Universe formation: `U0 : U1` in any context. -/
  | u0_type (Γ : PureCtx) :
      PureHasType Γ u0 u1

  /-- Free variable: `fvar x : A` when `(x, A) ∈ Γ` and `A` is locally closed.
      The `hA_lc` premise ensures contexts only assign locally closed types,
      while `hA_pure` keeps the legacy typed layer inside the explicit pure
      fragment. -/
  | fvar (Γ : PureCtx) (x : String) (A : Pattern)
      (hmem : (x, A) ∈ Γ)
      (hA_pure : PureTmPattern A)
      (hA_lc : lc_at 0 A = true) :
      PureHasType Γ (.fvar x) A

  /-- Π-formation: if `A : U` and for all fresh `x`, `B[x] : U` in
      context extended with `x : A`, then `Π(A, B) : U`. -/
  | pi_form (Γ : PureCtx) (L : Finset String) (A B : Pattern) (U : Pattern)
      (hA : PureHasType Γ A U)
      (hB : ∀ x, x ∉ L →
        PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      PureHasType Γ (mkPi A B) U

  /-- Π-introduction: `λ.body : Π(A, B)` when for all fresh `x`,
      `body[x] : B[x]` in extended context. -/
  | lam_intro (Γ : PureCtx) (L : Finset String)
      (A body B : Pattern) (U : Pattern)
      (hA : PureHasType Γ A U)
      (hBody : ∀ x, x ∉ L →
        PureHasType ((x, A) :: Γ)
          (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) B)) :
      PureHasType Γ (mkLam body) (mkPi A B)

  /-- Π-elimination: if `f : Π(A, B)` and `a : A`, then `f a : B[a]`.
      The codomain witness `hB` records that `B` is well-formed — standard
      practice in DTT formalizations to support the subject reduction proof. -/
  | app (Γ : PureCtx) (L : Finset String) (f a A B : Pattern) (U : Pattern)
      (hf : PureHasType Γ f (mkPi A B))
      (ha : PureHasType Γ a A)
      (hB : ∀ x, x ∉ L →
        PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      PureHasType Γ (mkApp f a) (openBVar 0 a B)

  /-- Σ-formation: analogous to Π-formation. -/
  | sigma_form (Γ : PureCtx) (L : Finset String) (A B : Pattern) (U : Pattern)
      (hA : PureHasType Γ A U)
      (hB : ∀ x, x ∉ L →
        PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      PureHasType Γ (mkSigma A B) U

  /-- Σ-introduction: `(a, b) : Σ(A, B)` when `a : A`, `b : B[a]`, and `B` is
      well-formed. The codomain witness `hB` is standard practice in DTT
      formalizations to support subject reduction (cf. Adjedj et al. 2023). -/
  | pair_intro (Γ : PureCtx) (L : Finset String) (a b A B : Pattern) (U : Pattern)
      (ha : PureHasType Γ a A)
      (hb : PureHasType Γ b (openBVar 0 a B))
      (hB : ∀ x, x ∉ L →
        PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      PureHasType Γ (mkPair a b) (mkSigma A B)

  /-- Σ-elimination (fst): `fst p : A` when `p : Σ(A, B)`. -/
  | fst_elim (Γ : PureCtx) (L : Finset String) (p A B : Pattern) (U : Pattern)
      (hp : PureHasType Γ p (mkSigma A B))
      (hB : ∀ x, x ∉ L →
        PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      PureHasType Γ (mkFst p) A

  /-- Σ-elimination (snd): `snd p : B[fst p]` when `p : Σ(A, B)`. -/
  | snd_elim (Γ : PureCtx) (L : Finset String) (p A B : Pattern) (U : Pattern)
      (hp : PureHasType Γ p (mkSigma A B))
      (hB : ∀ x, x ∉ L →
        PureHasType ((x, A) :: Γ) (openBVar 0 (.fvar x) B) U) :
      PureHasType Γ (mkSnd p) (openBVar 0 (mkFst p) B)

  /-- Id-formation: `Id(A, a, b) : U` when `A : U`, `a : A`, `b : A`. -/
  | id_form (Γ : PureCtx) (A a b : Pattern) (U : Pattern)
      (hA : PureHasType Γ A U)
      (ha : PureHasType Γ a A)
      (hb : PureHasType Γ b A) :
      PureHasType Γ (mkId A a b) U

  /-- Id-introduction: `refl a : Id(A, a, a)` when `a : A`. -/
  | refl_intro (Γ : PureCtx) (a A : Pattern)
      (ha : PureHasType Γ a A) :
      PureHasType Γ (mkRefl a) (mkId A a a)

  /-- Conversion: change type along definitional equality. -/
  | conv (Γ : PureCtx) (t A B : Pattern)
      (ht : PureHasType Γ t A)
      (hconv : PureConv A B) :
      PureHasType Γ t B

/-- Fragment membership on both sides of conversion. -/
theorem PureConv_pure_both : {s t : Pattern} → PureConv s t → PureTmPattern s ∧ PureTmPattern t
  | _, _, .refl _ hpure =>
      ⟨hpure, hpure⟩
  | _, _, .symm h =>
      let ih := PureConv_pure_both h
      ⟨ih.2, ih.1⟩
  | _, _, .trans h₁ h₂ =>
      let ih₁ := PureConv_pure_both h₁
      let ih₂ := PureConv_pure_both h₂
      ⟨ih₁.1, ih₂.2⟩
  | _, _, .betaPi body a hbodyPure haPure _ _ =>
      ⟨.app (.lam hbodyPure) haPure, pureTm_openBVar haPure hbodyPure⟩
  | _, _, .betaSigmaFst a b haPure hbPure _ _ =>
      ⟨.fst (.pair haPure hbPure), haPure⟩
  | _, _, .betaSigmaSnd a b haPure hbPure _ _ =>
      ⟨.snd (.pair haPure hbPure), hbPure⟩
  | _, _, @PureConv.congPi A₁ A₂ B₁ B₂ L hA hB =>
      let ihA := PureConv_pure_both hA
      have ihB : ∀ x, x ∉ L →
          PureTmPattern (openBVar 0 (.fvar x) B₁) ∧ PureTmPattern (openBVar 0 (.fvar x) B₂) := by
        intro x hx
        exact PureConv_pure_both (hB x hx)
      have hB₁ : PureTmPattern B₁ := by
        let S := L ∪ listToFinset (freeVars B₁)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B₁) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (ihB x hxL |>.1) (isFresh_of_not_in_freeVars_finset hxB)
      have hB₂ : PureTmPattern B₂ := by
        let S := L ∪ listToFinset (freeVars B₂)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B₂) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (ihB x hxL |>.2) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.pi ihA.1 hB₁, .pi ihA.2 hB₂⟩
  | _, _, @PureConv.congSigma A₁ A₂ B₁ B₂ L hA hB =>
      let ihA := PureConv_pure_both hA
      have ihB : ∀ x, x ∉ L →
          PureTmPattern (openBVar 0 (.fvar x) B₁) ∧ PureTmPattern (openBVar 0 (.fvar x) B₂) := by
        intro x hx
        exact PureConv_pure_both (hB x hx)
      have hB₁ : PureTmPattern B₁ := by
        let S := L ∪ listToFinset (freeVars B₁)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B₁) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (ihB x hxL |>.1) (isFresh_of_not_in_freeVars_finset hxB)
      have hB₂ : PureTmPattern B₂ := by
        let S := L ∪ listToFinset (freeVars B₂)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B₂) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (ihB x hxL |>.2) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.sigma ihA.1 hB₁, .sigma ihA.2 hB₂⟩
  | _, _, @PureConv.congId A₁ A₂ a₁ a₂ b₁ b₂ hA ha hb =>
      let ihA := PureConv_pure_both hA
      let iha := PureConv_pure_both ha
      let ihb := PureConv_pure_both hb
      ⟨.id ihA.1 iha.1 ihb.1, .id ihA.2 iha.2 ihb.2⟩
  | _, _, @PureConv.congLam body₁ body₂ L h =>
      have ih : ∀ x, x ∉ L →
          PureTmPattern (openBVar 0 (.fvar x) body₁) ∧ PureTmPattern (openBVar 0 (.fvar x) body₂) := by
        intro x hx
        exact PureConv_pure_both (h x hx)
      have hBody₁ : PureTmPattern body₁ := by
        let S := L ∪ listToFinset (freeVars body₁)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars body₁) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (ih x hxL |>.1) (isFresh_of_not_in_freeVars_finset hxB)
      have hBody₂ : PureTmPattern body₂ := by
        let S := L ∪ listToFinset (freeVars body₂)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars body₂) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (ih x hxL |>.2) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.lam hBody₁, .lam hBody₂⟩
  | _, _, @PureConv.congApp f₁ f₂ a₁ a₂ hf ha =>
      let ihf := PureConv_pure_both hf
      let iha := PureConv_pure_both ha
      ⟨.app ihf.1 iha.1, .app ihf.2 iha.2⟩
  | _, _, @PureConv.congPair a₁ a₂ b₁ b₂ ha hb =>
      let iha := PureConv_pure_both ha
      let ihb := PureConv_pure_both hb
      ⟨.pair iha.1 ihb.1, .pair iha.2 ihb.2⟩
  | _, _, @PureConv.congFst p₁ p₂ hp =>
      let ih := PureConv_pure_both hp
      ⟨.fst ih.1, .fst ih.2⟩
  | _, _, @PureConv.congSnd p₁ p₂ hp =>
      let ih := PureConv_pure_both hp
      ⟨.snd ih.1, .snd ih.2⟩
  | _, _, @PureConv.congRefl a₁ a₂ ha =>
      let ih := PureConv_pure_both ha
      ⟨.refl ih.1, .refl ih.2⟩

theorem PureConv_leftPure {s t : Pattern} (h : PureConv s t) : PureTmPattern s :=
  (PureConv_pure_both h).1

theorem PureConv_rightPure {s t : Pattern} (h : PureConv s t) : PureTmPattern t :=
  (PureConv_pure_both h).2

/-- Well-typed legacy Pure terms stay inside the explicit pure fragment,
    and so do their types. -/
theorem typing_pure_both : {Γ : PureCtx} → {t A : Pattern} →
    PureHasType Γ t A → PureTmPattern t ∧ PureTmPattern A
  | _, _, _, .u0_type _ =>
      ⟨.u0, .u1⟩
  | _, _, _, .fvar _ x _ _ hA_pure _ =>
      ⟨.fvar x, hA_pure⟩
  | _, _, _, .pi_form _ L A B U hA hB =>
      let ihA := typing_pure_both hA
      have hOpenB : ∀ x, x ∉ L → PureTmPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_pure_both (hB x hx)).1
      have hBpure : PureTmPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.pi ihA.1 hBpure, ihA.2⟩
  | _, _, _, .lam_intro _ L A body B U hA hBody =>
      let ihA := typing_pure_both hA
      have hOpenBody : ∀ x, x ∉ L → PureTmPattern (openBVar 0 (.fvar x) body) := by
        intro x hx
        exact (typing_pure_both (hBody x hx)).1
      have hOpenB : ∀ x, x ∉ L → PureTmPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_pure_both (hBody x hx)).2
      have hBodyPure : PureTmPattern body := by
        let S := L ∪ listToFinset (freeVars body)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars body) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (hOpenBody x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      have hBPure : PureTmPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.lam hBodyPure, .pi ihA.1 hBPure⟩
  | _, _, _, .app _ L f a A B _ hf ha hB =>
      let ihf := typing_pure_both hf
      let iha := typing_pure_both ha
      have hOpenB : ∀ x, x ∉ L → PureTmPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_pure_both (hB x hx)).1
      have hBPure : PureTmPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.app ihf.1 iha.1, pureTm_openBVar iha.1 hBPure⟩
  | _, _, _, .sigma_form _ L A B U hA hB =>
      let ihA := typing_pure_both hA
      have hOpenB : ∀ x, x ∉ L → PureTmPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_pure_both (hB x hx)).1
      have hBpure : PureTmPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.sigma ihA.1 hBpure, ihA.2⟩
  | _, _, _, .pair_intro _ L a b A B _ ha hb hB =>
      let iha := typing_pure_both ha
      let ihb := typing_pure_both hb
      have hOpenB : ∀ x, x ∉ L → PureTmPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_pure_both (hB x hx)).1
      have hBPure : PureTmPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.pair iha.1 ihb.1, .sigma iha.2 hBPure⟩
  | _, _, _, .fst_elim _ _ _ _ _ _ hp _ =>
      let ihp := typing_pure_both hp
      let hAB := pure_sigma_inv ihp.2
      ⟨.fst ihp.1, hAB.1⟩
  | _, _, _, .snd_elim _ L p A B _ hp hB =>
      let ihp := typing_pure_both hp
      have hOpenB : ∀ x, x ∉ L → PureTmPattern (openBVar 0 (.fvar x) B) := by
        intro x hx
        exact (typing_pure_both (hB x hx)).1
      have hBPure : PureTmPattern B := by
        let S := L ∪ listToFinset (freeVars B)
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
        have hxL : x ∉ L := fun hmem => hx (Finset.mem_union_left _ hmem)
        have hxB : x ∉ listToFinset (freeVars B) := fun hmem => hx (Finset.mem_union_right _ hmem)
        exact pureTm_of_openBVar_fresh x (hOpenB x hxL) (isFresh_of_not_in_freeVars_finset hxB)
      ⟨.snd ihp.1, pureTm_openBVar (.fst ihp.1) hBPure⟩
  | _, _, _, .id_form _ _ _ _ _ hA ha hb =>
      let ihA := typing_pure_both hA
      let iha := typing_pure_both ha
      let ihb := typing_pure_both hb
      ⟨.id ihA.1 iha.1 ihb.1, ihA.2⟩
  | _, _, _, .refl_intro _ _ _ ha =>
      let iha := typing_pure_both ha
      ⟨.refl iha.1, .id iha.2 iha.1 iha.1⟩
  | _, _, _, .conv _ _ _ _ ht hconv =>
      let iht := typing_pure_both ht
      ⟨iht.1, PureConv_rightPure hconv⟩

theorem typing_term_pure {Γ : PureCtx} {t A : Pattern}
    (ht : PureHasType Γ t A) : PureTmPattern t :=
  (typing_pure_both ht).1

theorem typing_type_pure {Γ : PureCtx} {t A : Pattern}
    (ht : PureHasType Γ t A) : PureTmPattern A :=
  (typing_pure_both ht).2

/-! ## Concrete Typing Examples -/

/-- U0 : U1 in the empty context. -/
theorem u0_has_type_u1 : PureHasType [] u0 u1 :=
  .u0_type []

/-- The identity function λx.x has type Π(U0, U0).
    The body `.bvar 0` is opened with fresh `fvar x`, yielding `fvar x`,
    which has type U0 in context `[(x, U0)]`. -/
theorem identity_type : PureHasType [] (mkLam (.bvar 0)) (mkPi u0 u0) :=
  .lam_intro [] ∅ u0 (.bvar 0) u0 u1 (.u0_type [])
    (fun x _ => by
      simp only [openBVar, u0]
      exact .fvar [(x, .apply "U0" [])] x (.apply "U0" [])
        List.mem_cons_self PureTmPattern.u0 (by simp [lc_at, lc_at_list]))

/-- First projection λA.λB.A : Π(U0, Π(U0, U0)).
    Takes two type arguments and returns the first. -/
theorem fst_proj_type :
    PureHasType [] (mkLam (mkLam (.bvar 1))) (mkPi u0 (mkPi u0 u0)) := by
  apply PureHasType.lam_intro [] ∅ u0 (mkLam (.bvar 1)) (mkPi u0 u0) u1
    (.u0_type [])
  intro x _
  -- Reduce: openBVar 0 (fvar x) (mkLam (bvar 1)) = mkLam (fvar x)
  --         openBVar 0 (fvar x) (mkPi u0 u0) = mkPi u0 u0
  simp only [openBVar, mkLam, mkPi, u0, List.map]
  apply PureHasType.lam_intro _ ∅
    (.apply "U0" []) (.fvar x) (.apply "U0" []) (.apply "U1" [])
    (.u0_type _)
  intro y _
  simp only [openBVar]
  exact .fvar _ x (.apply "U0" [])
    (List.mem_cons_of_mem _ List.mem_cons_self) PureTmPattern.u0 (by simp [lc_at, lc_at_list])

/-! ## Summary

**0 sorries. 0 axioms.**

Defines:
- `PureConv` — intensional definitional equality (3 β-rules + congruence)
- `PureHasType` — dependent typing judgment (12 rules) with cofinite quantification
- Three concrete typing examples (U0 : U1, identity, first projection)

**Next**: `Reduction.lean` defines `PureReduces` and proves `PureReduces → PureConv`.
-/

end Mettapedia.Languages.MeTTa.Pure.Typing
