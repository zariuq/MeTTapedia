import Mettapedia.OSLF.MeTTaPure.Typing

/-!
# MeTTa-Pure: Reduction Relation

Defines `PureReduces` (one-step β-reduction with congruence) and
`PureReducesStar` (reflexive-transitive closure), plus the key lemma
that every reduction step is a definitional equality.

## Design

`PureReduces` has three computational rules (BetaPi, BetaSigmaFst,
BetaSigmaSnd) and congruence rules for all type/term constructors.
This is a standard CBN-style open reduction (under all constructors).

## References

- Adjedj et al., "Martin-Löf à la Coq" (2023)
-/

namespace Mettapedia.OSLF.MeTTaPure.Reduction

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Substitution (openBVar)
open Mettapedia.OSLF.MeTTaPure.Core
open Mettapedia.OSLF.MeTTaPure.Typing (PureConv)

/-! ## One-Step Reduction -/

/-- One-step β-reduction for MeTTa-Pure, with congruence under all constructors.

    This is open reduction: reductions can occur under any constructor,
    including under binders (Lam, Pi, Sigma). -/
inductive PureReduces : Pattern → Pattern → Prop where
  -- β-rules
  | betaPi (body a : Pattern) :
      PureReduces (mkApp (mkLam body) a) (openBVar 0 a body)
  | betaSigmaFst (a b : Pattern) :
      PureReduces (mkFst (mkPair a b)) a
  | betaSigmaSnd (a b : Pattern) :
      PureReduces (mkSnd (mkPair a b)) b

  -- Congruence: Pi
  | congPiDom : PureReduces A A' →
      PureReduces (mkPi A B) (mkPi A' B)
  | congPiCod (L : Finset String) (A B B' : Pattern) :
      (∀ x, x ∉ L → PureReduces (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) →
      PureReduces (mkPi A B) (mkPi A B')
  -- Congruence: Sigma
  | congSigmaDom : PureReduces A A' →
      PureReduces (mkSigma A B) (mkSigma A' B)
  | congSigmaCod (L : Finset String) (A B B' : Pattern) :
      (∀ x, x ∉ L → PureReduces (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) →
      PureReduces (mkSigma A B) (mkSigma A B')
  -- Congruence: Id
  | congIdType : PureReduces A A' →
      PureReduces (mkId A a b) (mkId A' a b)
  | congIdLeft : PureReduces a a' →
      PureReduces (mkId A a b) (mkId A a' b)
  | congIdRight : PureReduces b b' →
      PureReduces (mkId A a b) (mkId A a b')
  -- Congruence: Lam (cofinite — under binder)
  | congLam (L : Finset String) (body body' : Pattern) :
      (∀ x, x ∉ L → PureReduces (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) body')) →
      PureReduces (mkLam body) (mkLam body')
  -- Congruence: App
  | congAppFun : PureReduces f f' →
      PureReduces (mkApp f a) (mkApp f' a)
  | congAppArg : PureReduces a a' →
      PureReduces (mkApp f a) (mkApp f a')
  -- Congruence: Pair
  | congPairFst : PureReduces a a' →
      PureReduces (mkPair a b) (mkPair a' b)
  | congPairSnd : PureReduces b b' →
      PureReduces (mkPair a b) (mkPair a b')
  -- Congruence: Fst
  | congFst : PureReduces p p' →
      PureReduces (mkFst p) (mkFst p')
  -- Congruence: Snd
  | congSnd : PureReduces p p' →
      PureReduces (mkSnd p) (mkSnd p')
  -- Congruence: Refl
  | congRefl : PureReduces a a' →
      PureReduces (mkRefl a) (mkRefl a')

/-! ## Reflexive-Transitive Closure -/

/-- Multi-step reduction (reflexive-transitive closure of `PureReduces`). -/
inductive PureReducesStar : Pattern → Pattern → Prop where
  | refl (t : Pattern) : PureReducesStar t t
  | step : PureReduces t₁ t₂ → PureReducesStar t₂ t₃ → PureReducesStar t₁ t₃

/-- Multi-step reduction is transitive. -/
theorem PureReducesStar.trans :
    PureReducesStar t₁ t₂ → PureReducesStar t₂ t₃ → PureReducesStar t₁ t₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- Single step embeds into multi-step. -/
theorem PureReducesStar.single (h : PureReduces t₁ t₂) : PureReducesStar t₁ t₂ :=
  .step h (.refl _)

/-! ## Reduction implies Conversion -/

/-- Every one-step reduction is a definitional equality. -/
theorem PureReduces_implies_PureConv (h : PureReduces t₁ t₂) : PureConv t₁ t₂ := by
  induction h with
  | betaPi body a => exact .betaPi body a
  | betaSigmaFst a b => exact .betaSigmaFst a b
  | betaSigmaSnd a b => exact .betaSigmaSnd a b
  | congPiDom _ ih => exact .congPi ∅ ih (fun _ _ => .refl _)
  | congPiCod L _ _ _ _ ih => exact .congPi L (.refl _) (fun x hx => ih x hx)
  | congSigmaDom _ ih => exact .congSigma ∅ ih (fun _ _ => .refl _)
  | congSigmaCod L _ _ _ _ ih => exact .congSigma L (.refl _) (fun x hx => ih x hx)
  | congIdType _ ih => exact .congId ih (.refl _) (.refl _)
  | congIdLeft _ ih => exact .congId (.refl _) ih (.refl _)
  | congIdRight _ ih => exact .congId (.refl _) (.refl _) ih
  | congLam L _ _ _ ih => exact .congLam L (fun x hx => ih x hx)
  | congAppFun _ ih => exact .congApp ih (.refl _)
  | congAppArg _ ih => exact .congApp (.refl _) ih
  | congPairFst _ ih => exact .congPair ih (.refl _)
  | congPairSnd _ ih => exact .congPair (.refl _) ih
  | congFst _ ih => exact .congFst ih
  | congSnd _ ih => exact .congSnd ih
  | congRefl _ ih => exact .congRefl ih

/-- Multi-step reduction implies conversion. -/
theorem PureReducesStar_implies_PureConv (h : PureReducesStar t₁ t₂) :
    PureConv t₁ t₂ := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .trans (PureReduces_implies_PureConv hs) ih

/-! ## Concrete Reduction Examples -/

/-- β fires: (λ.@0) U0 ~> U0 -/
theorem beta_identity_u0 : PureReduces (mkApp (mkLam (.bvar 0)) u0) u0 := by
  have h := PureReduces.betaPi (.bvar 0) u0
  simp [openBVar, u0] at h
  exact h

/-- Fst fires: fst (U0, U1) ~> U0 -/
theorem fst_pair : PureReduces (mkFst (mkPair u0 u1)) u0 :=
  .betaSigmaFst u0 u1

/-- Snd fires: snd (U0, U1) ~> U1 -/
theorem snd_pair : PureReduces (mkSnd (mkPair u0 u1)) u1 :=
  .betaSigmaSnd u0 u1

/-- Multi-step: (λ.@0) (fst (U0, U1)) ~>* U0 -/
theorem identity_fst_reduces :
    PureReducesStar (mkApp (mkLam (.bvar 0)) (mkFst (mkPair u0 u1))) u0 := by
  -- Step 1: reduce the argument first — fst (U0, U1) ~> U0
  apply PureReducesStar.step (.congAppArg (.betaSigmaFst u0 u1))
  -- Step 2: β-reduce — (λ.@0) U0 ~> U0
  apply PureReducesStar.step
  · have h := PureReduces.betaPi (.bvar 0) u0
    simp [openBVar, u0] at h
    exact h
  exact .refl _

/-! ## Inversion for Refl -/

/-- If `mkRefl a` reduces in one step, the result must be `mkRefl a'`
    for some `a'` with `PureReduces a a'`.
    (Manual inversion avoids dependent elimination failure on `.apply` tag.) -/
theorem reduces_mkRefl_inv {a t : Pattern}
    (h : PureReduces (mkRefl a) t) :
    ∃ a', t = mkRefl a' ∧ PureReduces a a' := by
  generalize heq : mkRefl a = s at h
  cases h with
  | betaPi body arg => simp [mkRefl, mkApp] at heq
  | betaSigmaFst x y => simp [mkRefl, mkFst] at heq
  | betaSigmaSnd x y => simp [mkRefl, mkSnd] at heq
  | congPiDom hA => simp [mkRefl, mkPi] at heq
  | congPiCod L _ Bc Bc' hBc => simp [mkRefl, mkPi] at heq
  | congSigmaDom hA => simp [mkRefl, mkSigma] at heq
  | congSigmaCod L _ Bc Bc' hBc => simp [mkRefl, mkSigma] at heq
  | congIdType hA => simp [mkRefl, mkId] at heq
  | congIdLeft ha => simp [mkRefl, mkId] at heq
  | congIdRight hb => simp [mkRefl, mkId] at heq
  | congLam L body body' hB => simp [mkRefl, mkLam] at heq
  | congAppFun hf => simp [mkRefl, mkApp] at heq
  | congAppArg ha => simp [mkRefl, mkApp] at heq
  | congPairFst ha => simp [mkRefl, mkPair] at heq
  | congPairSnd hb => simp [mkRefl, mkPair] at heq
  | congFst hp => simp [mkRefl, mkFst] at heq
  | congSnd hp => simp [mkRefl, mkSnd] at heq
  | congRefl ha =>
      simp [mkRefl] at heq; obtain ⟨rfl⟩ := heq
      exact ⟨_, rfl, ha⟩

/-! ## Summary

**0 sorries. 0 axioms.**

Defines:
- `PureReduces` — one-step β-reduction with 3 computational + 16 congruence rules
- `PureReducesStar` — reflexive-transitive closure
- `PureReduces_implies_PureConv` — every reduction is a conversion
- `PureReducesStar_implies_PureConv` — multi-step version
- 4 concrete reduction examples

**Next**: `SubjectReduction.lean` proves the crown theorem:
  `PureHasType Γ t A → PureReduces t t' → PureHasType Γ t' A`
-/

end Mettapedia.OSLF.MeTTaPure.Reduction
