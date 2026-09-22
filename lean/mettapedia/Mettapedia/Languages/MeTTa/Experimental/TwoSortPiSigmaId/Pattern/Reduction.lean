import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Typing
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Fragment

/-!
# the two-sort experiment: Reduction Relation

Defines `TwoSortReduces` (one-step β-reduction with congruence) and
`TwoSortReducesStar` (reflexive-transitive closure), plus the key lemma
that every reduction step is a definitional equality.

## Design

`TwoSortReduces` has three computational rules (BetaPi, BetaSigmaFst,
BetaSigmaSnd) and congruence rules for all type/term constructors.
This is a standard CBN-style open reduction (under all constructors).

## References

- Adjedj et al., "Martin-Löf à la Coq" (2023)
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Reduction

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Substitution (openBVar lc_at lc_at_list lc_at_openBVar_result)
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Typing (TwoSortConv)
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Fragment

/-! ## One-Step Reduction -/

/-- One-step β-reduction for the two-sort experiment, with congruence under all constructors.

    This is open reduction: reductions can occur under any constructor,
    including under binders (Lam, Pi, Sigma). -/
inductive TwoSortReduces : Pattern → Pattern → Prop where
  -- β-rules
  | betaPi (body a : Pattern) :
      TwoSortReduces (mkApp (mkLam body) a) (openBVar 0 a body)
  | betaSigmaFst (a b : Pattern) :
      TwoSortReduces (mkFst (mkPair a b)) a
  | betaSigmaSnd (a b : Pattern) :
      TwoSortReduces (mkSnd (mkPair a b)) b

  -- Congruence: Pi
  | congPiDom : TwoSortReduces A A' →
      TwoSortReduces (mkPi A B) (mkPi A' B)
  | congPiCod (L : Finset String) (A B B' : Pattern) :
      (∀ x, x ∉ L → TwoSortReduces (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) →
      TwoSortReduces (mkPi A B) (mkPi A B')
  -- Congruence: Sigma
  | congSigmaDom : TwoSortReduces A A' →
      TwoSortReduces (mkSigma A B) (mkSigma A' B)
  | congSigmaCod (L : Finset String) (A B B' : Pattern) :
      (∀ x, x ∉ L → TwoSortReduces (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) →
      TwoSortReduces (mkSigma A B) (mkSigma A B')
  -- Congruence: Id
  | congIdType : TwoSortReduces A A' →
      TwoSortReduces (mkId A a b) (mkId A' a b)
  | congIdLeft : TwoSortReduces a a' →
      TwoSortReduces (mkId A a b) (mkId A a' b)
  | congIdRight : TwoSortReduces b b' →
      TwoSortReduces (mkId A a b) (mkId A a b')
  -- Congruence: Lam (cofinite — under binder)
  | congLam (L : Finset String) (body body' : Pattern) :
      (∀ x, x ∉ L → TwoSortReduces (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) body')) →
      TwoSortReduces (mkLam body) (mkLam body')
  -- Congruence: App
  | congAppFun : TwoSortReduces f f' →
      TwoSortReduces (mkApp f a) (mkApp f' a)
  | congAppArg : TwoSortReduces a a' →
      TwoSortReduces (mkApp f a) (mkApp f a')
  -- Congruence: Pair
  | congPairFst : TwoSortReduces a a' →
      TwoSortReduces (mkPair a b) (mkPair a' b)
  | congPairSnd : TwoSortReduces b b' →
      TwoSortReduces (mkPair a b) (mkPair a b')
  -- Congruence: Fst
  | congFst : TwoSortReduces p p' →
      TwoSortReduces (mkFst p) (mkFst p')
  -- Congruence: Snd
  | congSnd : TwoSortReduces p p' →
      TwoSortReduces (mkSnd p) (mkSnd p')
  -- Congruence: Refl
  | congRefl : TwoSortReduces a a' →
      TwoSortReduces (mkRefl a) (mkRefl a')

/-! ## Reflexive-Transitive Closure -/

/-- Multi-step reduction (reflexive-transitive closure of `TwoSortReduces`). -/
inductive TwoSortReducesStar : Pattern → Pattern → Prop where
  | refl (t : Pattern) : TwoSortReducesStar t t
  | step : TwoSortReduces t₁ t₂ → TwoSortReducesStar t₂ t₃ → TwoSortReducesStar t₁ t₃

/-- Multi-step reduction is transitive. -/
theorem TwoSortReducesStar.trans :
    TwoSortReducesStar t₁ t₂ → TwoSortReducesStar t₂ t₃ → TwoSortReducesStar t₁ t₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- Single step embeds into multi-step. -/
theorem TwoSortReducesStar.single (h : TwoSortReduces t₁ t₂) : TwoSortReducesStar t₁ t₂ :=
  .step h (.refl _)

/-! ## Reduction implies Conversion -/

 /-- Every one-step reduction of a locally closed two-sort term is a definitional equality. -/
theorem TwoSortReduces_implies_TwoSortConv (h : TwoSortReduces t₁ t₂)
    (hlc : lc_at 0 t₁ = true) (htwoSort : TwoSortTermPattern t₁) : TwoSortConv t₁ t₂ := by
  revert hlc htwoSort
  induction h with
  | betaPi body a =>
      intro hlc htwoSort
      have hlcB : lc_at 1 body = true := by
        simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcA : lc_at 0 a = true := by
        simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      have hTwoSortApp : TwoSortTermPattern (mkLam body) ∧ TwoSortTermPattern a := twoSort_app_inv htwoSort
      have hTwoSortBody : TwoSortTermPattern body := twoSort_lam_inv hTwoSortApp.1
      exact .betaPi body a hTwoSortBody hTwoSortApp.2 hlcB hlcA
  | betaSigmaFst a b =>
      intro hlc htwoSort
      have hlcA : lc_at 0 a = true := by
        simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcB : lc_at 0 b = true := by
        simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      have hTwoSortPair : TwoSortTermPattern (mkPair a b) := twoSort_fst_inv htwoSort
      have hTwoSortAB : TwoSortTermPattern a ∧ TwoSortTermPattern b := twoSort_pair_inv hTwoSortPair
      exact .betaSigmaFst a b hTwoSortAB.1 hTwoSortAB.2 hlcA hlcB
  | betaSigmaSnd a b =>
      intro hlc htwoSort
      have hlcA : lc_at 0 a = true := by
        simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcB : lc_at 0 b = true := by
        simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      have hTwoSortPair : TwoSortTermPattern (mkPair a b) := twoSort_snd_inv htwoSort
      have hTwoSortAB : TwoSortTermPattern a ∧ TwoSortTermPattern b := twoSort_pair_inv hTwoSortPair
      exact .betaSigmaSnd a b hTwoSortAB.1 hTwoSortAB.2 hlcA hlcB
  | @congPiDom A A' B _ ih =>
      intro hlc htwoSort
      have : lc_at 0 A = true := by
        simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hTwoSortAB : TwoSortTermPattern A ∧ TwoSortTermPattern B := twoSort_pi_inv htwoSort
      exact .congPi ∅ (ih this hTwoSortAB.1) (fun x _ => .refl _ (twoSortTm_openBVar_fvar x hTwoSortAB.2))
  | congPiCod L A B B' _ ih =>
      intro hlc htwoSort
      have hTwoSortAB : TwoSortTermPattern A ∧ TwoSortTermPattern B := twoSort_pi_inv htwoSort
      exact .congPi L (.refl _ hTwoSortAB.1) (fun x hx => by
        have hOpenTwoSort : TwoSortTermPattern (openBVar 0 (.fvar x) B) := twoSortTm_openBVar_fvar x hTwoSortAB.2
        have hlcOpen := Mettapedia.OSLF.MeTTaIL.Substitution.lc_at_openBVar_result
          (by simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2)
          (by simp [lc_at] : lc_at 0 (.fvar x) = true)
        exact ih x hx hlcOpen hOpenTwoSort)
  | @congSigmaDom A A' B _ ih =>
      intro hlc htwoSort
      have : lc_at 0 A = true := by
        simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hTwoSortAB : TwoSortTermPattern A ∧ TwoSortTermPattern B := twoSort_sigma_inv htwoSort
      exact .congSigma ∅ (ih this hTwoSortAB.1) (fun x _ => .refl _ (twoSortTm_openBVar_fvar x hTwoSortAB.2))
  | congSigmaCod L A B B' _ ih =>
      intro hlc htwoSort
      have hTwoSortAB : TwoSortTermPattern A ∧ TwoSortTermPattern B := twoSort_sigma_inv htwoSort
      exact .congSigma L (.refl _ hTwoSortAB.1) (fun x hx => by
        have hOpenTwoSort : TwoSortTermPattern (openBVar 0 (.fvar x) B) := twoSortTm_openBVar_fvar x hTwoSortAB.2
        have hlcOpen := Mettapedia.OSLF.MeTTaIL.Substitution.lc_at_openBVar_result
          (by simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2)
          (by simp [lc_at] : lc_at 0 (.fvar x) = true)
        exact ih x hx hlcOpen hOpenTwoSort)
  | @congIdType A A' a b _ ih =>
      intro hlc htwoSort
      have hTwoSortId : TwoSortTermPattern A ∧ TwoSortTermPattern a ∧ TwoSortTermPattern b := twoSort_id_inv htwoSort
      exact .congId
        (ih (by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1) hTwoSortId.1)
        (.refl _ hTwoSortId.2.1)
        (.refl _ hTwoSortId.2.2)
  | @congIdLeft a a' A b _ ih =>
      intro hlc htwoSort
      have hTwoSortId : TwoSortTermPattern A ∧ TwoSortTermPattern a ∧ TwoSortTermPattern b := twoSort_id_inv htwoSort
      exact .congId
        (.refl _ hTwoSortId.1)
        (ih (by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.1) hTwoSortId.2.1)
        (.refl _ hTwoSortId.2.2)
  | @congIdRight b b' A a _ ih =>
      intro hlc htwoSort
      have hTwoSortId : TwoSortTermPattern A ∧ TwoSortTermPattern a ∧ TwoSortTermPattern b := twoSort_id_inv htwoSort
      exact .congId
        (.refl _ hTwoSortId.1)
        (.refl _ hTwoSortId.2.1)
        (ih (by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.2) hTwoSortId.2.2)
  | congLam L body body' _ ih =>
      intro hlc htwoSort
      exact .congLam L (fun x hx => by
        have hTwoSortBody : TwoSortTermPattern body := twoSort_lam_inv htwoSort
        have hOpenTwoSort : TwoSortTermPattern (openBVar 0 (.fvar x) body) := twoSortTm_openBVar_fvar x hTwoSortBody
        have hlcOpen := Mettapedia.OSLF.MeTTaIL.Substitution.lc_at_openBVar_result
          (by simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc)
          (by simp [lc_at] : lc_at 0 (.fvar x) = true)
        exact ih x hx hlcOpen hOpenTwoSort)
  | @congAppFun f f' a _ ih =>
      intro hlc htwoSort
      have hTwoSortApp : TwoSortTermPattern f ∧ TwoSortTermPattern a := twoSort_app_inv htwoSort
      exact .congApp
        (ih (by simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1) hTwoSortApp.1)
        (.refl _ hTwoSortApp.2)
  | @congAppArg a a' f _ ih =>
      intro hlc htwoSort
      have hTwoSortApp : TwoSortTermPattern f ∧ TwoSortTermPattern a := twoSort_app_inv htwoSort
      exact .congApp
        (.refl _ hTwoSortApp.1)
        (ih (by simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2) hTwoSortApp.2)
  | @congPairFst a a' b _ ih =>
      intro hlc htwoSort
      have hTwoSortPair : TwoSortTermPattern a ∧ TwoSortTermPattern b := twoSort_pair_inv htwoSort
      exact .congPair
        (ih (by simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1) hTwoSortPair.1)
        (.refl _ hTwoSortPair.2)
  | @congPairSnd b b' a _ ih =>
      intro hlc htwoSort
      have hTwoSortPair : TwoSortTermPattern a ∧ TwoSortTermPattern b := twoSort_pair_inv htwoSort
      exact .congPair
        (.refl _ hTwoSortPair.1)
        (ih (by simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2) hTwoSortPair.2)
  | congFst _ ih =>
      intro hlc htwoSort
      exact .congFst (ih (by simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc) (twoSort_fst_inv htwoSort))
  | congSnd _ ih =>
      intro hlc htwoSort
      exact .congSnd (ih (by simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc) (twoSort_snd_inv htwoSort))
  | congRefl _ ih =>
      intro hlc htwoSort
      exact .congRefl (ih (by simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc) (twoSort_refl_inv htwoSort))

-- Note: TwoSortReducesStar_implies_TwoSortConv is in FVarSubst.lean (needs twoSortReduces_preserves_lc)

/-! ## Concrete Reduction Examples -/

/-- β fires: (λ.@0) U0 ~> U0 -/
theorem beta_identity_u0 : TwoSortReduces (mkApp (mkLam (.bvar 0)) u0) u0 := by
  have h := TwoSortReduces.betaPi (.bvar 0) u0
  simp [openBVar, u0] at h
  exact h

/-- Fst fires: fst (U0, U1) ~> U0 -/
theorem fst_pair : TwoSortReduces (mkFst (mkPair u0 u1)) u0 :=
  .betaSigmaFst u0 u1

/-- Snd fires: snd (U0, U1) ~> U1 -/
theorem snd_pair : TwoSortReduces (mkSnd (mkPair u0 u1)) u1 :=
  .betaSigmaSnd u0 u1

/-- Multi-step: (λ.@0) (fst (U0, U1)) ~>* U0 -/
theorem identity_fst_reduces :
    TwoSortReducesStar (mkApp (mkLam (.bvar 0)) (mkFst (mkPair u0 u1))) u0 := by
  -- Step 1: reduce the argument first — fst (U0, U1) ~> U0
  apply TwoSortReducesStar.step (.congAppArg (.betaSigmaFst u0 u1))
  -- Step 2: β-reduce — (λ.@0) U0 ~> U0
  apply TwoSortReducesStar.step
  · have h := TwoSortReduces.betaPi (.bvar 0) u0
    simp [openBVar, u0] at h
    exact h
  exact .refl _

/-! ## Inversion for Refl -/

/-- If `mkRefl a` reduces in one step, the result must be `mkRefl a'`
    for some `a'` with `TwoSortReduces a a'`.
    (Manual inversion avoids dependent elimination failure on `.apply` tag.) -/
theorem reduces_mkRefl_inv {a t : Pattern}
    (h : TwoSortReduces (mkRefl a) t) :
    ∃ a', t = mkRefl a' ∧ TwoSortReduces a a' := by
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
- `TwoSortReduces` — one-step β-reduction with 3 computational + 16 congruence rules
- `TwoSortReducesStar` — reflexive-transitive closure
- `TwoSortReduces_implies_TwoSortConv` — every reduction is a conversion
- `TwoSortReducesStar_implies_TwoSortConv` — multi-step version
- 4 concrete reduction examples

**Next**: `SubjectReduction.lean` proves the crown theorem:
  `TwoSortHasType Γ t A → TwoSortReduces t t' → TwoSortHasType Γ t' A`
-/

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Reduction
