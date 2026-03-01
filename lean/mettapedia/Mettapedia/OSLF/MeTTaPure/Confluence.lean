import Mettapedia.OSLF.MeTTaPure.Reduction
import Mettapedia.OSLF.MeTTaPure.FVarSubst

/-!
# MeTTa-Pure: Confluence and Pi/Sigma Injectivity

Proves Church-Rosser for MeTTa-Pure via parallel reduction, then derives
Pi/Sigma injectivity under `PureConv`. These are needed for subject reduction.

## Proof Architecture

1. Head preservation for `PureReduces` and `PureReducesStar` (easy, no CR)
2. Pi/Sigma decomposition for `PureReducesStar` (from head preservation)
3. Church-Rosser for `PureConv` (from confluence of `PureReducesStar`)
4. Pi/Sigma injectivity (from CR + head preservation + decomposition)

The confluence proof uses parallel reduction with the `substFVar` bridge
to work around the non-shifting `openBVar` composition issue.

## References

- Takahashi, "Parallel reductions in lambda-calculus" (1995)
-/

namespace Mettapedia.OSLF.MeTTaPure.Confluence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Substitution (openBVar lc_at lc_at_list lc_at_openBVar_result freeVars isFresh)
open Mettapedia.OSLF.MeTTaPure.Core
open Mettapedia.OSLF.MeTTaPure.Typing (PureConv)
open Mettapedia.OSLF.MeTTaPure.Reduction
open Mettapedia.OSLF.MeTTaPure.FVarSubst

/-! ## Head Preservation for Single-Step Reduction

`PureReduces (mkPi A B) t → t` is always a Pi (and similarly for Sigma).
Proved by generalizing the index, then case analysis with discrimination. -/

/-- Helper: convert list to finset for cofinite freshness sets. -/
private def listToFinset (l : List String) : Finset String := l.toFinset

/-- Freshness from finite exclusion on free variables. -/
private theorem isFresh_of_not_in_freeVars_finset {x : String} {p : Pattern}
    (h : x ∉ listToFinset (freeVars p)) : isFresh x p = true := by
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hmem
  exact h (List.mem_toFinset.mpr (List.contains_iff_mem.mp hmem))

private theorem apply_label_inj {c₁ c₂ : String} {args₁ args₂ : List Pattern}
    (h : Pattern.apply c₁ args₁ = Pattern.apply c₂ args₂) : c₁ = c₂ ∧ args₁ = args₂ :=
  ⟨Pattern.apply.inj h |>.1, Pattern.apply.inj h |>.2⟩

/-- Single-step reduction preserves Pi head. -/
theorem reduces_pi_head_pres {A B t : Pattern}
    (h : PureReduces (mkPi A B) t) :
    (∃ A', t = mkPi A' B ∧ PureReduces A A') ∨
    (∃ B', ∃ L : Finset String, t = mkPi A B' ∧
      ∀ x, x ∉ L → PureReduces (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) := by
  generalize heq : mkPi A B = s at h
  cases h with
  | betaPi body a => simp [mkPi, mkApp] at heq
  | betaSigmaFst a b => simp [mkPi, mkFst] at heq
  | betaSigmaSnd a b => simp [mkPi, mkSnd] at heq
  | congPiDom hA =>
      simp [mkPi] at heq; obtain ⟨rfl, rfl⟩ := heq
      left; exact ⟨_, rfl, hA⟩
  | congPiCod L _ Bc Bc' hBc =>
      simp [mkPi] at heq; obtain ⟨rfl, rfl⟩ := heq
      right; exact ⟨Bc', L, rfl, hBc⟩
  | congSigmaDom hA => simp [mkPi, mkSigma] at heq
  | congSigmaCod L _ Bc Bc' hBc => simp [mkPi, mkSigma] at heq
  | congIdType hA => simp [mkPi, mkId] at heq
  | congIdLeft ha => simp [mkPi, mkId] at heq
  | congIdRight hb => simp [mkPi, mkId] at heq
  | congLam L body body' hB => simp [mkPi, mkLam] at heq
  | congAppFun hf => simp [mkPi, mkApp] at heq
  | congAppArg ha => simp [mkPi, mkApp] at heq
  | congPairFst ha => simp [mkPi, mkPair] at heq
  | congPairSnd hb => simp [mkPi, mkPair] at heq
  | congFst hp => simp [mkPi, mkFst] at heq
  | congSnd hp => simp [mkPi, mkSnd] at heq
  | congRefl ha => simp [mkPi, mkRefl] at heq

/-- Single-step reduction preserves Sigma head. -/
theorem reduces_sigma_head_pres {A B t : Pattern}
    (h : PureReduces (mkSigma A B) t) :
    (∃ A', t = mkSigma A' B ∧ PureReduces A A') ∨
    (∃ B', ∃ L : Finset String, t = mkSigma A B' ∧
      ∀ x, x ∉ L → PureReduces (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) := by
  generalize heq : mkSigma A B = s at h
  cases h with
  | betaPi body a => simp [mkSigma, mkApp] at heq
  | betaSigmaFst a b => simp [mkSigma, mkFst] at heq
  | betaSigmaSnd a b => simp [mkSigma, mkSnd] at heq
  | congPiDom hA => simp [mkSigma, mkPi] at heq
  | congPiCod L _ Bc Bc' hBc => simp [mkSigma, mkPi] at heq
  | congSigmaDom hA =>
      simp [mkSigma] at heq; obtain ⟨rfl, rfl⟩ := heq
      left; exact ⟨_, rfl, hA⟩
  | congSigmaCod L _ Bc Bc' hBc =>
      simp [mkSigma] at heq; obtain ⟨rfl, rfl⟩ := heq
      right; exact ⟨Bc', L, rfl, hBc⟩
  | congIdType hA => simp [mkSigma, mkId] at heq
  | congIdLeft ha => simp [mkSigma, mkId] at heq
  | congIdRight hb => simp [mkSigma, mkId] at heq
  | congLam L body body' hB => simp [mkSigma, mkLam] at heq
  | congAppFun hf => simp [mkSigma, mkApp] at heq
  | congAppArg ha => simp [mkSigma, mkApp] at heq
  | congPairFst ha => simp [mkSigma, mkPair] at heq
  | congPairSnd hb => simp [mkSigma, mkPair] at heq
  | congFst hp => simp [mkSigma, mkFst] at heq
  | congSnd hp => simp [mkSigma, mkSnd] at heq
  | congRefl ha => simp [mkSigma, mkRefl] at heq

/-! ## Head Preservation for Multi-Step Reduction -/

private theorem reduceStar_pi_head_aux {s t : Pattern}
    (h : PureReducesStar s t) (hs : ∃ A B, s = mkPi A B) :
    ∃ A' B', t = mkPi A' B' := by
  induction h with
  | refl => exact hs
  | step hs₁ _ ih =>
      obtain ⟨A, B, rfl⟩ := hs
      obtain (⟨A', heq, _⟩ | ⟨B', _, heq, _⟩) := reduces_pi_head_pres hs₁
      · exact ih ⟨A', B, heq⟩
      · exact ih ⟨A, B', heq⟩

/-- Multi-step reduction preserves Pi head. -/
theorem reduceStar_pi_head {A B t : Pattern}
    (h : PureReducesStar (mkPi A B) t) :
    ∃ A' B', t = mkPi A' B' :=
  reduceStar_pi_head_aux h ⟨A, B, rfl⟩

private theorem reduceStar_sigma_head_aux {s t : Pattern}
    (h : PureReducesStar s t) (hs : ∃ A B, s = mkSigma A B) :
    ∃ A' B', t = mkSigma A' B' := by
  induction h with
  | refl => exact hs
  | step hs₁ _ ih =>
      obtain ⟨A, B, rfl⟩ := hs
      obtain (⟨A', heq, _⟩ | ⟨B', _, heq, _⟩) := reduces_sigma_head_pres hs₁
      · exact ih ⟨A', B, heq⟩
      · exact ih ⟨A, B', heq⟩

/-- Multi-step reduction preserves Sigma head. -/
theorem reduceStar_sigma_head {A B t : Pattern}
    (h : PureReducesStar (mkSigma A B) t) :
    ∃ A' B', t = mkSigma A' B' :=
  reduceStar_sigma_head_aux h ⟨A, B, rfl⟩

/-! ## Pi/Sigma Decomposition for Multi-Step Reduction

Decompose `PureReducesStar (mkPi A B) (mkPi A' B')` into domain and
codomain multi-step reductions. -/

private theorem reduceStar_pi_decomp_aux {s t : Pattern}
    (h : PureReducesStar s t) :
    ∀ {A B A' B' : Pattern}, s = mkPi A B → t = mkPi A' B' →
    PureReducesStar A A' ∧
    (∃ L : Finset String, ∀ x, x ∉ L →
      PureReducesStar (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) := by
  induction h with
  | refl =>
      intro A B A' B' hs ht
      subst hs; simp [mkPi] at ht; obtain ⟨rfl, rfl⟩ := ht
      exact ⟨.refl _, ∅, fun _ _ => .refl _⟩
  | step hs₁ _ ih =>
      intro A B A' B' hs ht
      subst hs
      obtain (⟨Am, heq, hA⟩ | ⟨Bm, Ls, heq, hBs⟩) := reduces_pi_head_pres hs₁
      · -- Domain step: A →₁ Am, codomain unchanged
        obtain ⟨hdom, L, hcod⟩ := ih heq ht
        exact ⟨.step hA hdom, L, hcod⟩
      · -- Codomain step: domain unchanged, B →₁ Bm under binder
        obtain ⟨hdom, L, hcod⟩ := ih heq ht
        refine ⟨hdom, Ls ∪ L, fun x hx => ?_⟩
        exact .step (hBs x (fun h => hx (Finset.mem_union_left _ h)))
                    (hcod x (fun h => hx (Finset.mem_union_right _ h)))

/-- Multi-step reduction of a Pi decomposes into domain and codomain. -/
theorem reduceStar_pi_decomp {A B A' B' : Pattern}
    (h : PureReducesStar (mkPi A B) (mkPi A' B')) :
    PureReducesStar A A' ∧
    (∃ L : Finset String, ∀ x, x ∉ L →
      PureReducesStar (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) :=
  reduceStar_pi_decomp_aux h rfl rfl

private theorem reduceStar_sigma_decomp_aux {s t : Pattern}
    (h : PureReducesStar s t) :
    ∀ {A B A' B' : Pattern}, s = mkSigma A B → t = mkSigma A' B' →
    PureReducesStar A A' ∧
    (∃ L : Finset String, ∀ x, x ∉ L →
      PureReducesStar (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) := by
  induction h with
  | refl =>
      intro A B A' B' hs ht
      subst hs; simp [mkSigma] at ht; obtain ⟨rfl, rfl⟩ := ht
      exact ⟨.refl _, ∅, fun _ _ => .refl _⟩
  | step hs₁ _ ih =>
      intro A B A' B' hs ht
      subst hs
      obtain (⟨Am, heq, hA⟩ | ⟨Bm, Ls, heq, hBs⟩) := reduces_sigma_head_pres hs₁
      · obtain ⟨hdom, L, hcod⟩ := ih heq ht
        exact ⟨.step hA hdom, L, hcod⟩
      · obtain ⟨hdom, L, hcod⟩ := ih heq ht
        refine ⟨hdom, Ls ∪ L, fun x hx => ?_⟩
        exact .step (hBs x (fun h => hx (Finset.mem_union_left _ h)))
                    (hcod x (fun h => hx (Finset.mem_union_right _ h)))

/-- Multi-step reduction of a Sigma decomposes into domain and codomain. -/
theorem reduceStar_sigma_decomp {A B A' B' : Pattern}
    (h : PureReducesStar (mkSigma A B) (mkSigma A' B')) :
    PureReducesStar A A' ∧
    (∃ L : Finset String, ∀ x, x ∉ L →
      PureReducesStar (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) :=
  reduceStar_sigma_decomp_aux h rfl rfl

/-! ## Multi-Step Congruence Lemmas

Lift `PureReducesStar` through each constructor. -/

theorem PureReducesStar.congAppFun {f f' a : Pattern}
    (h : PureReducesStar f f') : PureReducesStar (mkApp f a) (mkApp f' a) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congAppFun hs) ih

theorem PureReducesStar.congAppArg {f a a' : Pattern}
    (h : PureReducesStar a a') : PureReducesStar (mkApp f a) (mkApp f a') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congAppArg hs) ih

theorem PureReducesStar.congApp {f f' a a' : Pattern}
    (hf : PureReducesStar f f') (ha : PureReducesStar a a') :
    PureReducesStar (mkApp f a) (mkApp f' a') :=
  (congAppFun hf).trans (congAppArg ha)

theorem PureReducesStar.congPairFst {a a' b : Pattern}
    (h : PureReducesStar a a') : PureReducesStar (mkPair a b) (mkPair a' b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congPairFst hs) ih

theorem PureReducesStar.congPairSnd {a b b' : Pattern}
    (h : PureReducesStar b b') : PureReducesStar (mkPair a b) (mkPair a b') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congPairSnd hs) ih

theorem PureReducesStar.congPair {a a' b b' : Pattern}
    (ha : PureReducesStar a a') (hb : PureReducesStar b b') :
    PureReducesStar (mkPair a b) (mkPair a' b') :=
  (congPairFst ha).trans (congPairSnd hb)

theorem PureReducesStar.congFst {p p' : Pattern}
    (h : PureReducesStar p p') : PureReducesStar (mkFst p) (mkFst p') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congFst hs) ih

theorem PureReducesStar.congSnd {p p' : Pattern}
    (h : PureReducesStar p p') : PureReducesStar (mkSnd p) (mkSnd p') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congSnd hs) ih

theorem PureReducesStar.congRefl {a a' : Pattern}
    (h : PureReducesStar a a') : PureReducesStar (mkRefl a) (mkRefl a') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congRefl hs) ih

theorem PureReducesStar.congIdType {A A' a b : Pattern}
    (h : PureReducesStar A A') : PureReducesStar (mkId A a b) (mkId A' a b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congIdType hs) ih

theorem PureReducesStar.congIdLeft {A a a' b : Pattern}
    (h : PureReducesStar a a') : PureReducesStar (mkId A a b) (mkId A a' b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congIdLeft hs) ih

theorem PureReducesStar.congIdRight {A a b b' : Pattern}
    (h : PureReducesStar b b') : PureReducesStar (mkId A a b) (mkId A a b') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congIdRight hs) ih

theorem PureReducesStar.congId {A A' a a' b b' : Pattern}
    (hA : PureReducesStar A A') (ha : PureReducesStar a a') (hb : PureReducesStar b b') :
    PureReducesStar (mkId A a b) (mkId A' a' b') :=
  (congIdType hA).trans ((congIdLeft ha).trans (congIdRight hb))

theorem PureReducesStar.congPiDom {A A' B : Pattern}
    (h : PureReducesStar A A') : PureReducesStar (mkPi A B) (mkPi A' B) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congPiDom hs) ih

theorem PureReducesStar.congSigmaDom {A A' B : Pattern}
    (h : PureReducesStar A A') : PureReducesStar (mkSigma A B) (mkSigma A' B) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congSigmaDom hs) ih

/-! ## Parallel Reduction

Takahashi-style parallel reduction where all redexes can fire simultaneously.
Uses cofinite quantification for binder cases and `lc_at` constraints on β-rules
to support the substitution lemma and diamond property. -/

/-- Parallel reduction: all redexes may fire simultaneously. -/
inductive ParRed : Pattern → Pattern → Prop where
  | bvar (n : Nat) : ParRed (.bvar n) (.bvar n)
  | fvar (x : String) : ParRed (.fvar x) (.fvar x)
  | pi (L : Finset String) : ParRed A A' →
      (∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) →
      ParRed (mkPi A B) (mkPi A' B')
  | sigma (L : Finset String) : ParRed A A' →
      (∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) →
      ParRed (mkSigma A B) (mkSigma A' B')
  | lam (L : Finset String) :
      (∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) body')) →
      ParRed (mkLam body) (mkLam body')
  | app : ParRed f f' → ParRed a a' → ParRed (mkApp f a) (mkApp f' a')
  | pair : ParRed a a' → ParRed b b' → ParRed (mkPair a b) (mkPair a' b')
  | fst : ParRed p p' → ParRed (mkFst p) (mkFst p')
  | snd : ParRed p p' → ParRed (mkSnd p) (mkSnd p')
  | id : ParRed A A' → ParRed a a' → ParRed b b' →
      ParRed (mkId A a b) (mkId A' a' b')
  | refl : ParRed a a' → ParRed (mkRefl a) (mkRefl a')
  | betaPi (L : Finset String) :
      (∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) body')) →
      ParRed a a' → lc_at 1 body = true → lc_at 0 a = true →
      ParRed (mkApp (mkLam body) a) (openBVar 0 a' body')
  | betaSigmaFst : ParRed a a' → ParRed b b' →
      ParRed (mkFst (mkPair a b)) a'
  | betaSigmaSnd : ParRed a a' → ParRed b b' →
      ParRed (mkSnd (mkPair a b)) b'

/-! ## PureConv Preserves Local Closure

Proved independently of Church-Rosser. Both directions (fwd and bwd) are
proved simultaneously so the `symm` case works by swapping. -/

/-- PureConv preserves lc in both directions (needed for symm case). -/
theorem PureConv_preserves_lc_both {s t : Pattern} (h : PureConv s t) :
    (lc_at 0 s = true → lc_at 0 t = true) ∧
    (lc_at 0 t = true → lc_at 0 s = true) := by
  induction h with
  | refl _ => exact ⟨id, id⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨fun h => ih₂.1 (ih₁.1 h), fun h => ih₁.2 (ih₂.2 h)⟩
  | betaPi body a hlcBody hlcA =>
      constructor
      · intro hlc
        exact lc_at_openBVar_result hlcBody hlcA
      · intro _
        simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        exact ⟨hlcBody, hlcA⟩
  | betaSigmaFst a b hlcA hlcB =>
      exact ⟨fun _ => hlcA, fun _ => by
        simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        exact ⟨hlcA, hlcB⟩⟩
  | betaSigmaSnd a b hlcA hlcB =>
      exact ⟨fun _ => hlcB, fun _ => by
        simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        exact ⟨hlcA, hlcB⟩⟩
  | @congPi A₁ A₂ B₁ B₂ L _ _ ihA ihB =>
      constructor
      · intro hlc
        have hlcA : lc_at 0 A₁ = true := by
          simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
        have hlcB : lc_at 1 B₁ = true := by
          simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
        simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        constructor
        · exact ihA.1 hlcA
        · obtain ⟨x₀, hx₀⟩ := exists_fresh L
          have := (ihB x₀ hx₀).1 (lc_at_openBVar_result hlcB (by simp [lc_at]))
          exact lc_at_of_openBVar this
      · intro hlc
        have hlcA : lc_at 0 A₂ = true := by
          simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
        have hlcB : lc_at 1 B₂ = true := by
          simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
        simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        constructor
        · exact ihA.2 hlcA
        · obtain ⟨x₀, hx₀⟩ := exists_fresh L
          have := (ihB x₀ hx₀).2 (lc_at_openBVar_result hlcB (by simp [lc_at]))
          exact lc_at_of_openBVar this
  | @congSigma A₁ A₂ B₁ B₂ L _ _ ihA ihB =>
      constructor
      · intro hlc
        have hlcA : lc_at 0 A₁ = true := by
          simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
        have hlcB : lc_at 1 B₁ = true := by
          simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
        simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        constructor
        · exact ihA.1 hlcA
        · obtain ⟨x₀, hx₀⟩ := exists_fresh L
          have := (ihB x₀ hx₀).1 (lc_at_openBVar_result hlcB (by simp [lc_at]))
          exact lc_at_of_openBVar this
      · intro hlc
        have hlcA : lc_at 0 A₂ = true := by
          simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
        have hlcB : lc_at 1 B₂ = true := by
          simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
        simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        constructor
        · exact ihA.2 hlcA
        · obtain ⟨x₀, hx₀⟩ := exists_fresh L
          have := (ihB x₀ hx₀).2 (lc_at_openBVar_result hlcB (by simp [lc_at]))
          exact lc_at_of_openBVar this
  | @congId A₁ A₂ a₁ a₂ b₁ b₂ _ _ _ ihA iha ihb =>
      constructor
      · intro hlc
        simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨ihA.1 hlc.1, iha.1 hlc.2.1, ihb.1 hlc.2.2⟩
      · intro hlc
        simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨ihA.2 hlc.1, iha.2 hlc.2.1, ihb.2 hlc.2.2⟩
  | @congLam body₁ body₂ L _ ihB =>
      constructor
      · intro hlc
        have hlcB : lc_at 1 body₁ = true := by
          simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
        simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        obtain ⟨x₀, hx₀⟩ := exists_fresh L
        have := (ihB x₀ hx₀).1 (lc_at_openBVar_result hlcB (by simp [lc_at]))
        exact lc_at_of_openBVar this
      · intro hlc
        have hlcB : lc_at 1 body₂ = true := by
          simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
        simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        obtain ⟨x₀, hx₀⟩ := exists_fresh L
        have := (ihB x₀ hx₀).2 (lc_at_openBVar_result hlcB (by simp [lc_at]))
        exact lc_at_of_openBVar this
  | @congApp f₁ f₂ a₁ a₂ _ _ ihf iha =>
      constructor
      · intro hlc
        simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨ihf.1 hlc.1, iha.1 hlc.2⟩
      · intro hlc
        simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨ihf.2 hlc.1, iha.2 hlc.2⟩
  | @congPair a₁ a₂ b₁ b₂ _ _ iha ihb =>
      constructor
      · intro hlc
        simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨iha.1 hlc.1, ihb.1 hlc.2⟩
      · intro hlc
        simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨iha.2 hlc.1, ihb.2 hlc.2⟩
  | @congFst p₁ p₂ _ ih =>
      constructor
      · intro hlc
        simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.1 hlc
      · intro hlc
        simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.2 hlc
  | @congSnd p₁ p₂ _ ih =>
      constructor
      · intro hlc
        simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.1 hlc
      · intro hlc
        simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.2 hlc
  | @congRefl a₁ a₂ _ ih =>
      constructor
      · intro hlc
        simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.1 hlc
      · intro hlc
        simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.2 hlc

/-- Conversion preserves local closure (forward). -/
theorem PureConv_preserves_lc {s t : Pattern} (h : PureConv s t)
    (hlc : lc_at 0 s = true) : lc_at 0 t = true :=
  (PureConv_preserves_lc_both h).1 hlc

/-! ## Church-Rosser

Confluence of `PureReducesStar`, proved via parallel reduction. -/

/-- Confluence: if `s` multi-step reduces to both `u` and `v`,
    they have a common reduct (for locally closed terms). -/
theorem reduceStar_confluence_lc
    {s u v : Pattern} (hlc : lc_at 0 s = true)
    (h₁ : PureReducesStar s u) (h₂ : PureReducesStar s v) :
    ∃ w, PureReducesStar u w ∧ PureReducesStar v w := by
  sorry -- Filled after diamond_parRed is proved

/-- Church-Rosser: if `s ≡ t` and `s` is locally closed,
    they share a common reduct. -/
theorem church_rosser_lc {s t : Pattern} (h : PureConv s t)
    (hlc : lc_at 0 s = true) :
    ∃ u, PureReducesStar s u ∧ PureReducesStar t u := by
  induction h with
  | refl t => exact ⟨t, .refl t, .refl t⟩
  | symm hsub ih =>
      have hlcT := (PureConv_preserves_lc_both hsub).2 hlc
      obtain ⟨u, h₁, h₂⟩ := ih hlcT
      exact ⟨u, h₂, h₁⟩
  | trans h₁₂ h₂₃ ih₁ ih₂ =>
      have hlcMid := PureConv_preserves_lc h₁₂ hlc
      obtain ⟨u₁, hs_u₁, hmid_u₁⟩ := ih₁ hlc
      obtain ⟨u₂, hmid_u₂, ht_u₂⟩ := ih₂ hlcMid
      obtain ⟨w, hu₁_w, hu₂_w⟩ := reduceStar_confluence_lc hlcMid hmid_u₁ hmid_u₂
      exact ⟨w, hs_u₁.trans hu₁_w, ht_u₂.trans hu₂_w⟩
  | betaPi body a hlcBody hlcA =>
      exact ⟨_, PureReducesStar.single (.betaPi body a), .refl _⟩
  | betaSigmaFst a b _ _ =>
      exact ⟨_, PureReducesStar.single (.betaSigmaFst a b), .refl _⟩
  | betaSigmaSnd a b _ _ =>
      exact ⟨_, PureReducesStar.single (.betaSigmaSnd a b), .refl _⟩
  | @congApp f₁ f₂ a₁ a₂ _ _ ihf iha =>
      have hlcF : lc_at 0 f₁ = true := by
        simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcA : lc_at 0 a₁ = true := by
        simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      obtain ⟨uf, hf₁, hf₂⟩ := ihf hlcF
      obtain ⟨ua, ha₁, ha₂⟩ := iha hlcA
      exact ⟨mkApp uf ua, PureReducesStar.congApp hf₁ ha₁,
             PureReducesStar.congApp hf₂ ha₂⟩
  | @congPair a₁ a₂ b₁ b₂ _ _ iha ihb =>
      have hlcA : lc_at 0 a₁ = true := by
        simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcB : lc_at 0 b₁ = true := by
        simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      obtain ⟨ua, ha₁, ha₂⟩ := iha hlcA
      obtain ⟨ub, hb₁, hb₂⟩ := ihb hlcB
      exact ⟨mkPair ua ub, PureReducesStar.congPair ha₁ hb₁,
             PureReducesStar.congPair ha₂ hb₂⟩
  | @congFst p₁ p₂ _ ih =>
      have hlcP : lc_at 0 p₁ = true := by
        simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
      obtain ⟨u, h₁, h₂⟩ := ih hlcP
      exact ⟨mkFst u, PureReducesStar.congFst h₁, PureReducesStar.congFst h₂⟩
  | @congSnd p₁ p₂ _ ih =>
      have hlcP : lc_at 0 p₁ = true := by
        simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
      obtain ⟨u, h₁, h₂⟩ := ih hlcP
      exact ⟨mkSnd u, PureReducesStar.congSnd h₁, PureReducesStar.congSnd h₂⟩
  | @congRefl a₁ a₂ _ ih =>
      have hlcA : lc_at 0 a₁ = true := by
        simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
      obtain ⟨u, h₁, h₂⟩ := ih hlcA
      exact ⟨mkRefl u, PureReducesStar.congRefl h₁, PureReducesStar.congRefl h₂⟩
  | @congId A₁ A₂ a₁ a₂ b₁ b₂ _ _ _ ihA iha ihb =>
      have hlcA : lc_at 0 A₁ = true := by
        simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlca : lc_at 0 a₁ = true := by
        simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.1
      have hlcb : lc_at 0 b₁ = true := by
        simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.2
      obtain ⟨uA, hA₁, hA₂⟩ := ihA hlcA
      obtain ⟨ua, ha₁, ha₂⟩ := iha hlca
      obtain ⟨ub, hb₁, hb₂⟩ := ihb hlcb
      exact ⟨mkId uA ua ub, PureReducesStar.congId hA₁ ha₁ hb₁,
             PureReducesStar.congId hA₂ ha₂ hb₂⟩
  | @congPi A₁ A₂ B₁ B₂ L hA hB ihA ihB =>
      have hlcA₁ : lc_at 0 A₁ = true := by
        simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcB₁ : lc_at 1 B₁ = true := by
        simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      obtain ⟨uA, hA₁s, hA₂s⟩ := ihA hlcA₁
      -- For the codomain: pick x₀ fresh for L and both bodies
      let Lx : Finset String := L ∪ listToFinset (freeVars B₁) ∪ listToFinset (freeVars B₂)
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lx
      have hx₀L : x₀ ∉ L := by
        intro hmem
        exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
      have hfreshB₁ : isFresh x₀ B₁ = true :=
        isFresh_of_not_in_freeVars_finset (p := B₁) (by
          intro hmem
          exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem)))
      have hfreshB₂ : isFresh x₀ B₂ = true :=
        isFresh_of_not_in_freeVars_finset (p := B₂) (by
          intro hmem
          exact hx₀ (Finset.mem_union_right _ hmem))
      have hlcOpen₁ := lc_at_openBVar_result hlcB₁ (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨uBx₀, hB₁s, hB₂s⟩ := ihB x₀ hx₀L hlcOpen₁
      -- Close the common reduct to get a body
      let uB := closeBVar 0 x₀ uBx₀
      have hlcUBx₀ := pureReducesStar_preserves_lc hB₁s hlcOpen₁
      have hlcUB : lc_at 1 uB = true := lc_at_closeBVar hlcUBx₀
      -- Build multi-step reductions for all fresh y
      refine ⟨mkPi uA uB, ?_, ?_⟩
      · -- mkPi A₁ B₁ →* mkPi uA uB
        exact (PureReducesStar.congPiDom hA₁s).trans
          (PureReducesStar.congPiCodLC L hlcB₁ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₁))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₁s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₁) =
                  openBVar 0 (.fvar y) B₁ := by
              simpa using (substFVar_intro (p := B₁) (x := x₀) (u := .fvar y) hfreshB₁ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) B₁) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid))
      · -- mkPi A₂ B₂ →* mkPi uA uB
        have hlcA₂ := (PureConv_preserves_lc_both hA).1 hlcA₁
        have hlcB₂ : lc_at 1 B₂ = true := by
          have hlcOpen₂ := (PureConv_preserves_lc_both (hB x₀ hx₀L)).1 hlcOpen₁
          exact lc_at_of_openBVar hlcOpen₂
        exact (PureReducesStar.congPiDom hA₂s).trans
          (PureReducesStar.congPiCodLC L hlcB₂ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₂))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₂s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₂) =
                  openBVar 0 (.fvar y) B₂ := by
              simpa using (substFVar_intro (p := B₂) (x := x₀) (u := .fvar y) hfreshB₂ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) B₂) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid))
  | @congSigma A₁ A₂ B₁ B₂ L hA hB ihA ihB =>
      have hlcA₁ : lc_at 0 A₁ = true := by
        simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcB₁ : lc_at 1 B₁ = true := by
        simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      obtain ⟨uA, hA₁s, hA₂s⟩ := ihA hlcA₁
      let Lx : Finset String := L ∪ listToFinset (freeVars B₁) ∪ listToFinset (freeVars B₂)
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lx
      have hx₀L : x₀ ∉ L := by
        intro hmem
        exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
      have hfreshB₁ : isFresh x₀ B₁ = true :=
        isFresh_of_not_in_freeVars_finset (p := B₁) (by
          intro hmem
          exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem)))
      have hfreshB₂ : isFresh x₀ B₂ = true :=
        isFresh_of_not_in_freeVars_finset (p := B₂) (by
          intro hmem
          exact hx₀ (Finset.mem_union_right _ hmem))
      have hlcOpen₁ := lc_at_openBVar_result hlcB₁ (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨uBx₀, hB₁s, hB₂s⟩ := ihB x₀ hx₀L hlcOpen₁
      let uB := closeBVar 0 x₀ uBx₀
      have hlcUBx₀ := pureReducesStar_preserves_lc hB₁s hlcOpen₁
      have hlcUB : lc_at 1 uB = true := lc_at_closeBVar hlcUBx₀
      refine ⟨mkSigma uA uB, ?_, ?_⟩
      · exact (PureReducesStar.congSigmaDom hA₁s).trans
          (PureReducesStar.congSigmaCodLC L hlcB₁ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₁))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₁s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₁) =
                  openBVar 0 (.fvar y) B₁ := by
              simpa using (substFVar_intro (p := B₁) (x := x₀) (u := .fvar y) hfreshB₁ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) B₁) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid))
      · have hlcB₂ : lc_at 1 B₂ = true := by
          have hlcOpen₂ := (PureConv_preserves_lc_both (hB x₀ hx₀L)).1 hlcOpen₁
          exact lc_at_of_openBVar hlcOpen₂
        exact (PureReducesStar.congSigmaDom hA₂s).trans
          (PureReducesStar.congSigmaCodLC L hlcB₂ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₂))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₂s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₂) =
                  openBVar 0 (.fvar y) B₂ := by
              simpa using (substFVar_intro (p := B₂) (x := x₀) (u := .fvar y) hfreshB₂ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) B₂) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid))
  | @congLam body₁ body₂ L hB ihB =>
      have hlcB₁ : lc_at 1 body₁ = true := by
        simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
      let Lx : Finset String := L ∪ listToFinset (freeVars body₁) ∪ listToFinset (freeVars body₂)
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lx
      have hx₀L : x₀ ∉ L := by
        intro hmem
        exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
      have hfreshBody₁ : isFresh x₀ body₁ = true :=
        isFresh_of_not_in_freeVars_finset (p := body₁) (by
          intro hmem
          exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem)))
      have hfreshBody₂ : isFresh x₀ body₂ = true :=
        isFresh_of_not_in_freeVars_finset (p := body₂) (by
          intro hmem
          exact hx₀ (Finset.mem_union_right _ hmem))
      have hlcOpen₁ := lc_at_openBVar_result hlcB₁ (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨uBx₀, hB₁s, hB₂s⟩ := ihB x₀ hx₀L hlcOpen₁
      let uB := closeBVar 0 x₀ uBx₀
      have hlcUBx₀ := pureReducesStar_preserves_lc hB₁s hlcOpen₁
      have hlcUB : lc_at 1 uB = true := lc_at_closeBVar hlcUBx₀
      refine ⟨mkLam uB, ?_, ?_⟩
      · exact PureReducesStar.congLamLC L hlcB₁ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) body₁))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₁s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) body₁) =
                  openBVar 0 (.fvar y) body₁ := by
              simpa using (substFVar_intro (p := body₁) (x := x₀) (u := .fvar y) hfreshBody₁ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) body₁) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid)
      · have hlcB₂ : lc_at 1 body₂ = true := by
          have hlcOpen₂ := (PureConv_preserves_lc_both (hB x₀ hx₀L)).1 hlcOpen₁
          exact lc_at_of_openBVar hlcOpen₂
        exact PureReducesStar.congLamLC L hlcB₂ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) body₂))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₂s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) body₂) =
                  openBVar 0 (.fvar y) body₂ := by
              simpa using (substFVar_intro (p := body₂) (x := x₀) (u := .fvar y) hfreshBody₂ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) body₂) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid)

/-! ## Counterexample: Unconditional Backward Head Preservation is FALSE

β-reduction CAN produce a Pi-headed term from a non-Pi term.
The identity function applied to a Pi type β-reduces to that Pi type,
but `mkApp (mkLam ..) ..` is always App-headed, never Pi-headed.
This proves the direct inversion route (`pureConv_pi_inv` / `pureConv_sigma_inv`
with unconditional bidirectional head preservation) is impossible. -/

/-- β fires: (λx.x)(Π(X,Y)) ≡ Π(X,Y) — conversion from non-Pi to Pi. -/
theorem conv_nonPi_to_Pi (X Y : Pattern)
    (hlcX : lc_at 0 X = true) (hlcY : lc_at 1 Y = true) :
    PureConv (mkApp (mkLam (.bvar 0)) (mkPi X Y)) (mkPi X Y) := by
  have hlcBody : lc_at 1 (.bvar 0 : Pattern) = true := by simp [lc_at]
  have hlcPi : lc_at 0 (mkPi X Y) = true := by
    simp [mkPi, lc_at, lc_at_list, Bool.and_eq_true]
    exact ⟨hlcX, hlcY⟩
  have h := PureConv.betaPi (.bvar 0) (mkPi X Y) hlcBody hlcPi
  simp [openBVar, mkPi] at h
  exact h

/-- The source `mkApp (mkLam (.bvar 0)) (mkPi X Y)` is NEVER a Pi. -/
theorem app_ne_pi (X Y A B : Pattern) :
    mkApp (mkLam (.bvar 0)) (mkPi X Y) ≠ mkPi A B := by
  simp [mkApp, mkLam, mkPi]

/-! ## Pi/Sigma Injectivity via Church-Rosser

Uses `church_rosser` + head preservation + decomposition to extract
convertible components from convertible Pi/Sigma types. -/

/-- Pi-injectivity: convertible Pi types have convertible components. -/
theorem pi_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkPi A₁ B₁) (mkPi A₂ B₂))
    (hlc : lc_at 0 (mkPi A₁ B₁) = true) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) := by
  have hlcA₁ : lc_at 0 A₁ = true := by
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
  have hlcB₁ : lc_at 1 B₁ = true := by
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
  have hlc₂ := PureConv_preserves_lc h hlc
  have hlcA₂ : lc_at 0 A₂ = true := by
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc₂; exact hlc₂.1
  have hlcB₂ : lc_at 1 B₂ = true := by
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc₂; exact hlc₂.2
  obtain ⟨u, h₁, h₂⟩ := church_rosser_lc h hlc
  obtain ⟨A', B', heq⟩ := reduceStar_pi_head h₁
  subst heq
  obtain ⟨hdomL, Ll, hcodL⟩ := reduceStar_pi_decomp h₁
  obtain ⟨hdomR, Lr, hcodR⟩ := reduceStar_pi_decomp h₂
  exact ⟨.trans (PureReducesStar_implies_PureConv hdomL hlcA₁)
               (.symm (PureReducesStar_implies_PureConv hdomR hlcA₂)),
         Ll ∪ Lr, fun x hx =>
           .trans (PureReducesStar_implies_PureConv
                    (hcodL x (fun h => hx (Finset.mem_union_left _ h)))
                    (lc_at_openBVar_result hlcB₁ (by simp [lc_at])))
                  (.symm (PureReducesStar_implies_PureConv
                    (hcodR x (fun h => hx (Finset.mem_union_right _ h)))
                    (lc_at_openBVar_result hlcB₂ (by simp [lc_at]))))⟩

/-- Sigma-injectivity: convertible Sigma types have convertible components. -/
theorem sigma_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkSigma A₁ B₁) (mkSigma A₂ B₂))
    (hlc : lc_at 0 (mkSigma A₁ B₁) = true) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) := by
  have hlcA₁ : lc_at 0 A₁ = true := by
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
  have hlcB₁ : lc_at 1 B₁ = true := by
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
  have hlc₂ := PureConv_preserves_lc h hlc
  have hlcA₂ : lc_at 0 A₂ = true := by
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc₂; exact hlc₂.1
  have hlcB₂ : lc_at 1 B₂ = true := by
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc₂; exact hlc₂.2
  obtain ⟨u, h₁, h₂⟩ := church_rosser_lc h hlc
  obtain ⟨A', B', heq⟩ := reduceStar_sigma_head h₁
  subst heq
  obtain ⟨hdomL, Ll, hcodL⟩ := reduceStar_sigma_decomp h₁
  obtain ⟨hdomR, Lr, hcodR⟩ := reduceStar_sigma_decomp h₂
  exact ⟨.trans (PureReducesStar_implies_PureConv hdomL hlcA₁)
               (.symm (PureReducesStar_implies_PureConv hdomR hlcA₂)),
         Ll ∪ Lr, fun x hx =>
           .trans (PureReducesStar_implies_PureConv
                    (hcodL x (fun h => hx (Finset.mem_union_left _ h)))
                    (lc_at_openBVar_result hlcB₁ (by simp [lc_at])))
                  (.symm (PureReducesStar_implies_PureConv
                    (hcodR x (fun h => hx (Finset.mem_union_right _ h)))
                    (lc_at_openBVar_result hlcB₂ (by simp [lc_at]))))⟩

end Mettapedia.OSLF.MeTTaPure.Confluence
