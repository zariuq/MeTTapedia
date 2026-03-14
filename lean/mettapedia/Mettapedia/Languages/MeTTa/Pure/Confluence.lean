import Mettapedia.Languages.MeTTa.Pure.Reduction
import Mettapedia.Languages.MeTTa.Pure.FVarSubst
import Mettapedia.Languages.MeTTa.Pure.Fragment

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

namespace Mettapedia.Languages.MeTTa.Pure.Confluence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Substitution (openBVar lc_at lc_at_list openBVar_lc_at lc_at_openBVar_result lc_at_mono lc_at_list_mem freeVars isFresh)
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.Typing (PureConv PureConv_pure_both PureConv_rightPure)
open Mettapedia.Languages.MeTTa.Pure.Reduction
open Mettapedia.Languages.MeTTa.Pure.FVarSubst
open Mettapedia.Languages.MeTTa.Pure.Fragment

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
  /-- Catch-all reflexivity for patterns not covered by other constructors
      (e.g., `.lambda`, `.multiLambda`, `.collection`, or `.apply c args` for
      non-MeTTa-Pure labels). Also used as the base case for `parRed_refl`. -/
  | refl_pat (t : Pattern) : ParRed t t

/-! ## PureConv Preserves Local Closure

Proved independently of Church-Rosser. Both directions (fwd and bwd) are
proved simultaneously so the `symm` case works by swapping. -/

/-- PureConv preserves lc in both directions (needed for symm case). -/
theorem PureConv_preserves_lc_both {s t : Pattern} (h : PureConv s t) :
    (lc_at 0 s = true → lc_at 0 t = true) ∧
    (lc_at 0 t = true → lc_at 0 s = true) := by
  induction h with
  | refl _ _ => exact ⟨id, id⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨fun h => ih₂.1 (ih₁.1 h), fun h => ih₁.2 (ih₂.2 h)⟩
  | betaPi body a _ _ hlcBody hlcA =>
      constructor
      · intro hlc
        exact lc_at_openBVar_result hlcBody hlcA
      · intro _
        simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        exact ⟨hlcBody, hlcA⟩
  | betaSigmaFst a b _ _ hlcA hlcB =>
      exact ⟨fun _ => hlcA, fun _ => by
        simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        exact ⟨hlcA, hlcB⟩⟩
  | betaSigmaSnd a b _ _ hlcA hlcB =>
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

/-! ## Parallel Reduction: Basic Lemmas -/

/-- Reflexivity for ParRed. -/
theorem parRed_refl (t : Pattern) : ParRed t t := .refl_pat t

/-! ### ParRed preserves local closure (aux, needed early) -/

private theorem parRed_preserves_lc_aux {p q : Pattern}
    (h : ParRed p q) (hlc : lc_at 0 p = true) : lc_at 0 q = true := by
  induction h with
  | bvar n => exact hlc
  | fvar x => exact hlc
  | pi L hA hB ihA ihB =>
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    constructor
    · exact ihA hlc.1
    · obtain ⟨x, hx⟩ := exists_fresh L
      have := ihB x hx (lc_at_openBVar_result hlc.2 (by simp [lc_at]))
      exact lc_at_of_openBVar this
  | sigma L hA hB ihA ihB =>
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    constructor
    · exact ihA hlc.1
    · obtain ⟨x, hx⟩ := exists_fresh L
      have := ihB x hx (lc_at_openBVar_result hlc.2 (by simp [lc_at]))
      exact lc_at_of_openBVar this
  | lam L hB ihB =>
    simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    obtain ⟨x, hx⟩ := exists_fresh L
    have := ihB x hx (lc_at_openBVar_result hlc (by simp [lc_at]))
    exact lc_at_of_openBVar this
  | app hf ha ihf iha =>
    simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ihf hlc.1, iha hlc.2⟩
  | pair ha hb iha ihb =>
    simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨iha hlc.1, ihb hlc.2⟩
  | fst hp ihp =>
    simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ihp hlc
  | snd hp ihp =>
    simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ihp hlc
  | id hA ha hb ihA iha ihb =>
    simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ihA hlc.1, iha hlc.2.1, ihb hlc.2.2⟩
  | refl ha iha =>
    simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact iha hlc
  | betaPi L hbody ha hlcBody hlcA ihbody iha =>
    simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact lc_at_openBVar_result
      (by
        obtain ⟨x, hx⟩ := exists_fresh L
        have := ihbody x hx (lc_at_openBVar_result hlcBody (by simp [lc_at]))
        exact lc_at_of_openBVar this)
      (iha hlc.2)
  | betaSigmaFst ha hb iha ihb =>
    simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact iha hlc.1
  | betaSigmaSnd ha hb iha ihb =>
    simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact ihb hlc.2
  | refl_pat t => exact hlc

/-! ### openBVar commutativity for fvar opens

`openBVar j (fvar x) (openBVar k (fvar y) p) = openBVar k (fvar y) (openBVar j (fvar x) p)`
when `j ≠ k`. Needed for `parRed_openBVar_fvar`. -/

private theorem openBVar_comm_fvar {j k : Nat} {x y : String} (hjk : j ≠ k)
    (p : Pattern) :
    openBVar j (.fvar x) (openBVar k (.fvar y) p) =
      openBVar k (.fvar y) (openBVar j (.fvar x) p) := by
  induction p using Pattern.inductionOn generalizing j k with
  | hbvar n =>
    simp only [openBVar]
    by_cases hnk : n = k
    · subst hnk
      have hne : ¬(n = j) := fun h => hjk (h ▸ rfl)
      simp [show (n == k) = true from beq_iff_eq.mpr rfl,
            show (n == j) = false from beq_eq_false_iff_ne.mpr hne, openBVar]
    · by_cases hnj : n = j
      · subst hnj
        simp [show (n == k) = false from beq_eq_false_iff_ne.mpr hnk,
              show (n == j) = true from beq_iff_eq.mpr rfl, openBVar]
      · simp [show (n == k) = false from beq_eq_false_iff_ne.mpr hnk,
              show (n == j) = false from beq_eq_false_iff_ne.mpr hnj, openBVar]
  | hfvar z => simp [openBVar]
  | happly c args ih =>
    simp only [openBVar, List.map_map]
    congr 1; exact List.map_congr_left fun a ha => ih a ha hjk
  | hlambda body ih =>
    simp only [openBVar]; congr 1
    exact ih (by omega : j + 1 ≠ k + 1)
  | hmultiLambda n body ih =>
    simp only [openBVar]; congr 1
    exact ih (by omega : j + n ≠ k + n)
  | hsubst body repl ihb ihr =>
    simp only [openBVar]; congr 1
    · exact ihb (by omega : j + 1 ≠ k + 1)
    · exact ihr hjk
  | hcollection ct elems rest ih =>
    simp only [openBVar, List.map_map]
    congr 1; exact List.map_congr_left fun a ha => ih a ha hjk

/-- Composition law for opening:
    opening at `j` and then at `k+j` equals opening `p` first at `k+j+1`
    then opening at `j`, provided `u` and `p` are locally closed at the
    corresponding levels. -/
private theorem openBVar_open_comp_lc {j k : Nat} {u v p : Pattern}
    (hlcU : lc_at j u = true) (hlcP : lc_at (j + 1) p = true) :
    openBVar (k + j) v (openBVar j u p) =
      openBVar j u (openBVar (k + j + 1) v p) := by
  induction p using Pattern.inductionOn generalizing j k with
  | hbvar n =>
    by_cases hnj : n = j
    · subst hnj
      have hlcUkj : lc_at (k + n) u = true := lc_at_mono hlcU (Nat.le_add_left n k)
      have hId : openBVar (k + n) v u = u := openBVar_lc_at (k + n) v u hlcUkj
      have hnj1 : n ≠ k + n + 1 := by omega
      calc
        openBVar (k + n) v (openBVar n u (.bvar n))
            = openBVar (k + n) v u := by simp [openBVar]
        _ = u := hId
        _ = openBVar n u (openBVar (k + n + 1) v (.bvar n)) := by
              simp [openBVar, beq_eq_false_iff_ne.mpr hnj1]
    · have hnlt : n < j + 1 := by
        simpa [lc_at, decide_eq_true_eq] using hlcP
      have hnkj : n ≠ k + j := by omega
      have hnkj1 : n ≠ k + j + 1 := by omega
      simp [openBVar, beq_eq_false_iff_ne.mpr hnj,
        beq_eq_false_iff_ne.mpr hnkj, beq_eq_false_iff_ne.mpr hnkj1]
  | hfvar _ =>
    simp [openBVar]
  | happly c args ih =>
    simp only [lc_at] at hlcP
    simp only [openBVar]
    congr 1
    simp only [List.map_map]
    exact List.map_congr_left (fun a ha =>
      ih a ha (j := j) (k := k) hlcU (lc_at_list_mem hlcP ha))
  | hlambda body ih =>
    simp only [openBVar, lc_at] at hlcP ⊢
    have hlcU' : lc_at (j + 1) u = true := lc_at_mono hlcU (Nat.le_add_right j 1)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (j := j + 1) (k := k) hlcU' hlcP
  | hmultiLambda n body ih =>
    simp only [openBVar, lc_at] at hlcP ⊢
    have hlcU' : lc_at (j + n) u = true := lc_at_mono hlcU (Nat.le_add_right j n)
    have hlcBody : lc_at (j + n + 1) body = true := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlcP
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (j := j + n) (k := k) hlcU' hlcBody
  | hsubst body repl ihb ihr =>
    simp only [lc_at, Bool.and_eq_true] at hlcP
    simp only [openBVar]
    congr 1
    · have hlcU' : lc_at (j + 1) u = true := lc_at_mono hlcU (Nat.le_add_right j 1)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ihb (j := j + 1) (k := k) hlcU' hlcP.1
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ihr (j := j) (k := k) hlcU hlcP.2
  | hcollection ct elems rest ih =>
    simp only [lc_at] at hlcP
    simp only [openBVar]
    congr 1
    simp only [List.map_map]
    exact List.map_congr_left (fun a ha =>
      ih a ha (j := j) (k := k) hlcU (lc_at_list_mem hlcP ha))

/-- ParRed is preserved by opening with a free variable. -/
theorem parRed_openBVar_fvar {y : String} {p q : Pattern}
    (h : ParRed p q) : ∀ (k : Nat),
    ParRed (openBVar k (.fvar y) p) (openBVar k (.fvar y) q) := by
  induction h with
  | bvar n => intro k; simp [openBVar]; split <;> exact parRed_refl _
  | fvar x => intro _; simp [openBVar]; exact .fvar x
  | pi L hA hB ihA ihB =>
    intro k
    simp only [openBVar_mkPi]
    exact .pi (L ∪ {y}) (ihA k) (fun z hz => by
      have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
      have hzy : z ≠ y := fun h => hz (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      rw [openBVar_comm_fvar (by omega : 0 ≠ k + 1),
          openBVar_comm_fvar (by omega : 0 ≠ k + 1)]
      exact ihB z hzL (k + 1))
  | sigma L hA hB ihA ihB =>
    intro k
    simp only [openBVar_mkSigma]
    exact .sigma (L ∪ {y}) (ihA k) (fun z hz => by
      have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
      have hzy : z ≠ y := fun h => hz (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      rw [openBVar_comm_fvar (by omega : 0 ≠ k + 1),
          openBVar_comm_fvar (by omega : 0 ≠ k + 1)]
      exact ihB z hzL (k + 1))
  | lam L hB ihB =>
    intro k
    simp only [openBVar_mkLam]
    exact .lam (L ∪ {y}) (fun z hz => by
      have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
      have hzy : z ≠ y := fun h => hz (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      rw [openBVar_comm_fvar (by omega : 0 ≠ k + 1),
          openBVar_comm_fvar (by omega : 0 ≠ k + 1)]
      exact ihB z hzL (k + 1))
  | app hf ha ihf iha =>
    intro k; simp only [openBVar_mkApp]; exact .app (ihf k) (iha k)
  | pair ha hb iha ihb =>
    intro k; simp only [openBVar_mkPair]; exact .pair (iha k) (ihb k)
  | fst hp ihp =>
    intro k; simp only [openBVar_mkFst]; exact .fst (ihp k)
  | snd hp ihp =>
    intro k; simp only [openBVar_mkSnd]; exact .snd (ihp k)
  | id hA ha hb ihA iha ihb =>
    intro k; simp only [openBVar_mkId]; exact .id (ihA k) (iha k) (ihb k)
  | refl ha iha =>
    intro k; simp only [openBVar_mkRefl]; exact .refl (iha k)
  | @betaPi bd bd' ar ar' L hbody ha hlcBody hlcA ihbody iha =>
    intro k
    simp only [openBVar_mkApp, openBVar_mkLam]
    -- Goal: ParRed (mkApp (mkLam (openBVar (k+1) (.fvar y) bd)) (openBVar k (.fvar y) ar))
    --              (openBVar k (.fvar y) (openBVar 0 ar' bd'))
    -- Need: openBVar k (.fvar y) (openBVar 0 ar' bd')
    --      = openBVar 0 (openBVar k (.fvar y) ar') (openBVar (k+1) (.fvar y) bd')
    -- This is the open-open commutativity for locally nameless; requires lc_at 1 bd'.
    -- The identity holds because lc_at 1 bd' prevents .bvar (k+1) at any depth
    -- where openBVar (k+1) (.fvar y) would mismatch.
    -- Need lc_at 1 bd' to apply open/open composition.
    have hlcBd' : lc_at 1 bd' = true := by
      obtain ⟨x₀, hx₀⟩ := exists_fresh L
      have hOpen : ParRed (openBVar 0 (.fvar x₀) bd) (openBVar 0 (.fvar x₀) bd') := hbody x₀ hx₀
      have hlcOpen : lc_at 0 (openBVar 0 (.fvar x₀) bd) = true :=
        lc_at_openBVar_result hlcBody (by simp [lc_at])
      exact lc_at_of_openBVar (parRed_preserves_lc_aux hOpen hlcOpen)
    have hlcAr' : lc_at 0 ar' = true := parRed_preserves_lc_aux ha hlcA
    have hArg : openBVar k (.fvar y) ar' = ar' := by
      have hk : lc_at k ar' = true := lc_at_mono hlcAr' (Nat.zero_le k)
      exact openBVar_lc_at k (.fvar y) ar' hk
    have hcomp :
        openBVar k (.fvar y) (openBVar 0 ar' bd') =
          openBVar 0 (openBVar k (.fvar y) ar') (openBVar (k + 1) (.fvar y) bd') := by
      calc
        openBVar k (.fvar y) (openBVar 0 ar' bd')
            = openBVar 0 ar' (openBVar (k + 1) (.fvar y) bd') := by
                simpa [Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  (openBVar_open_comp_lc (j := 0) (k := k) (u := ar') (v := .fvar y) (p := bd') hlcAr' hlcBd')
        _ = openBVar 0 (openBVar k (.fvar y) ar') (openBVar (k + 1) (.fvar y) bd') := by
              rw [hArg]
    have hcomp' :
        openBVar 0 (openBVar k (.fvar y) ar') (openBVar (k + 1) (.fvar y) bd') =
          openBVar k (.fvar y) (openBVar 0 ar' bd') := hcomp.symm
    simpa [hcomp'] using
      (.betaPi (L ∪ {y})
        (fun z hz => by
          have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
          rw [openBVar_comm_fvar (by omega : 0 ≠ k + 1),
              openBVar_comm_fvar (by omega : 0 ≠ k + 1)]
          exact ihbody z hzL (k + 1))
        (iha k)
        (by
          have h := lc_at_mono hlcBody (by omega : 1 ≤ k + 1)
          rw [openBVar_lc_at _ _ _ h]
          exact hlcBody)
        (by
          have h := lc_at_mono hlcA (Nat.zero_le k)
          rw [openBVar_lc_at _ _ _ h]
          exact hlcA) : ParRed
          (mkApp (mkLam (openBVar (k + 1) (.fvar y) bd)) (openBVar k (.fvar y) ar))
          (openBVar 0 (openBVar k (.fvar y) ar') (openBVar (k + 1) (.fvar y) bd')))
  | betaSigmaFst ha hb iha ihb =>
    intro k; simp only [openBVar_mkFst, openBVar_mkPair]
    exact .betaSigmaFst (iha k) (ihb k)
  | betaSigmaSnd ha hb iha ihb =>
    intro k; simp only [openBVar_mkSnd, openBVar_mkPair]
    exact .betaSigmaSnd (iha k) (ihb k)
  | refl_pat t => intro k; exact .refl_pat _

/-! ### ParRed substitution -/

/-- Parallel reduction preserves the pure fragment when started from a pure source. -/
private theorem parRed_preserves_pure {p q : Pattern}
    (h : ParRed p q) (hp : PureTmPattern p) : PureTmPattern q := by
  induction h with
  | bvar n =>
    cases hp
    exact .bvar n
  | fvar x =>
    cases hp
    exact .fvar x
  | @pi A A' B B' L hA hB ihA ihB =>
    let hAB := pure_pi_inv hp
    have hA' : PureTmPattern A' := ihA hAB.1
    set S := L ∪ listToFinset (freeVars B')
    obtain ⟨x₀, hx₀⟩ := exists_fresh S
    have hx₀L : x₀ ∉ L := fun hmem => hx₀ (Finset.mem_union_left _ hmem)
    have hx₀B' : x₀ ∉ listToFinset (freeVars B') := fun hmem => hx₀ (Finset.mem_union_right _ hmem)
    have hOpenSrc : PureTmPattern (openBVar 0 (.fvar x₀) B) := pureTm_openBVar_fvar x₀ hAB.2
    have hOpenTgt : PureTmPattern (openBVar 0 (.fvar x₀) B') := ihB x₀ hx₀L hOpenSrc
    have hB' : PureTmPattern B' :=
      pureTm_of_openBVar_fresh x₀ hOpenTgt (isFresh_of_not_in_freeVars_finset (p := B') hx₀B')
    exact .pi hA' hB'
  | @sigma A A' B B' L hA hB ihA ihB =>
    let hAB := pure_sigma_inv hp
    have hA' : PureTmPattern A' := ihA hAB.1
    set S := L ∪ listToFinset (freeVars B')
    obtain ⟨x₀, hx₀⟩ := exists_fresh S
    have hx₀L : x₀ ∉ L := fun hmem => hx₀ (Finset.mem_union_left _ hmem)
    have hx₀B' : x₀ ∉ listToFinset (freeVars B') := fun hmem => hx₀ (Finset.mem_union_right _ hmem)
    have hOpenSrc : PureTmPattern (openBVar 0 (.fvar x₀) B) := pureTm_openBVar_fvar x₀ hAB.2
    have hOpenTgt : PureTmPattern (openBVar 0 (.fvar x₀) B') := ihB x₀ hx₀L hOpenSrc
    have hB' : PureTmPattern B' :=
      pureTm_of_openBVar_fresh x₀ hOpenTgt (isFresh_of_not_in_freeVars_finset (p := B') hx₀B')
    exact .sigma hA' hB'
  | @lam body body' L hBody ihBody =>
    let hBodySrc := pure_lam_inv hp
    set S := L ∪ listToFinset (freeVars body')
    obtain ⟨x₀, hx₀⟩ := exists_fresh S
    have hx₀L : x₀ ∉ L := fun hmem => hx₀ (Finset.mem_union_left _ hmem)
    have hx₀Body' : x₀ ∉ listToFinset (freeVars body') := fun hmem => hx₀ (Finset.mem_union_right _ hmem)
    have hOpenSrc : PureTmPattern (openBVar 0 (.fvar x₀) body) := pureTm_openBVar_fvar x₀ hBodySrc
    have hOpenTgt : PureTmPattern (openBVar 0 (.fvar x₀) body') := ihBody x₀ hx₀L hOpenSrc
    have hBody' : PureTmPattern body' :=
      pureTm_of_openBVar_fresh x₀ hOpenTgt (isFresh_of_not_in_freeVars_finset (p := body') hx₀Body')
    exact .lam hBody'
  | @app f f' a a' hf ha ihf iha =>
    let hfa := pure_app_inv hp
    exact .app (ihf hfa.1) (iha hfa.2)
  | @pair a a' b b' ha hb iha ihb =>
    let hab := pure_pair_inv hp
    exact .pair (iha hab.1) (ihb hab.2)
  | @fst p p' hp' ihp =>
    let hpp := pure_fst_inv hp
    exact .fst (ihp hpp)
  | @snd p p' hp' ihp =>
    let hpp := pure_snd_inv hp
    exact .snd (ihp hpp)
  | @id A A' a a' b b' hA ha hb ihA iha ihb =>
    let hId := pure_id_inv hp
    exact .id (ihA hId.1) (iha hId.2.1) (ihb hId.2.2)
  | @refl a a' ha iha =>
    let haPure := pure_refl_inv hp
    exact .refl (iha haPure)
  | @betaPi bd bd' ar ar' L hbody ha hlcBody hlcA ihbody iha =>
    let hApp := pure_app_inv hp
    let hbd := pure_lam_inv hApp.1
    have har' : PureTmPattern ar' := iha hApp.2
    set S := L ∪ listToFinset (freeVars bd')
    obtain ⟨x₀, hx₀⟩ := exists_fresh S
    have hx₀L : x₀ ∉ L := fun hmem => hx₀ (Finset.mem_union_left _ hmem)
    have hx₀Bd' : x₀ ∉ listToFinset (freeVars bd') := fun hmem => hx₀ (Finset.mem_union_right _ hmem)
    have hOpenSrc : PureTmPattern (openBVar 0 (.fvar x₀) bd) := pureTm_openBVar_fvar x₀ hbd
    have hOpenTgt : PureTmPattern (openBVar 0 (.fvar x₀) bd') := ihbody x₀ hx₀L hOpenSrc
    have hbd' : PureTmPattern bd' :=
      pureTm_of_openBVar_fresh x₀ hOpenTgt (isFresh_of_not_in_freeVars_finset (p := bd') hx₀Bd')
    simpa using (pureTm_openBVar har' (k := 0) hbd')
  | @betaSigmaFst a a' b b' ha hb iha ihb =>
    let hPair := pure_fst_inv hp
    let hab := pure_pair_inv hPair
    exact iha hab.1
  | @betaSigmaSnd a a' b b' ha hb iha ihb =>
    let hPair := pure_snd_inv hp
    let hab := pure_pair_inv hPair
    exact ihb hab.2
  | refl_pat _ =>
    simpa using hp

/-- Substituting the same fvar-replacement into both sides of ParRed.
    Uses sizeOf-based recursion so we can recurse into bodies inside `.lambda`
    wrappers (e.g., the codomain `B` of `mkPi A B = .apply "Pi" [A, .lambda B]`).
    Restricted to `PureTmPattern` to avoid ambient-host constructors. -/
private theorem parRed_substFVar_both {x : String} {u u' : Pattern}
    (hu : ParRed u u')
    {t : Pattern} (hpure : PureTmPattern t) :
    ParRed (substFVar x u t) (substFVar x u' t) := by
  induction hpure with
  | bvar n =>
    simp
    exact .bvar n
  | fvar y =>
    simp only [substFVar]
    split
    · exact hu
    · exact .fvar y
  | u0 =>
    simpa [u0, substFVar] using (parRed_refl u0)
  | u1 =>
    simpa [u1, substFVar] using (parRed_refl u1)
  | pi hA hB ihA ihB =>
    simpa [substFVar_mkPi] using
      (ParRed.pi ({x}) ihA (fun y _ => parRed_openBVar_fvar ihB 0))
  | sigma hA hB ihA ihB =>
    simpa [substFVar_mkSigma] using
      (ParRed.sigma ({x}) ihA (fun y _ => parRed_openBVar_fvar ihB 0))
  | lam hBody ihBody =>
    simpa [substFVar_mkLam] using
      (ParRed.lam ({x}) (fun y _ => parRed_openBVar_fvar ihBody 0))
  | app hf ha ihf iha =>
    simpa [substFVar_mkApp] using (ParRed.app ihf iha)
  | pair ha hb iha ihb =>
    simpa [substFVar_mkPair] using (ParRed.pair iha ihb)
  | fst hp ihp =>
    simpa [substFVar_mkFst] using (ParRed.fst ihp)
  | snd hp ihp =>
    simpa [substFVar_mkSnd] using (ParRed.snd ihp)
  | id hA ha hb ihA iha ihb =>
    simpa [substFVar_mkId] using (ParRed.id ihA iha ihb)
  | refl ha iha =>
    simpa [substFVar_mkRefl] using (ParRed.refl iha)

/-- Full ParRed substitution: if `ParRed u u'` and `ParRed p q`,
    then `ParRed (substFVar x u p) (substFVar x u' q)`.
    Restricted to pure-source terms. -/
theorem parRed_substFVar {x : String} {u u' : Pattern}
    (hu : ParRed u u') (hlc_u : lc_at 0 u = true) (hlc_u' : lc_at 0 u' = true)
    {p q : Pattern} (h : ParRed p q) (hp : PureTmPattern p) :
    ParRed (substFVar x u p) (substFVar x u' q) := by
  revert hp
  induction h with
  | bvar n =>
    intro hp
    cases hp
    simp
    exact .bvar n
  | fvar y =>
    intro hp
    cases hp
    simp only [substFVar]; split
    · exact hu
    · exact .fvar y
  | @pi A A' B B' L hA hB ihA ihB =>
    intro hp
    let hAB := pure_pi_inv hp
    simp only [substFVar_mkPi]
    exact .pi (L ∪ {x}) (ihA hAB.1) (fun y hy => by
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have hpOpen : PureTmPattern (openBVar 0 (.fvar y) B) := pureTm_openBVar_fvar y hAB.2
      have key := ihB y hyL hpOpen
      rwa [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx] at key)
  | @sigma A A' B B' L hA hB ihA ihB =>
    intro hp
    let hAB := pure_sigma_inv hp
    simp only [substFVar_mkSigma]
    exact .sigma (L ∪ {x}) (ihA hAB.1) (fun y hy => by
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have hpOpen : PureTmPattern (openBVar 0 (.fvar y) B) := pureTm_openBVar_fvar y hAB.2
      have key := ihB y hyL hpOpen
      rwa [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx] at key)
  | @lam body body' L hB ihB =>
    intro hp
    let hBody := pure_lam_inv hp
    simp only [substFVar_mkLam]
    exact .lam (L ∪ {x}) (fun y hy => by
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have hpOpen : PureTmPattern (openBVar 0 (.fvar y) body) := pureTm_openBVar_fvar y hBody
      have key := ihB y hyL hpOpen
      rwa [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx] at key)
  | @app f f' a a' hf ha ihf iha =>
    intro hp
    let hfa := pure_app_inv hp
    simp only [substFVar_mkApp]
    exact .app (ihf hfa.1) (iha hfa.2)
  | @pair a a' b b' ha hb iha ihb =>
    intro hp
    let hab := pure_pair_inv hp
    simp only [substFVar_mkPair]
    exact .pair (iha hab.1) (ihb hab.2)
  | @fst p p' hp ihp =>
    intro hpPure
    let hp' := pure_fst_inv hpPure
    simp only [substFVar_mkFst]
    exact .fst (ihp hp')
  | @snd p p' hp ihp =>
    intro hpPure
    let hp' := pure_snd_inv hpPure
    simp only [substFVar_mkSnd]
    exact .snd (ihp hp')
  | @id A A' a a' b b' hA ha hb ihA iha ihb =>
    intro hp
    let hId := pure_id_inv hp
    simp only [substFVar_mkId]
    exact .id (ihA hId.1) (iha hId.2.1) (ihb hId.2.2)
  | @refl a a' ha iha =>
    intro hp
    let ha_pure := pure_refl_inv hp
    simp only [substFVar_mkRefl]
    exact .refl (iha ha_pure)
  | @betaPi bd bd' ar ar' L hbody ha hlcBody hlcA ihbody iha =>
    intro hp
    let hApp := pure_app_inv hp
    let hbd := pure_lam_inv hApp.1
    simp only [substFVar_mkApp, substFVar_mkLam]
    rw [substFVar_openBVar_comm hlc_u']
    exact .betaPi (L ∪ {x})
      (fun y hy => by
        have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
        have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
        have hpOpen : PureTmPattern (openBVar 0 (.fvar y) bd) := pureTm_openBVar_fvar y hbd
        have key := ihbody y hyL hpOpen
        rwa [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
             substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx] at key)
      (iha hApp.2)
      (lc_at_substFVar hlcBody (lc_at_mono hlc_u (Nat.le_add_right 0 1)))
      (lc_at_substFVar hlcA hlc_u)
  | @betaSigmaFst a a' b b' ha hb iha ihb =>
    intro hp
    let hPair := pure_fst_inv hp
    let hab := pure_pair_inv hPair
    simp only [substFVar_mkFst, substFVar_mkPair]
    exact .betaSigmaFst (iha hab.1) (ihb hab.2)
  | @betaSigmaSnd a a' b b' ha hb iha ihb =>
    intro hp
    let hPair := pure_snd_inv hp
    let hab := pure_pair_inv hPair
    simp only [substFVar_mkSnd, substFVar_mkPair]
    exact .betaSigmaSnd (iha hab.1) (ihb hab.2)
  | refl_pat t =>
    intro hp
    exact parRed_substFVar_both hu hp

/-- Same-substituent substitution transport for ParRed.
    This one does not need pure-fragment restrictions because the
    `refl_pat` branch stays reflexive after substitution. -/
private theorem parRed_substFVar_same {x : String} {u p q : Pattern}
    (hlc_u : lc_at 0 u = true)
    (h : ParRed p q) :
    ParRed (substFVar x u p) (substFVar x u q) := by
  induction h with
  | bvar n =>
    simp
    exact .bvar n
  | fvar y =>
    simp only [substFVar]
    split
    · exact parRed_refl u
    · exact .fvar y
  | pi L hA hB ihA ihB =>
    simp only [substFVar_mkPi]
    exact .pi (L ∪ {x}) ihA (fun y hy => by
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ihB y hyL
      rwa [substFVar_openBVar_comm hlc_u,
           substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc_u,
           substFVar_fvar_ne u hyx] at key)
  | sigma L hA hB ihA ihB =>
    simp only [substFVar_mkSigma]
    exact .sigma (L ∪ {x}) ihA (fun y hy => by
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ihB y hyL
      rwa [substFVar_openBVar_comm hlc_u,
           substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc_u,
           substFVar_fvar_ne u hyx] at key)
  | lam L hB ihB =>
    simp only [substFVar_mkLam]
    exact .lam (L ∪ {x}) (fun y hy => by
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      have key := ihB y hyL
      rwa [substFVar_openBVar_comm hlc_u,
           substFVar_fvar_ne u hyx,
           substFVar_openBVar_comm hlc_u,
           substFVar_fvar_ne u hyx] at key)
  | app hf ha ihf iha =>
    simpa [substFVar_mkApp] using .app ihf iha
  | pair ha hb iha ihb =>
    simpa [substFVar_mkPair] using .pair iha ihb
  | fst hp ihp =>
    simpa [substFVar_mkFst] using .fst ihp
  | snd hp ihp =>
    simpa [substFVar_mkSnd] using .snd ihp
  | id hA ha hb ihA iha ihb =>
    simpa [substFVar_mkId] using .id ihA iha ihb
  | refl ha iha =>
    simpa [substFVar_mkRefl] using .refl iha
  | betaPi L hbody ha hlcBody hlcA ihbody iha =>
    simp only [substFVar_mkApp, substFVar_mkLam]
    rw [substFVar_openBVar_comm hlc_u]
    exact .betaPi (L ∪ {x})
      (fun y hy => by
        have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
        have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
        have key := ihbody y hyL
        rwa [substFVar_openBVar_comm hlc_u,
             substFVar_fvar_ne u hyx,
             substFVar_openBVar_comm hlc_u,
             substFVar_fvar_ne u hyx] at key)
      iha
      (lc_at_substFVar hlcBody (lc_at_mono hlc_u (Nat.le_add_right 0 1)))
      (lc_at_substFVar hlcA hlc_u)
  | betaSigmaFst ha hb iha ihb =>
    simpa [substFVar_mkFst, substFVar_mkPair] using .betaSigmaFst iha ihb
  | betaSigmaSnd ha hb iha ihb =>
    simpa [substFVar_mkSnd, substFVar_mkPair] using .betaSigmaSnd iha ihb
  | refl_pat t =>
    exact .refl_pat _

/-- Opening with parallel-reduced terms preserves ParRed.
    Uses the substFVar bridge (pick fresh x₀, subst, apply substFVar_intro). -/
theorem parRed_openBVar {a a' : Pattern} {body body' : Pattern}
    (L : Finset String)
    (hbody : ∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) body'))
    (hbodyPure : PureTmPattern body)
    (ha : ParRed a a')
    (hlcA : lc_at 0 a = true) (hlcA' : lc_at 0 a' = true) :
    ParRed (openBVar 0 a body) (openBVar 0 a' body') := by
  set L' := L ∪ listToFinset (freeVars body) ∪ listToFinset (freeVars body')
  obtain ⟨x₀, hx₀⟩ := exists_fresh L'
  have hx₀L : x₀ ∉ L := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hfreshBody : isFresh x₀ body = true :=
    isFresh_of_not_in_freeVars_finset (p := body) (fun h =>
      hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hfreshBody' : isFresh x₀ body' = true :=
    isFresh_of_not_in_freeVars_finset (p := body') (fun h =>
      hx₀ (Finset.mem_union_right _ h))
  have hOpenPure : PureTmPattern (openBVar 0 (.fvar x₀) body) :=
    pureTm_openBVar_fvar x₀ (k := 0) hbodyPure
  have key := parRed_substFVar (x := x₀) ha hlcA hlcA' (hbody x₀ hx₀L) hOpenPure
  rw [substFVar_intro body hfreshBody 0,
      substFVar_intro body' hfreshBody' 0] at key
  exact key

/-! ### Embeddings: PureReduces ↔ ParRed ↔ PureReducesStar -/

/-- Single-step reduction embeds into parallel reduction (requires lc). -/
theorem pureReduces_to_parRed {p q : Pattern} (h : PureReduces p q)
    (hlc : lc_at 0 p = true) : ParRed p q := by
  induction h with
  | betaPi body a =>
    have hlcB : lc_at 1 body = true := by
      simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcA : lc_at 0 a = true := by
      simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    exact .betaPi ∅ (fun x _ => parRed_openBVar_fvar (parRed_refl body) 0)
      (parRed_refl a) hlcB hlcA
  | betaSigmaFst a b => exact .betaSigmaFst (parRed_refl a) (parRed_refl b)
  | betaSigmaSnd a b => exact .betaSigmaSnd (parRed_refl a) (parRed_refl b)
  | congPiDom hA ih =>
    exact .pi ∅ (ih (by simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1))
      (fun _ _ => parRed_refl _)
  | congPiCod L A B B' hB ih =>
    exact .pi L (parRed_refl A) (fun x hx =>
      ih x hx (lc_at_openBVar_result
        (by simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2)
        (by simp [lc_at])))
  | congSigmaDom hA ih =>
    exact .sigma ∅ (ih (by simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1))
      (fun _ _ => parRed_refl _)
  | congSigmaCod L A B B' hB ih =>
    exact .sigma L (parRed_refl A) (fun x hx =>
      ih x hx (lc_at_openBVar_result
        (by simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2)
        (by simp [lc_at])))
  | congIdType hA ih =>
    exact .id (ih (by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1))
      (parRed_refl _) (parRed_refl _)
  | congIdLeft ha ih =>
    exact .id (parRed_refl _)
      (ih (by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.1))
      (parRed_refl _)
  | congIdRight hb ih =>
    exact .id (parRed_refl _) (parRed_refl _)
      (ih (by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.2))
  | congLam L body body' hB ih =>
    exact .lam L (fun x hx =>
      ih x hx (lc_at_openBVar_result
        (by simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc)
        (by simp [lc_at])))
  | congAppFun hf ih =>
    exact .app (ih (by simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1))
      (parRed_refl _)
  | congAppArg ha ih =>
    exact .app (parRed_refl _)
      (ih (by simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2))
  | congPairFst ha ih =>
    exact .pair (ih (by simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1))
      (parRed_refl _)
  | congPairSnd hb ih =>
    exact .pair (parRed_refl _)
      (ih (by simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2))
  | congFst hp ih =>
    exact .fst (ih (by simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))
  | congSnd hp ih =>
    exact .snd (ih (by simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))
  | congRefl ha ih =>
    exact .refl (ih (by simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))

/-! ### ParRed preserves local closure -/

theorem parRed_preserves_lc {p q : Pattern}
    (h : ParRed p q) (hlc : lc_at 0 p = true) : lc_at 0 q = true := by
  induction h with
  | bvar n => exact hlc
  | fvar x => exact hlc
  | pi L hA hB ihA ihB =>
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    constructor
    · exact ihA hlc.1
    · obtain ⟨x, hx⟩ := exists_fresh L
      have := ihB x hx (lc_at_openBVar_result hlc.2 (by simp [lc_at]))
      exact lc_at_of_openBVar this
  | sigma L hA hB ihA ihB =>
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    constructor
    · exact ihA hlc.1
    · obtain ⟨x, hx⟩ := exists_fresh L
      have := ihB x hx (lc_at_openBVar_result hlc.2 (by simp [lc_at]))
      exact lc_at_of_openBVar this
  | lam L hB ihB =>
    simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    obtain ⟨x, hx⟩ := exists_fresh L
    have := ihB x hx (lc_at_openBVar_result hlc (by simp [lc_at]))
    exact lc_at_of_openBVar this
  | app hf ha ihf iha =>
    simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ihf hlc.1, iha hlc.2⟩
  | pair ha hb iha ihb =>
    simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨iha hlc.1, ihb hlc.2⟩
  | fst hp ihp =>
    simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢; exact ihp hlc
  | snd hp ihp =>
    simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢; exact ihp hlc
  | id hA ha hb ihA iha ihb =>
    simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ihA hlc.1, iha hlc.2.1, ihb hlc.2.2⟩
  | refl ha iha =>
    simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢; exact iha hlc
  | betaPi L hbody ha hlcBody hlcA ihbody iha =>
    simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact lc_at_openBVar_result
      (by obtain ⟨x, hx⟩ := exists_fresh L
          have := ihbody x hx (lc_at_openBVar_result hlcBody (by simp [lc_at]))
          exact lc_at_of_openBVar this)
      (iha hlc.2)
  | betaSigmaFst ha hb iha ihb =>
    simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact iha hlc.1
  | betaSigmaSnd ha hb iha ihb =>
    simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact ihb hlc.2
  | refl_pat t => exact hlc

/-- Parallel reduction embeds into multi-step reduction. -/
theorem parRed_to_pureReducesStar {p q : Pattern} (h : ParRed p q)
    (hlc : lc_at 0 p = true) : PureReducesStar p q := by
  induction h with
  | bvar n => exact .refl _
  | fvar x => exact .refl _
  | @pi A A' B B' L hA hB ihA ihB =>
    have hlcA : lc_at 0 A = true := by
      simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB : lc_at 1 B = true := by
      simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    have hlcA' := parRed_preserves_lc hA hlcA
    have hlcB' : lc_at 1 B' = true := by
      obtain ⟨x, hx⟩ := exists_fresh L
      have := parRed_preserves_lc (hB x hx) (lc_at_openBVar_result hlcB (by simp [lc_at]))
      exact lc_at_of_openBVar this
    exact (PureReducesStar.congPiDom (ihA hlcA)).trans
      (PureReducesStar.congPiCodLC L hlcB hlcB' (fun x hx =>
        ihB x hx (lc_at_openBVar_result hlcB (by simp [lc_at]))))
  | @sigma A A' B B' L hA hB ihA ihB =>
    have hlcA : lc_at 0 A = true := by
      simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB : lc_at 1 B = true := by
      simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    have hlcB' : lc_at 1 B' = true := by
      obtain ⟨x, hx⟩ := exists_fresh L
      have := parRed_preserves_lc (hB x hx) (lc_at_openBVar_result hlcB (by simp [lc_at]))
      exact lc_at_of_openBVar this
    exact (PureReducesStar.congSigmaDom (ihA hlcA)).trans
      (PureReducesStar.congSigmaCodLC L hlcB hlcB' (fun x hx =>
        ihB x hx (lc_at_openBVar_result hlcB (by simp [lc_at]))))
  | @lam bd bd' L hB ihB =>
    have hlcB : lc_at 1 bd = true := by
      simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
    have hlcB' : lc_at 1 bd' = true := by
      obtain ⟨x, hx⟩ := exists_fresh L
      have := parRed_preserves_lc (hB x hx) (lc_at_openBVar_result hlcB (by simp [lc_at]))
      exact lc_at_of_openBVar this
    exact PureReducesStar.congLamLC L hlcB hlcB' (fun x hx =>
      ihB x hx (lc_at_openBVar_result hlcB (by simp [lc_at])))
  | app hf ha ihf iha =>
    have hlcF := by simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcA := by simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    exact PureReducesStar.congApp (ihf hlcF) (iha hlcA)
  | pair ha hb iha ihb =>
    have hlcA := by simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB := by simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    exact PureReducesStar.congPair (iha hlcA) (ihb hlcB)
  | fst hp ihp =>
    exact PureReducesStar.congFst (ihp (by simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))
  | snd hp ihp =>
    exact PureReducesStar.congSnd (ihp (by simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))
  | id hA ha hb ihA iha ihb =>
    have hlcA := by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlca := by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.1
    have hlcb := by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.2
    exact PureReducesStar.congId (ihA hlcA) (iha hlca) (ihb hlcb)
  | refl ha iha =>
    exact PureReducesStar.congRefl (iha (by simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))
  | @betaPi bd bd' ar ar' L hbody ha hlcBody hlcA ihbody iha =>
    have hlcFull := hlc
    simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    have hlcBody' : lc_at 1 bd' = true := by
      obtain ⟨x, hx⟩ := exists_fresh L
      have := parRed_preserves_lc (hbody x hx) (lc_at_openBVar_result hlcBody (by simp [lc_at]))
      exact lc_at_of_openBVar this
    exact (PureReducesStar.congApp
        (PureReducesStar.congLamLC L hlcBody hlcBody' (fun x hx =>
          ihbody x hx (lc_at_openBVar_result hlcBody (by simp [lc_at]))))
        (iha hlc.2)).trans
      (.single (.betaPi bd' ar'))
  | @betaSigmaFst ar ar' br br' ha hb iha ihb =>
    simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact (PureReducesStar.congFst (PureReducesStar.congPair (iha hlc.1) (ihb hlc.2))).trans
      (.single (.betaSigmaFst ar' br'))
  | @betaSigmaSnd ar ar' br br' ha hb iha ihb =>
    simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact (PureReducesStar.congSnd (PureReducesStar.congPair (iha hlc.1) (ihb hlc.2))).trans
      (.single (.betaSigmaSnd ar' br'))
  | refl_pat t => exact .refl _

/-! ### ParRed inversion lemmas -/

/-- Inversion for ParRed on mkLam: the result is always mkLam of a related body. -/
theorem parRed_lam_inv {body t : Pattern} (h : ParRed (mkLam body) t)
    (_hlc : lc_at 0 (mkLam body) = true) :
    (∃ bd' : Pattern, ∃ L : Finset String, t = mkLam bd' ∧
      ∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) bd')) ∨
    t = mkLam body := by
  generalize heq : mkLam body = s at h
  cases h with
  | bvar n => simp [mkLam] at heq
  | fvar x => simp [mkLam] at heq
  | pi _ _ _ => simp [mkLam, mkPi] at heq
  | sigma _ _ _ => simp [mkLam, mkSigma] at heq
  | lam L hB =>
    simp [mkLam] at heq; obtain ⟨rfl⟩ := heq
    left; exact ⟨_, L, rfl, hB⟩
  | app _ _ => simp [mkLam, mkApp] at heq
  | pair _ _ => simp [mkLam, mkPair] at heq
  | fst _ => simp [mkLam, mkFst] at heq
  | snd _ => simp [mkLam, mkSnd] at heq
  | id _ _ _ => simp [mkLam, mkId] at heq
  | refl _ => simp [mkLam, mkRefl] at heq
  | betaPi _ _ _ _ _ => simp [mkLam, mkApp] at heq
  | betaSigmaFst _ _ => simp [mkLam, mkFst] at heq
  | betaSigmaSnd _ _ => simp [mkLam, mkSnd] at heq
  | refl_pat t => subst heq; right; rfl

/-- Inversion for ParRed on mkPair. -/
theorem parRed_pair_inv {a b t : Pattern} (h : ParRed (mkPair a b) t)
    (_hlc : lc_at 0 (mkPair a b) = true) :
    (∃ a' b', t = mkPair a' b' ∧ ParRed a a' ∧ ParRed b b') ∨
    t = mkPair a b := by
  generalize heq : mkPair a b = s at h
  cases h with
  | bvar n => simp [mkPair] at heq
  | fvar x => simp [mkPair] at heq
  | pi _ _ _ => simp [mkPair, mkPi] at heq
  | sigma _ _ _ => simp [mkPair, mkSigma] at heq
  | lam _ _ => simp [mkPair, mkLam] at heq
  | app _ _ => simp [mkPair, mkApp] at heq
  | pair ha hb =>
    simp [mkPair] at heq; obtain ⟨rfl, rfl⟩ := heq
    left; exact ⟨_, _, rfl, ha, hb⟩
  | fst _ => simp [mkPair, mkFst] at heq
  | snd _ => simp [mkPair, mkSnd] at heq
  | id _ _ _ => simp [mkPair, mkId] at heq
  | refl _ => simp [mkPair, mkRefl] at heq
  | betaPi _ _ _ _ _ => simp [mkPair, mkApp] at heq
  | betaSigmaFst _ _ => simp [mkPair, mkFst] at heq
  | betaSigmaSnd _ _ => simp [mkPair, mkSnd] at heq
  | refl_pat _ => subst heq; right; rfl

/-- Rewrite `substFVar x (fvar y) (openBVar 0 (fvar x) B) = openBVar 0 (fvar y) B`
    when `x` is fresh in `B`. Uses `substFVar_openBVar_comm` + `substFVar_fresh`. -/
private theorem subst_open_self_var
    {x y : String} {B : Pattern} (hfresh : isFresh x B = true) :
    substFVar x (.fvar y) (openBVar 0 (.fvar x) B) = openBVar 0 (.fvar y) B := by
  rw [substFVar_openBVar_comm (by simp [lc_at] : lc_at 0 (.fvar y) = true)]
  simp [substFVar_fresh hfresh]

/-! ### Diamond Property -/

/-- Diamond property for ParRed (for locally closed terms).
    Proved by induction on `h₁`, generalizing `t₂` and `h₂`. -/
theorem diamond_parRed {s t₁ t₂ : Pattern}
    (hlc : lc_at 0 s = true)
    (h₁ : ParRed s t₁) (h₂ : ParRed s t₂)
    (hpure : PureTmPattern s) :
    ∃ w, ParRed t₁ w ∧ ParRed t₂ w := by
  revert hpure
  induction h₁ generalizing t₂ with
  | refl_pat _ =>
    intro hpure
    exact ⟨t₂, h₂, parRed_refl t₂⟩
  | bvar n =>
    intro hpure
    cases hpure
    cases h₂ with
    | bvar _ => exact ⟨_, .bvar n, .bvar n⟩
    | refl_pat _ => exact ⟨_, parRed_refl _, .bvar n⟩
  | fvar x =>
    intro hpure
    cases hpure
    cases h₂ with
    | fvar _ => exact ⟨_, .fvar x, .fvar x⟩
    | refl_pat _ => exact ⟨_, parRed_refl _, .fvar x⟩
  | @pi A A' B B' L₁ hA₁ hB₁ ihA ihB =>
    intro hpure
    let hAB := pure_pi_inv hpure
    have hlcA : lc_at 0 A = true := by
      simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB : lc_at 1 B = true := by
      simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    generalize heq : mkPi A B = s' at h₂
    cases h₂ with
    | @pi _ _ A₂ B₂ L₂ hA₂ hB₂ =>
      simp [mkPi] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨wA, hwA₁, hwA₂⟩ := ihA hlcA hA₂ hAB.1
      -- Codomain: pick fresh x₀, use IH, close
      set Lall := L₁ ∪ L₂ ∪ listToFinset (freeVars B') ∪ listToFinset (freeVars B₂)
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lall
      have hx₀L₁ : x₀ ∉ L₁ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
      have hx₀L₂ : x₀ ∉ L₂ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hlcOpen := lc_at_openBVar_result hlcB (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨wBx₀, hwB₁, hwB₂⟩ := ihB x₀ hx₀L₁ hlcOpen (hB₂ x₀ hx₀L₂)
        (pureTm_openBVar_fvar x₀ hAB.2)
      -- Close wBx₀ back
      set wB := closeBVar 0 x₀ wBx₀
      have hlcWBx₀ := parRed_preserves_lc hwB₁
        (parRed_preserves_lc (hB₁ x₀ hx₀L₁) hlcOpen)
      have hopen_wB : openBVar 0 (.fvar x₀) wB = wBx₀ := openBVar_closeBVar_cancel hlcWBx₀
      have hfreshB' := isFresh_of_not_in_freeVars_finset (p := B') (fun h =>
        hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hfreshB₂ := isFresh_of_not_in_freeVars_finset (p := B₂) (fun h =>
        hx₀ (Finset.mem_union_right _ h))
      have hfreshWB : isFresh x₀ wB = true := isFresh_closeBVar 0 x₀ wBx₀
      refine ⟨mkPi wA wB, .pi (L₁ ∪ {x₀}) hwA₁ (fun y hy => ?_),
                            .pi (L₂ ∪ {x₀}) hwA₂ (fun y hy => ?_)⟩
      · have hyL₁ : y ∉ L₁ := fun h => hy (Finset.mem_union_left _ h)
        have key := parRed_substFVar_same (x := x₀) (u := .fvar y) (by simp [lc_at]) hwB₁
        rwa [subst_open_self_var hfreshB',
             show substFVar x₀ (.fvar y) wBx₀ = openBVar 0 (.fvar y) wB from by
              rw [← hopen_wB]; exact substFVar_intro wB hfreshWB 0] at key
      · have hyL₂ : y ∉ L₂ := fun h => hy (Finset.mem_union_left _ h)
        have key := parRed_substFVar_same (x := x₀) (u := .fvar y) (by simp [lc_at]) hwB₂
        rwa [subst_open_self_var hfreshB₂,
             show substFVar x₀ (.fvar y) wBx₀ = openBVar 0 (.fvar y) wB from by
              rw [← hopen_wB]; exact substFVar_intro wB hfreshWB 0] at key
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .pi L₁ hA₁ hB₁⟩
    | _ => simp [mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at heq
  | @sigma A A' B B' L₁ hA₁ hB₁ ihA ihB =>
    intro hpure
    let hAB := pure_sigma_inv hpure
    have hlcA : lc_at 0 A = true := by
      simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB : lc_at 1 B = true := by
      simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    generalize heq : mkSigma A B = s' at h₂
    cases h₂ with
    | @sigma _ _ A₂ B₂ L₂ hA₂ hB₂ =>
      simp [mkSigma] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨wA, hwA₁, hwA₂⟩ := ihA hlcA hA₂ hAB.1
      set Lall := L₁ ∪ L₂ ∪ listToFinset (freeVars B') ∪ listToFinset (freeVars B₂)
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lall
      have hx₀L₁ : x₀ ∉ L₁ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
      have hx₀L₂ : x₀ ∉ L₂ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hlcOpen := lc_at_openBVar_result hlcB (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨wBx₀, hwB₁, hwB₂⟩ := ihB x₀ hx₀L₁ hlcOpen (hB₂ x₀ hx₀L₂)
        (pureTm_openBVar_fvar x₀ hAB.2)
      set wB := closeBVar 0 x₀ wBx₀
      have hlcWBx₀ := parRed_preserves_lc hwB₁
        (parRed_preserves_lc (hB₁ x₀ hx₀L₁) hlcOpen)
      have hopen_wB : openBVar 0 (.fvar x₀) wB = wBx₀ := openBVar_closeBVar_cancel hlcWBx₀
      have hfreshB' := isFresh_of_not_in_freeVars_finset (p := B') (fun h =>
        hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hfreshB₂ := isFresh_of_not_in_freeVars_finset (p := B₂) (fun h =>
        hx₀ (Finset.mem_union_right _ h))
      have hfreshWB : isFresh x₀ wB = true := isFresh_closeBVar 0 x₀ wBx₀
      refine ⟨mkSigma wA wB, .sigma (L₁ ∪ {x₀}) hwA₁ (fun y hy => ?_),
                               .sigma (L₂ ∪ {x₀}) hwA₂ (fun y hy => ?_)⟩
      · have hyL₁ : y ∉ L₁ := fun h => hy (Finset.mem_union_left _ h)
        have key := parRed_substFVar_same (x := x₀) (u := .fvar y) (by simp [lc_at]) hwB₁
        rwa [subst_open_self_var hfreshB',
             show substFVar x₀ (.fvar y) wBx₀ = openBVar 0 (.fvar y) wB from by
              rw [← hopen_wB]; exact substFVar_intro wB hfreshWB 0] at key
      · have hyL₂ : y ∉ L₂ := fun h => hy (Finset.mem_union_left _ h)
        have key := parRed_substFVar_same (x := x₀) (u := .fvar y) (by simp [lc_at]) hwB₂
        rwa [subst_open_self_var hfreshB₂,
             show substFVar x₀ (.fvar y) wBx₀ = openBVar 0 (.fvar y) wB from by
              rw [← hopen_wB]; exact substFVar_intro wB hfreshWB 0] at key
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .sigma L₁ hA₁ hB₁⟩
    | _ => simp [mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at heq
  | @lam bd bd' L₁ hbd₁ ihbd =>
    intro hpure
    have hPureBd : PureTmPattern bd := pure_lam_inv hpure
    have hlcBody : lc_at 1 bd = true := by
      simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
    generalize heq : mkLam bd = s' at h₂
    cases h₂ with
    | @lam _ bd₂' L₂ hbd₂ =>
      simp [mkLam] at heq; obtain ⟨rfl⟩ := heq
      set Lall := L₁ ∪ L₂ ∪ listToFinset (freeVars bd') ∪ listToFinset (freeVars bd₂')
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lall
      have hx₀L₁ : x₀ ∉ L₁ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
      have hx₀L₂ : x₀ ∉ L₂ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hlcOpen := lc_at_openBVar_result hlcBody (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨wBx₀, hwB₁, hwB₂⟩ := ihbd x₀ hx₀L₁ hlcOpen (hbd₂ x₀ hx₀L₂)
        (pureTm_openBVar_fvar x₀ hPureBd)
      set wB := closeBVar 0 x₀ wBx₀
      have hlcWBx₀ := parRed_preserves_lc hwB₁
        (parRed_preserves_lc (hbd₁ x₀ hx₀L₁) hlcOpen)
      have hopen_wB : openBVar 0 (.fvar x₀) wB = wBx₀ := openBVar_closeBVar_cancel hlcWBx₀
      have hfreshBd' := isFresh_of_not_in_freeVars_finset (p := bd') (fun h =>
        hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hfreshBd₂ := isFresh_of_not_in_freeVars_finset (p := bd₂') (fun h =>
        hx₀ (Finset.mem_union_right _ h))
      have hfreshWB : isFresh x₀ wB = true := isFresh_closeBVar 0 x₀ wBx₀
      refine ⟨mkLam wB, .lam (L₁ ∪ {x₀}) (fun y hy => ?_),
                          .lam (L₂ ∪ {x₀}) (fun y hy => ?_)⟩
      · have hyL₁ : y ∉ L₁ := fun h => hy (Finset.mem_union_left _ h)
        have key := parRed_substFVar_same (x := x₀) (u := .fvar y) (by simp [lc_at]) hwB₁
        rwa [subst_open_self_var hfreshBd',
             show substFVar x₀ (.fvar y) wBx₀ = openBVar 0 (.fvar y) wB from by
              rw [← hopen_wB]; exact substFVar_intro wB hfreshWB 0] at key
      · have hyL₂ : y ∉ L₂ := fun h => hy (Finset.mem_union_left _ h)
        have key := parRed_substFVar_same (x := x₀) (u := .fvar y) (by simp [lc_at]) hwB₂
        rwa [subst_open_self_var hfreshBd₂,
             show substFVar x₀ (.fvar y) wBx₀ = openBVar 0 (.fvar y) wB from by
              rw [← hopen_wB]; exact substFVar_intro wB hfreshWB 0] at key
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .lam L₁ hbd₁⟩
    | _ => simp [mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl] at heq
  | @app f f' a a' hf₁ ha₁ ihf iha =>
    intro hpure
    have hPureFA : PureTmPattern f ∧ PureTmPattern a := pure_app_inv hpure
    have hlcF : lc_at 0 f = true := by
      simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcA : lc_at 0 a = true := by
      simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    generalize heq : mkApp f a = s' at h₂
    cases h₂ with
    | @app _ _ _ _ hf₂ ha₂ =>
      simp [mkApp] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨wf, hwf₁, hwf₂⟩ := ihf hlcF hf₂ hPureFA.1
      obtain ⟨wa, hwa₁, hwa₂⟩ := iha hlcA ha₂ hPureFA.2
      exact ⟨mkApp wf wa, .app hwf₁ hwa₁, .app hwf₂ hwa₂⟩
    | @betaPi bodyS_h bodyS_t aS_h aS_t L₂ hbody₂ ha₂ hlcBody₂ hlcA₂ =>
      -- source = mkApp (mkLam bodyS_h) aS_h; h₁ is app, h₂ is betaPi
      -- After simp: f = mkLam bodyS_h, a = aS_h
      -- t₁ = mkApp f' a', t₂ = openBVar 0 aS_t bodyS_t
      simp [mkApp] at heq; obtain ⟨rfl, rfl⟩ := heq
      have hlcBodyS_h : lc_at 1 bodyS_h = true := by
        simp [mkLam, lc_at, lc_at_list] at hlcF; exact hlcF
      have hPureBodyS_h : PureTmPattern bodyS_h := by
        have hPureLam : PureTmPattern (mkLam bodyS_h) := by
          simpa [mkLam] using hPureFA.1
        exact pure_lam_inv hPureLam
      set SPureT := L₂ ∪ listToFinset (freeVars bodyS_t)
      obtain ⟨xt, hxt⟩ := exists_fresh SPureT
      have hxtL₂ : xt ∉ L₂ := fun hmem => hxt (Finset.mem_union_left _ hmem)
      have hxtB : xt ∉ listToFinset (freeVars bodyS_t) := fun hmem => hxt (Finset.mem_union_right _ hmem)
      have hOpenSrc_t : PureTmPattern (openBVar 0 (.fvar xt) bodyS_h) :=
        pureTm_openBVar_fvar xt hPureBodyS_h
      have hOpenTgt_t : PureTmPattern (openBVar 0 (.fvar xt) bodyS_t) :=
        parRed_preserves_pure (hbody₂ xt hxtL₂) hOpenSrc_t
      have hPureBodyS_t : PureTmPattern bodyS_t :=
        pureTm_of_openBVar_fresh xt hOpenTgt_t (isFresh_of_not_in_freeVars_finset (p := bodyS_t) hxtB)
      have hlcA' := parRed_preserves_lc ha₁ hlcA
      have hlcA₂' := parRed_preserves_lc ha₂ hlcA
      obtain ⟨wa, hwa₁, hwa₂⟩ := iha hlcA ha₂ hPureFA.2
      obtain ⟨wf, hwf₁, hwf₂⟩ := ihf hlcF (.lam L₂ hbody₂) hPureFA.1
      -- lam_inv on hf₁ : ParRed (mkLam bodyS_h) f' to establish f' = mkLam ...
      have hlcF_t : lc_at 0 (mkLam bodyS_t) = true := parRed_preserves_lc (.lam L₂ hbody₂) hlcF
      obtain ⟨body_f', Lf', hf₁_eq, hf₁_bd⟩ | hf₁_eq := parRed_lam_inv hf₁ hlcF
      · -- f' = mkLam body_f'; hwf₁ : ParRed (mkLam body_f') wf
        subst hf₁_eq
        have hlcBd_f' : lc_at 1 body_f' = true := by
          have h := parRed_preserves_lc hf₁ hlcF
          simp [mkLam, lc_at, lc_at_list] at h; exact h
        have hlcF' : lc_at 0 (mkLam body_f') = true := parRed_preserves_lc hf₁ hlcF
        obtain ⟨wbd, Lwf₁, hwf₁_eq, hwf₁_bd⟩ | hwf₁_eq := parRed_lam_inv hwf₁ hlcF'
        · subst hwf₁_eq  -- wf = mkLam wbd
          obtain ⟨wbd₂, Lwf₂, hwf₂_eq, hwf₂_bd⟩ | hwf₂_eq := parRed_lam_inv hwf₂ hlcF_t
          · simp [mkLam] at hwf₂_eq; obtain ⟨rfl⟩ := hwf₂_eq  -- wbd₂ = wbd
            exact ⟨openBVar 0 wa wbd,
              .betaPi Lwf₁ hwf₁_bd hwa₁ hlcBd_f' hlcA',
              parRed_openBVar Lwf₂ hwf₂_bd hPureBodyS_t hwa₂ hlcA₂' (parRed_preserves_lc hwa₂ hlcA₂')⟩
          · simp [mkLam] at hwf₂_eq; obtain ⟨rfl⟩ := hwf₂_eq  -- wbd = bodyS_t
            exact ⟨openBVar 0 wa bodyS_t,
              .betaPi Lwf₁ hwf₁_bd hwa₁ hlcBd_f' hlcA',
              parRed_openBVar ∅ (fun x _ => parRed_refl _) hPureBodyS_t hwa₂ hlcA₂' (parRed_preserves_lc hwa₂ hlcA₂')⟩
        · subst hwf₁_eq  -- wf = mkLam body_f' (refl of hwf₁)
          obtain ⟨wbd₂, Lwf₂, hwf₂_eq, hwf₂_bd⟩ | hwf₂_eq := parRed_lam_inv hwf₂ hlcF_t
          · simp [mkLam] at hwf₂_eq; obtain ⟨rfl⟩ := hwf₂_eq  -- wbd₂ = body_f'
            exact ⟨openBVar 0 wa body_f',
              .betaPi ∅ (fun x _ => parRed_refl _) hwa₁ hlcBd_f' hlcA',
              parRed_openBVar Lwf₂ hwf₂_bd hPureBodyS_t hwa₂ hlcA₂' (parRed_preserves_lc hwa₂ hlcA₂')⟩
          · simp [mkLam] at hwf₂_eq; obtain ⟨rfl⟩ := hwf₂_eq  -- body_f' = bodyS_t
            exact ⟨openBVar 0 wa bodyS_t,
              .betaPi ∅ (fun x _ => parRed_refl _) hwa₁ hlcBd_f' hlcA',
              parRed_openBVar ∅ (fun x _ => parRed_refl _) hPureBodyS_t hwa₂ hlcA₂' (parRed_preserves_lc hwa₂ hlcA₂')⟩
      · -- f' = mkLam bodyS_h (refl of lam_inv hf₁); hwf₁ : ParRed (mkLam bodyS_h) wf
        subst hf₁_eq
        obtain ⟨wbd, Lwf₁, hwf₁_eq, hwf₁_bd⟩ | hwf₁_eq := parRed_lam_inv hwf₁ hlcF
        · subst hwf₁_eq  -- wf = mkLam wbd
          obtain ⟨wbd₂, Lwf₂, hwf₂_eq, hwf₂_bd⟩ | hwf₂_eq := parRed_lam_inv hwf₂ hlcF_t
          · simp [mkLam] at hwf₂_eq; obtain ⟨rfl⟩ := hwf₂_eq  -- wbd₂ = wbd
            exact ⟨openBVar 0 wa wbd,
              .betaPi Lwf₁ hwf₁_bd hwa₁ hlcBodyS_h hlcA',
              parRed_openBVar Lwf₂ hwf₂_bd hPureBodyS_t hwa₂ hlcA₂' (parRed_preserves_lc hwa₂ hlcA₂')⟩
          · simp [mkLam] at hwf₂_eq; obtain ⟨rfl⟩ := hwf₂_eq  -- wbd = bodyS_t
            exact ⟨openBVar 0 wa bodyS_t,
              .betaPi Lwf₁ hwf₁_bd hwa₁ hlcBodyS_h hlcA',
              parRed_openBVar ∅ (fun x _ => parRed_refl _) hPureBodyS_t hwa₂ hlcA₂' (parRed_preserves_lc hwa₂ hlcA₂')⟩
        · subst hwf₁_eq  -- wf = mkLam bodyS_h (refl of hwf₁)
          obtain ⟨wbd₂, Lwf₂, hwf₂_eq, hwf₂_bd⟩ | hwf₂_eq := parRed_lam_inv hwf₂ hlcF_t
          · simp [mkLam] at hwf₂_eq; obtain ⟨rfl⟩ := hwf₂_eq  -- wbd₂ = bodyS_h
            exact ⟨openBVar 0 wa bodyS_h,
              .betaPi ∅ (fun x _ => parRed_refl _) hwa₁ hlcBodyS_h hlcA',
              parRed_openBVar Lwf₂ hwf₂_bd hPureBodyS_t hwa₂ hlcA₂' (parRed_preserves_lc hwa₂ hlcA₂')⟩
          · simp [mkLam] at hwf₂_eq; obtain ⟨rfl⟩ := hwf₂_eq  -- bodyS_h = bodyS_t
            exact ⟨openBVar 0 wa bodyS_h,
              .betaPi ∅ (fun x _ => parRed_refl _) hwa₁ hlcBodyS_h hlcA',
              parRed_openBVar ∅ (fun x _ => parRed_refl _) hPureBodyS_t hwa₂ hlcA₂' (parRed_preserves_lc hwa₂ hlcA₂')⟩
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .app hf₁ ha₁⟩
    | _ => simp [mkApp, mkPi, mkSigma, mkLam, mkPair, mkFst, mkSnd, mkId, mkRefl] at heq
  | @pair a a' b b' ha₁ hb₁ iha ihb =>
    intro hpure
    let hab := pure_pair_inv hpure
    have hlcA : lc_at 0 a = true := by
      simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB : lc_at 0 b = true := by
      simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    generalize heq : mkPair a b = s' at h₂
    cases h₂ with
    | @pair _ _ _ _ ha₂ hb₂ =>
      simp [mkPair] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨wa, hwa₁, hwa₂⟩ := iha hlcA ha₂ hab.1
      obtain ⟨wb, hwb₁, hwb₂⟩ := ihb hlcB hb₂ hab.2
      exact ⟨mkPair wa wb, .pair hwa₁ hwb₁, .pair hwa₂ hwb₂⟩
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .pair ha₁ hb₁⟩
    | _ => simp [mkPair, mkPi, mkSigma, mkLam, mkApp, mkFst, mkSnd, mkId, mkRefl] at heq
  | @fst p p' hp₁ ihp =>
    intro hpure
    have hPureP : PureTmPattern p := pure_fst_inv hpure
    have hlcP : lc_at 0 p = true := by
      simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
    generalize heq : mkFst p = s' at h₂
    cases h₂ with
    | @fst _ _ hp₂ =>
      simp [mkFst] at heq; obtain ⟨rfl⟩ := heq
      obtain ⟨wp, hwp₁, hwp₂⟩ := ihp hlcP hp₂ hPureP
      exact ⟨mkFst wp, .fst hwp₁, .fst hwp₂⟩
    | @betaSigmaFst a_s a_s' b_s b_s' ha₂ hb₂ =>
      -- source = mkFst (mkPair a_s b_s); h₁ is fst, h₂ is betaSigmaFst
      -- t₁ = mkFst p', t₂ = a_s'
      simp [mkFst] at heq; obtain ⟨rfl⟩ := heq
      -- p = mkPair a_s b_s; hp₁ : ParRed (mkPair a_s b_s) p'
      obtain ⟨wp, hwp₁, hwp₂⟩ := ihp hlcP (.pair ha₂ hb₂) hPureP
      -- hwp₁ : ParRed p' wp, hwp₂ : ParRed (mkPair a_s' b_s') wp
      obtain ⟨pa', pb', hp₁_eq, hpa', hpb'⟩ | hp₁_eq := parRed_pair_inv hp₁ hlcP
      · -- p' = mkPair pa' pb'
        subst hp₁_eq
        obtain ⟨wpa, wpb, hwp₂_eq, hrel_a, hrel_b⟩ | hwp₂_eq :=
            parRed_pair_inv hwp₂ (parRed_preserves_lc (.pair ha₂ hb₂) hlcP)
        · subst hwp₂_eq  -- wp = mkPair wpa wpb
          obtain ⟨wpa', wpb', hwp₁_eq, hpa'_rel, hpb'_rel⟩ | hwp₁_eq :=
              parRed_pair_inv hwp₁ (parRed_preserves_lc hp₁ hlcP)
          · simp [mkPair] at hwp₁_eq; obtain ⟨rfl, rfl⟩ := hwp₁_eq
            exact ⟨wpa, .betaSigmaFst hpa'_rel hpb'_rel, hrel_a⟩
          · simp [mkPair] at hwp₁_eq; obtain ⟨rfl, rfl⟩ := hwp₁_eq
            exact ⟨wpa, .betaSigmaFst (parRed_refl wpa) (parRed_refl wpb), hrel_a⟩
        · subst hwp₂_eq  -- wp = mkPair a_s' b_s' (refl of hwp₂)
          obtain ⟨wpa', wpb', hwp₁_eq, hpa'_rel, hpb'_rel⟩ | hwp₁_eq :=
              parRed_pair_inv hwp₁ (parRed_preserves_lc hp₁ hlcP)
          · simp [mkPair] at hwp₁_eq; obtain ⟨ha, hb⟩ := hwp₁_eq; subst ha; subst hb
            exact ⟨_, .betaSigmaFst hpa'_rel hpb'_rel, parRed_refl _⟩
          · simp [mkPair] at hwp₁_eq; obtain ⟨ha, hb⟩ := hwp₁_eq; subst ha; subst hb
            exact ⟨_, .betaSigmaFst (parRed_refl _) (parRed_refl _), parRed_refl _⟩
      · -- p' = mkPair a_s b_s (refl of hp₁)
        subst hp₁_eq
        obtain ⟨wpa, wpb, hwp₂_eq, hrel_a, hrel_b⟩ | hwp₂_eq :=
            parRed_pair_inv hwp₂ (parRed_preserves_lc (.pair ha₂ hb₂) hlcP)
        · subst hwp₂_eq  -- wp = mkPair wpa wpb
          obtain ⟨wpa', wpb', hwp₁_eq, hpar_a, hpar_b⟩ | hwp₁_eq :=
              parRed_pair_inv hwp₁ hlcP
          · simp [mkPair] at hwp₁_eq; obtain ⟨rfl, rfl⟩ := hwp₁_eq
            exact ⟨wpa, .betaSigmaFst hpar_a hpar_b, hrel_a⟩
          · simp [mkPair] at hwp₁_eq; obtain ⟨rfl, rfl⟩ := hwp₁_eq
            exact ⟨wpa, .betaSigmaFst (parRed_refl wpa) (parRed_refl wpb), hrel_a⟩
        · subst hwp₂_eq  -- wp = mkPair a_s' b_s' (refl of hwp₂)
          obtain ⟨wpa', wpb', hwp₁_eq, hpar_a, hpar_b⟩ | hwp₁_eq :=
              parRed_pair_inv hwp₁ hlcP
          · simp [mkPair] at hwp₁_eq; obtain ⟨ha, hb⟩ := hwp₁_eq; subst ha; subst hb
            exact ⟨_, .betaSigmaFst hpar_a hpar_b, parRed_refl _⟩
          · simp [mkPair] at hwp₁_eq; obtain ⟨ha, hb⟩ := hwp₁_eq; subst ha; subst hb
            exact ⟨_, .betaSigmaFst (parRed_refl _) (parRed_refl _), parRed_refl _⟩
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .fst hp₁⟩
    | _ => simp [mkFst, mkPi, mkSigma, mkLam, mkApp, mkPair, mkSnd, mkId, mkRefl] at heq
  | @snd p p' hp₁ ihp =>
    intro hpure
    have hPureP : PureTmPattern p := pure_snd_inv hpure
    have hlcP : lc_at 0 p = true := by
      simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
    generalize heq : mkSnd p = s' at h₂
    cases h₂ with
    | @snd _ _ hp₂ =>
      simp [mkSnd] at heq; obtain ⟨rfl⟩ := heq
      obtain ⟨wp, hwp₁, hwp₂⟩ := ihp hlcP hp₂ hPureP
      exact ⟨mkSnd wp, .snd hwp₁, .snd hwp₂⟩
    | @betaSigmaSnd a_s a_s' b_s b_s' ha₂ hb₂ =>
      -- source = mkSnd (mkPair a_s b_s); h₁ is snd, h₂ is betaSigmaSnd
      -- t₁ = mkSnd p', t₂ = b_s'
      simp [mkSnd] at heq; obtain ⟨rfl⟩ := heq
      -- p = mkPair a_s b_s; hp₁ : ParRed (mkPair a_s b_s) p'
      obtain ⟨wp, hwp₁, hwp₂⟩ := ihp hlcP (.pair ha₂ hb₂) hPureP
      -- hwp₁ : ParRed p' wp, hwp₂ : ParRed (mkPair a_s' b_s') wp
      obtain ⟨pa', pb', hp₁_eq, hpa', hpb'⟩ | hp₁_eq := parRed_pair_inv hp₁ hlcP
      · -- p' = mkPair pa' pb'
        subst hp₁_eq
        obtain ⟨wpa, wpb, hwp₂_eq, hrel_a, hrel_b⟩ | hwp₂_eq :=
            parRed_pair_inv hwp₂ (parRed_preserves_lc (.pair ha₂ hb₂) hlcP)
        · subst hwp₂_eq  -- wp = mkPair wpa wpb
          obtain ⟨wpa', wpb', hwp₁_eq, hpa'_rel, hpb'_rel⟩ | hwp₁_eq :=
              parRed_pair_inv hwp₁ (parRed_preserves_lc hp₁ hlcP)
          · simp [mkPair] at hwp₁_eq; obtain ⟨rfl, rfl⟩ := hwp₁_eq
            exact ⟨wpb, .betaSigmaSnd hpa'_rel hpb'_rel, hrel_b⟩
          · simp [mkPair] at hwp₁_eq; obtain ⟨rfl, rfl⟩ := hwp₁_eq
            exact ⟨wpb, .betaSigmaSnd (parRed_refl wpa) (parRed_refl wpb), hrel_b⟩
        · subst hwp₂_eq  -- wp = mkPair a_s' b_s' (refl of hwp₂)
          obtain ⟨wpa', wpb', hwp₁_eq, hpa'_rel, hpb'_rel⟩ | hwp₁_eq :=
              parRed_pair_inv hwp₁ (parRed_preserves_lc hp₁ hlcP)
          · simp [mkPair] at hwp₁_eq; obtain ⟨ha, hb⟩ := hwp₁_eq; subst ha; subst hb
            exact ⟨_, .betaSigmaSnd hpa'_rel hpb'_rel, parRed_refl _⟩
          · simp [mkPair] at hwp₁_eq; obtain ⟨ha, hb⟩ := hwp₁_eq; subst ha; subst hb
            exact ⟨_, .betaSigmaSnd (parRed_refl _) (parRed_refl _), parRed_refl _⟩
      · -- p' = mkPair a_s b_s (refl of hp₁)
        subst hp₁_eq
        obtain ⟨wpa, wpb, hwp₂_eq, hrel_a, hrel_b⟩ | hwp₂_eq :=
            parRed_pair_inv hwp₂ (parRed_preserves_lc (.pair ha₂ hb₂) hlcP)
        · subst hwp₂_eq  -- wp = mkPair wpa wpb
          obtain ⟨wpa', wpb', hwp₁_eq, hpar_a, hpar_b⟩ | hwp₁_eq :=
              parRed_pair_inv hwp₁ hlcP
          · simp [mkPair] at hwp₁_eq; obtain ⟨rfl, rfl⟩ := hwp₁_eq
            exact ⟨wpb, .betaSigmaSnd hpar_a hpar_b, hrel_b⟩
          · simp [mkPair] at hwp₁_eq; obtain ⟨rfl, rfl⟩ := hwp₁_eq
            exact ⟨wpb, .betaSigmaSnd (parRed_refl wpa) (parRed_refl wpb), hrel_b⟩
        · subst hwp₂_eq  -- wp = mkPair a_s' b_s' (refl of hwp₂)
          obtain ⟨wpa', wpb', hwp₁_eq, hpar_a, hpar_b⟩ | hwp₁_eq :=
              parRed_pair_inv hwp₁ hlcP
          · simp [mkPair] at hwp₁_eq; obtain ⟨ha, hb⟩ := hwp₁_eq; subst ha; subst hb
            exact ⟨_, .betaSigmaSnd hpar_a hpar_b, parRed_refl _⟩
          · simp [mkPair] at hwp₁_eq; obtain ⟨ha, hb⟩ := hwp₁_eq; subst ha; subst hb
            exact ⟨_, .betaSigmaSnd (parRed_refl _) (parRed_refl _), parRed_refl _⟩
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .snd hp₁⟩
    | _ => simp [mkSnd, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkId, mkRefl] at heq
  | @id A A' a a' b b' hA₁ ha₁ hb₁ ihA iha ihb =>
    intro hpure
    let hId := pure_id_inv hpure
    have hlcA : lc_at 0 A = true := by
      simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlca : lc_at 0 a = true := by
      simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.1
    have hlcb : lc_at 0 b = true := by
      simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.2
    generalize heq : mkId A a b = s' at h₂
    cases h₂ with
    | @id _ _ _ _ _ _ hA₂ ha₂ hb₂ =>
      simp [mkId] at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
      obtain ⟨wA, hwA₁, hwA₂⟩ := ihA hlcA hA₂ hId.1
      obtain ⟨wa, hwa₁, hwa₂⟩ := iha hlca ha₂ hId.2.1
      obtain ⟨wb, hwb₁, hwb₂⟩ := ihb hlcb hb₂ hId.2.2
      exact ⟨mkId wA wa wb, .id hwA₁ hwa₁ hwb₁, .id hwA₂ hwa₂ hwb₂⟩
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .id hA₁ ha₁ hb₁⟩
    | _ => simp [mkId, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl] at heq
  | @refl a a' ha₁ iha =>
    intro hpure
    have hPureA : PureTmPattern a := pure_refl_inv hpure
    have hlcA : lc_at 0 a = true := by
      simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
    generalize heq : mkRefl a = s' at h₂
    cases h₂ with
    | @refl _ _ ha₂ =>
      simp [mkRefl] at heq; obtain ⟨rfl⟩ := heq
      obtain ⟨wa, hwa₁, hwa₂⟩ := iha hlcA ha₂ hPureA
      exact ⟨mkRefl wa, .refl hwa₁, .refl hwa₂⟩
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .refl ha₁⟩
    | _ => simp [mkRefl, mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId] at heq
  | @betaPi bodyS bodyS' aS aS' L₁ hbody₁ ha₁ hlcBodyS hlcAS ihbody iha =>
    intro hpure
    -- source is mkApp (mkLam bodyS) aS
    have hPureApp : PureTmPattern (mkApp (mkLam bodyS) aS) := by
      simpa [mkApp, mkLam] using hpure
    have hPureAS : PureTmPattern aS := (pure_app_inv hPureApp).2
    have hPureBodyS : PureTmPattern bodyS := by
      exact pure_lam_inv (pure_app_inv hPureApp).1
    set SPureS' := L₁ ∪ listToFinset (freeVars bodyS')
    obtain ⟨xs, hxs⟩ := exists_fresh SPureS'
    have hxsL₁ : xs ∉ L₁ := fun hmem => hxs (Finset.mem_union_left _ hmem)
    have hxsB' : xs ∉ listToFinset (freeVars bodyS') := fun hmem => hxs (Finset.mem_union_right _ hmem)
    have hOpenSrcS : PureTmPattern (openBVar 0 (.fvar xs) bodyS) := pureTm_openBVar_fvar xs hPureBodyS
    have hOpenTgtS' : PureTmPattern (openBVar 0 (.fvar xs) bodyS') :=
      parRed_preserves_pure (hbody₁ xs hxsL₁) hOpenSrcS
    have hPureBodyS' : PureTmPattern bodyS' :=
      pureTm_of_openBVar_fresh xs hOpenTgtS' (isFresh_of_not_in_freeVars_finset (p := bodyS') hxsB')
    have hlcF : lc_at 0 (mkLam bodyS) = true := by
      simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcA : lc_at 0 aS = true := by
      simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    generalize heq : mkApp (mkLam bodyS) aS = s' at h₂
    cases h₂ with
    | @app _ _ _ _ hf₂ ha₂ =>
      -- h₂ is app, h₁ is betaPi — symmetric to app/betaPi overlap
      simp [mkApp] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨wa, hwa₁, hwa₂⟩ := iha hlcA ha₂ hPureAS
      -- hf₂ : ParRed (mkLam bodyS) f₂'. Use lam_inv.
      obtain ⟨bd₂, Lf₂, hf₂_eq, hf₂_body⟩ | hf₂_eq := parRed_lam_inv hf₂ hlcF
      · subst hf₂_eq
        have hlcA' := parRed_preserves_lc ha₁ hlcA
        have hlcA₂' := parRed_preserves_lc ha₂ hlcA
        -- Join target: openBVar 0 wa bd₂ (join bodies via ihbody + hf₂_body, args via wa)
        -- Need: body join between bodyS' and bd₂ for all fresh x
        -- ihbody x _ gives diamond for opened bodyS at x
        -- hbody₁ x : ParRed (open x bodyS) (open x bodyS')
        -- hf₂_body x : ParRed (open x bodyS) (open x bd₂)
        -- ihbody x _ hlcOpen (hf₂_body x _) gives ⟨wbx, hwbx₁, hwbx₂⟩
        -- Close wbx to get common body wb, then parRed_openBVar for both sides
        set Lall := L₁ ∪ Lf₂ ∪ listToFinset (freeVars bodyS') ∪ listToFinset (freeVars bd₂)
        obtain ⟨x₀, hx₀⟩ := exists_fresh Lall
        have hx₀L₁ : x₀ ∉ L₁ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
        have hx₀Lf₂ : x₀ ∉ Lf₂ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
        have hlcOpen := lc_at_openBVar_result hlcBodyS (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
        obtain ⟨wbx₀, hwb₁, hwb₂⟩ := ihbody x₀ hx₀L₁ hlcOpen (hf₂_body x₀ hx₀Lf₂)
          (pureTm_openBVar_fvar x₀ hPureBodyS)
        set wb := closeBVar 0 x₀ wbx₀
        have hlcWbx₀ := parRed_preserves_lc hwb₁
          (parRed_preserves_lc (hbody₁ x₀ hx₀L₁) hlcOpen)
        have hfreshBS' := isFresh_of_not_in_freeVars_finset (p := bodyS') (fun h =>
          hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
        have hfreshBd₂ := isFresh_of_not_in_freeVars_finset (p := bd₂) (fun h =>
          hx₀ (Finset.mem_union_right _ h))
        have hfreshWB : isFresh x₀ wb = true := isFresh_closeBVar 0 x₀ wbx₀
        have hopen_wB : openBVar 0 (.fvar x₀) wb = wbx₀ := openBVar_closeBVar_cancel hlcWbx₀
        -- Left: ParRed (openBVar 0 aS' bodyS') (openBVar 0 wa wb)
        -- Need: bodyS' → wb for all fresh y, and aS' → wa
        -- Use subst_open_self_var to transfer body join from x₀ to any y
        have hbody_left : ∀ y, y ∉ (L₁ ∪ {x₀}) →
            ParRed (openBVar 0 (.fvar y) bodyS') (openBVar 0 (.fvar y) wb) := fun y hy => by
          have key := parRed_substFVar_same (x := x₀) (u := .fvar y) (by simp [lc_at]) hwb₁
          rwa [subst_open_self_var hfreshBS',
               show substFVar x₀ (.fvar y) wbx₀ = openBVar 0 (.fvar y) wb from by
                rw [← hopen_wB]; exact substFVar_intro wb hfreshWB 0] at key
        have hbody_right : ∀ y, y ∉ (Lf₂ ∪ {x₀}) →
            ParRed (openBVar 0 (.fvar y) bd₂) (openBVar 0 (.fvar y) wb) := fun y hy => by
          have key := parRed_substFVar_same (x := x₀) (u := .fvar y) (by simp [lc_at]) hwb₂
          rwa [subst_open_self_var hfreshBd₂,
               show substFVar x₀ (.fvar y) wbx₀ = openBVar 0 (.fvar y) wb from by
                rw [← hopen_wB]; exact substFVar_intro wb hfreshWB 0] at key
        exact ⟨openBVar 0 wa wb,
          parRed_openBVar (L₁ ∪ {x₀}) hbody_left hPureBodyS' hwa₁ hlcA' (parRed_preserves_lc hwa₁ hlcA'),
          .betaPi (Lf₂ ∪ {x₀}) hbody_right hwa₂
            (by have h := parRed_preserves_lc hf₂ hlcF
                simp [mkLam, lc_at, lc_at_list] at h; exact h)
            (parRed_preserves_lc ha₂ hlcA)⟩
      · -- hf₂ is refl_pat: f₂' = mkLam bodyS (body unchanged on h₂ side)
        subst hf₂_eq
        obtain ⟨wa, hwa₁, hwa₂⟩ := iha hlcA ha₂ hPureAS
        have hlcA' := parRed_preserves_lc ha₁ hlcA
        have hlcA₂' := parRed_preserves_lc ha₂ hlcA
        -- t₁ = openBVar 0 aS' bodyS', t₂ = mkApp (mkLam bodyS) a₂'
        -- Join: openBVar 0 wa bodyS'
        -- Left: parRed_openBVar with body refl (bodyS' → bodyS') and hwa₁
        -- Right: betaPi with hbody₁ (bodyS → bodyS') and hwa₂
        exact ⟨openBVar 0 wa bodyS',
          parRed_openBVar ∅ (fun x _ => parRed_refl _) hPureBodyS' hwa₁ hlcA' (parRed_preserves_lc hwa₁ hlcA'),
          .betaPi L₁ hbody₁ hwa₂ hlcBodyS (parRed_preserves_lc ha₂ hlcA)⟩
    | @betaPi _ bodyS_t _ aS_t L₂ hbody₂ ha₂ hlcBody₂' hlcA₂ =>
      -- Both h₁ and h₂ are betaPi — self-overlap
      simp [mkApp, mkLam] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨wa, hwa₁, hwa₂⟩ := iha hlcA ha₂ hPureAS
      set SPureT := L₂ ∪ listToFinset (freeVars bodyS_t)
      obtain ⟨xt, hxt⟩ := exists_fresh SPureT
      have hxtL₂ : xt ∉ L₂ := fun hmem => hxt (Finset.mem_union_left _ hmem)
      have hxtB : xt ∉ listToFinset (freeVars bodyS_t) := fun hmem => hxt (Finset.mem_union_right _ hmem)
      have hOpenSrc_t : PureTmPattern (openBVar 0 (.fvar xt) bodyS) := pureTm_openBVar_fvar xt hPureBodyS
      have hOpenTgt_t : PureTmPattern (openBVar 0 (.fvar xt) bodyS_t) :=
        parRed_preserves_pure (hbody₂ xt hxtL₂) hOpenSrc_t
      have hPureBodyS_t : PureTmPattern bodyS_t :=
        pureTm_of_openBVar_fresh xt hOpenTgt_t (isFresh_of_not_in_freeVars_finset (p := bodyS_t) hxtB)
      -- Join bodies: pick fresh x₀, use ihbody on hbody₂
      set Lall := L₁ ∪ L₂ ∪ listToFinset (freeVars bodyS') ∪ listToFinset (freeVars bodyS_t)
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lall
      have hx₀L₁ : x₀ ∉ L₁ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
      have hx₀L₂ : x₀ ∉ L₂ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hlcOpen := lc_at_openBVar_result hlcBodyS (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨wbx₀, hwb₁, hwb₂⟩ := ihbody x₀ hx₀L₁ hlcOpen (hbody₂ x₀ hx₀L₂)
        (pureTm_openBVar_fvar x₀ hPureBodyS)
      set wb := closeBVar 0 x₀ wbx₀
      have hlcWbx₀ := parRed_preserves_lc hwb₁
        (parRed_preserves_lc (hbody₁ x₀ hx₀L₁) hlcOpen)
      have hfreshBS' := isFresh_of_not_in_freeVars_finset (p := bodyS') (fun h =>
        hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hfreshB₂ := isFresh_of_not_in_freeVars_finset (p := bodyS_t) (fun h =>
        hx₀ (Finset.mem_union_right _ h))
      have hfreshWB : isFresh x₀ wb = true := isFresh_closeBVar 0 x₀ wbx₀
      have hopen_wB : openBVar 0 (.fvar x₀) wb = wbx₀ := openBVar_closeBVar_cancel hlcWbx₀
      have hbody_left : ∀ y, y ∉ (L₁ ∪ {x₀}) →
          ParRed (openBVar 0 (.fvar y) bodyS') (openBVar 0 (.fvar y) wb) := fun y hy => by
        have key := parRed_substFVar_same (x := x₀) (u := .fvar y) (by simp [lc_at]) hwb₁
        rwa [subst_open_self_var hfreshBS',
             show substFVar x₀ (.fvar y) wbx₀ = openBVar 0 (.fvar y) wb from by
              rw [← hopen_wB]; exact substFVar_intro wb hfreshWB 0] at key
      have hbody_right : ∀ y, y ∉ (L₂ ∪ {x₀}) →
          ParRed (openBVar 0 (.fvar y) bodyS_t) (openBVar 0 (.fvar y) wb) := fun y hy => by
        have key := parRed_substFVar_same (x := x₀) (u := .fvar y) (by simp [lc_at]) hwb₂
        rwa [subst_open_self_var hfreshB₂,
             show substFVar x₀ (.fvar y) wbx₀ = openBVar 0 (.fvar y) wb from by
              rw [← hopen_wB]; exact substFVar_intro wb hfreshWB 0] at key
      have hlcA' := parRed_preserves_lc ha₁ hlcA
      have hlcA₂' := parRed_preserves_lc ha₂ hlcA
      exact ⟨openBVar 0 wa wb,
        parRed_openBVar (L₁ ∪ {x₀}) hbody_left hPureBodyS' hwa₁ hlcA' (parRed_preserves_lc hwa₁ hlcA'),
        parRed_openBVar (L₂ ∪ {x₀}) hbody_right hPureBodyS_t hwa₂ hlcA₂' (parRed_preserves_lc hwa₂ hlcA₂')⟩
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .betaPi L₁ hbody₁ ha₁ hlcBodyS hlcAS⟩
    | _ => simp [mkApp, mkPi, mkSigma, mkLam, mkPair, mkFst, mkSnd, mkId, mkRefl] at heq
  | @betaSigmaFst aS aS' bS bS' haS₁ hbS₁ iha ihb =>
    intro hpure
    have hPurePair : PureTmPattern (mkPair aS bS) := pure_fst_inv hpure
    let hPureAB := pure_pair_inv hPurePair
    have hlcA : lc_at 0 aS = true := by
      simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB : lc_at 0 bS = true := by
      simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    generalize heq : mkFst (mkPair aS bS) = s' at h₂
    cases h₂ with
    | @fst _ _ hp₂ =>
      -- h₂ is fst, h₁ is betaSigmaFst
      simp [mkFst] at heq; obtain ⟨rfl⟩ := heq
      -- hp₂ : ParRed (mkPair aS bS) p₂'. Use pair_inv.
      obtain ⟨wa₂, wb₂, hp₂_eq, hwa₂_rel, hwb₂_rel⟩ | hp₂_eq := parRed_pair_inv hp₂ (by
        simp [mkPair, lc_at, lc_at_list]; exact ⟨hlcA, hlcB⟩)
      · subst hp₂_eq
        obtain ⟨wa, hwa₁, hwa₂⟩ := iha hlcA hwa₂_rel hPureAB.1
        -- t₁ = aS', t₂ = mkFst (mkPair wa₂ wb₂)
        -- Join: wa. Left: hwa₁. Right: betaSigmaFst hwa₂ (parRed_refl wb₂)
        exact ⟨wa, hwa₁, .betaSigmaFst hwa₂ (parRed_refl wb₂)⟩
      · -- hp₂ is refl_pat: p₂' = mkPair aS bS
        subst hp₂_eq
        -- t₂ = mkFst (mkPair aS bS). Join with aS'.
        exact ⟨aS', parRed_refl aS', .betaSigmaFst haS₁ hbS₁⟩
    | @betaSigmaFst _ _ _ _ ha₂ hb₂ =>
      -- Both betaSigmaFst
      simp [mkFst, mkPair] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨wa, hwa₁, hwa₂⟩ := iha hlcA ha₂ hPureAB.1
      exact ⟨wa, hwa₁, hwa₂⟩
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .betaSigmaFst haS₁ hbS₁⟩
    | _ => simp [mkFst, mkPair, mkPi, mkSigma, mkLam, mkApp, mkSnd, mkId, mkRefl] at heq
  | @betaSigmaSnd aS aS' bS bS' haS₁ hbS₁ iha ihb =>
    intro hpure
    have hPurePair : PureTmPattern (mkPair aS bS) := pure_snd_inv hpure
    let hPureAB := pure_pair_inv hPurePair
    have hlcA : lc_at 0 aS = true := by
      simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB : lc_at 0 bS = true := by
      simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    generalize heq : mkSnd (mkPair aS bS) = s' at h₂
    cases h₂ with
    | @snd _ _ hp₂ =>
      simp [mkSnd] at heq; obtain ⟨rfl⟩ := heq
      obtain ⟨wa₂, wb₂, hp₂_eq, hwa₂_rel, hwb₂_rel⟩ | hp₂_eq := parRed_pair_inv hp₂ (by
        simp [mkPair, lc_at, lc_at_list]; exact ⟨hlcA, hlcB⟩)
      · subst hp₂_eq
        obtain ⟨wb, hwb₁, hwb₂⟩ := ihb hlcB hwb₂_rel hPureAB.2
        exact ⟨wb, hwb₁, .betaSigmaSnd (parRed_refl wa₂) hwb₂⟩
      · subst hp₂_eq
        exact ⟨bS', parRed_refl bS', .betaSigmaSnd haS₁ hbS₁⟩
    | @betaSigmaSnd _ _ _ _ ha₂ hb₂ =>
      simp [mkSnd, mkPair] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨wb, hwb₁, hwb₂⟩ := ihb hlcB hb₂ hPureAB.2
      exact ⟨wb, hwb₁, hwb₂⟩
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .betaSigmaSnd haS₁ hbS₁⟩
    | _ => simp [mkSnd, mkPair, mkPi, mkSigma, mkLam, mkApp, mkFst, mkId, mkRefl] at heq

/-! ## Church-Rosser

Confluence of `PureReducesStar`, proved via parallel reduction. -/

/-- Strip lemma: single ParRed step can be joined with multi-step. -/
private theorem strip_lemma {s u v : Pattern}
    (hlc : lc_at 0 s = true)
    (h₁ : ParRed s u) (h₂ : PureReducesStar s v)
    (hpure : PureTmPattern s) :
    ∃ w, PureReducesStar u w ∧ PureReducesStar v w := by
  induction h₂ generalizing u with
  | refl => exact ⟨u, .refl u, parRed_to_pureReducesStar h₁ hlc⟩
  | step hs htail ih =>
    have hlcMid := pureReduces_preserves_lc hs hlc
    obtain ⟨w₁, hw₁u, hw₁mid⟩ := diamond_parRed hlc h₁ (pureReduces_to_parRed hs hlc) hpure
    have hlcU := parRed_preserves_lc h₁ hlc
    have hmidPure : PureTmPattern _ := parRed_preserves_pure (pureReduces_to_parRed hs hlc) hpure
    obtain ⟨w₂, hw₂w₁, hw₂v⟩ := ih hlcMid hw₁mid hmidPure
    exact ⟨w₂, (parRed_to_pureReducesStar hw₁u hlcU).trans hw₂w₁, hw₂v⟩

/-- Confluence: if `s` multi-step reduces to both `u` and `v`,
    they have a common reduct (for locally closed terms). -/
theorem reduceStar_confluence_lc
    {s u v : Pattern} (hlc : lc_at 0 s = true)
    (h₁ : PureReducesStar s u) (h₂ : PureReducesStar s v)
    (hpure : PureTmPattern s) :
    ∃ w, PureReducesStar u w ∧ PureReducesStar v w := by
  induction h₁ generalizing v with
  | refl => exact ⟨v, h₂, .refl v⟩
  | step hs htail ih =>
    have hlcMid := pureReduces_preserves_lc hs hlc
    obtain ⟨w₁, hw₁mid, hw₁v⟩ := strip_lemma hlc (pureReduces_to_parRed hs hlc) h₂ hpure
    have hmidPure : PureTmPattern _ := parRed_preserves_pure (pureReduces_to_parRed hs hlc) hpure
    obtain ⟨w₂, hw₂u, hw₂w₁⟩ := ih hlcMid hw₁mid hmidPure
    exact ⟨w₂, hw₂u, hw₁v.trans hw₂w₁⟩

/-- Church-Rosser: if `s ≡ t` and `s` is locally closed,
    they share a common reduct. -/
theorem church_rosser_lc {s t : Pattern} (h : PureConv s t)
    (hlc : lc_at 0 s = true) :
    ∃ u, PureReducesStar s u ∧ PureReducesStar t u := by
  induction h with
  | refl t _ => exact ⟨t, .refl t, .refl t⟩
  | symm hsub ih =>
      have hlcT := (PureConv_preserves_lc_both hsub).2 hlc
      obtain ⟨u, h₁, h₂⟩ := ih hlcT
      exact ⟨u, h₂, h₁⟩
  | trans h₁₂ h₂₃ ih₁ ih₂ =>
      have hlcMid := PureConv_preserves_lc h₁₂ hlc
      obtain ⟨u₁, hs_u₁, hmid_u₁⟩ := ih₁ hlc
      obtain ⟨u₂, hmid_u₂, ht_u₂⟩ := ih₂ hlcMid
      obtain ⟨w, hu₁_w, hu₂_w⟩ :=
        reduceStar_confluence_lc hlcMid hmid_u₁ hmid_u₂ (PureConv_rightPure h₁₂)
      exact ⟨w, hs_u₁.trans hu₁_w, ht_u₂.trans hu₂_w⟩
  | betaPi body a _ _ _ _ =>
      exact ⟨_, PureReducesStar.single (.betaPi body a), .refl _⟩
  | betaSigmaFst a b _ _ _ _ =>
      exact ⟨_, PureReducesStar.single (.betaSigmaFst a b), .refl _⟩
  | betaSigmaSnd a b _ _ _ _ =>
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
    (hPureX : PureTmPattern X) (hPureY : PureTmPattern Y)
    (hlcX : lc_at 0 X = true) (hlcY : lc_at 1 Y = true) :
    PureConv (mkApp (mkLam (.bvar 0)) (mkPi X Y)) (mkPi X Y) := by
  have hlcBody : lc_at 1 (.bvar 0 : Pattern) = true := by simp [lc_at]
  have hlcPi : lc_at 0 (mkPi X Y) = true := by
    simp [mkPi, lc_at, lc_at_list, Bool.and_eq_true]
    exact ⟨hlcX, hlcY⟩
  have h := PureConv.betaPi (.bvar 0) (mkPi X Y) (PureTmPattern.bvar 0) (.pi hPureX hPureY) hlcBody hlcPi
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
  have hPure : PureTmPattern (mkPi A₁ B₁) ∧ PureTmPattern (mkPi A₂ B₂) := PureConv_pure_both h
  have hPureAB₁ : PureTmPattern A₁ ∧ PureTmPattern B₁ := pure_pi_inv hPure.1
  have hPureAB₂ : PureTmPattern A₂ ∧ PureTmPattern B₂ := pure_pi_inv hPure.2
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
  exact ⟨.trans (PureReducesStar_implies_PureConv hdomL hlcA₁ hPureAB₁.1)
               (.symm (PureReducesStar_implies_PureConv hdomR hlcA₂ hPureAB₂.1)),
         Ll ∪ Lr, fun x hx =>
           .trans (PureReducesStar_implies_PureConv
                    (hcodL x (fun h => hx (Finset.mem_union_left _ h)))
                    (lc_at_openBVar_result hlcB₁ (by simp [lc_at]))
                    (pureTm_openBVar_fvar x hPureAB₁.2))
                  (.symm (PureReducesStar_implies_PureConv
                    (hcodR x (fun h => hx (Finset.mem_union_right _ h)))
                    (lc_at_openBVar_result hlcB₂ (by simp [lc_at]))
                    (pureTm_openBVar_fvar x hPureAB₂.2)))⟩

/-- Sigma-injectivity: convertible Sigma types have convertible components. -/
theorem sigma_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkSigma A₁ B₁) (mkSigma A₂ B₂))
    (hlc : lc_at 0 (mkSigma A₁ B₁) = true) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) := by
  have hPure : PureTmPattern (mkSigma A₁ B₁) ∧ PureTmPattern (mkSigma A₂ B₂) := PureConv_pure_both h
  have hPureAB₁ : PureTmPattern A₁ ∧ PureTmPattern B₁ := pure_sigma_inv hPure.1
  have hPureAB₂ : PureTmPattern A₂ ∧ PureTmPattern B₂ := pure_sigma_inv hPure.2
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
  exact ⟨.trans (PureReducesStar_implies_PureConv hdomL hlcA₁ hPureAB₁.1)
               (.symm (PureReducesStar_implies_PureConv hdomR hlcA₂ hPureAB₂.1)),
         Ll ∪ Lr, fun x hx =>
           .trans (PureReducesStar_implies_PureConv
                    (hcodL x (fun h => hx (Finset.mem_union_left _ h)))
                    (lc_at_openBVar_result hlcB₁ (by simp [lc_at]))
                    (pureTm_openBVar_fvar x hPureAB₁.2))
                  (.symm (PureReducesStar_implies_PureConv
                    (hcodR x (fun h => hx (Finset.mem_union_right _ h)))
                    (lc_at_openBVar_result hlcB₂ (by simp [lc_at]))
                    (pureTm_openBVar_fvar x hPureAB₂.2)))⟩

end Mettapedia.Languages.MeTTa.Pure.Confluence
