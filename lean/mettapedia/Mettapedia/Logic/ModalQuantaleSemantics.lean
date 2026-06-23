import Mathlib.Algebra.Order.Quantale
import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.Logic.ModalMuCalculus
import Mettapedia.Logic.TemporalQuantale

/-!
# Quantale-Valued Modal μ-Calculus Semantics

This file extends the Boolean satisfaction relation of modal μ-calculus to
**quantale-valued** semantics, where formulas take values in a complete lattice
equipped with a monoidal structure.

## Mathematical Foundation

Instead of Boolean truth:
- `satisfies : State → Formula → Prop`

We have graded truth:
- `qSatisfies : State → Formula → Q`

where Q is a commutative quantale (complete lattice with associative, commutative,
supremum-distributing multiplication).

## Key Properties

1. **Lattice operations lift**: `φ ∧ ψ ↦ qSat(φ) ⊓ qSat(ψ)` (infimum)
2. **Modalities are residuated**: Box uses residuation from quantale
3. **Fixed points exist**: Knaster-Tarski in complete lattice

## Connection to PLN

PLN's evidence quantale `(n⁺, n⁻) ∈ ℝ≥0∞ × ℝ≥0∞` is a commutative quantale.
This file provides the semantic foundation for embedding temporal PLN into
modal μ-calculus with graded truth values.

## References

[1] Todorov & Poulsen (2024). "Modal μ-Calculus for Free in Agda". TyDe '24
[2] Rosenthal, K. "Quantales and their Applications"
[3] Goertzel, B. "Weakness and Its Quantale"
-/

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Algebra.QuantaleWeakness

universe u v w

namespace Mettapedia.Logic.ModalQuantaleSemantics

variable {Q : Type u} [CommSemigroup Q] [CompleteLattice Q] [IsCommQuantale Q]
variable {S : Type v} {Act : Type w}

/-! ## Quantale-Valued Transition Systems

A labeled transition system with quantale-valued transitions.
Instead of `trans : S → Act → S → Prop`, we have `trans : S → Act → S → Q`.
-/

/-- A quantale-labeled transition system (QLTS).
    Transitions carry quantale values representing "strength" or "evidence". -/
structure QLTS (Q : Type*) [CompleteLattice Q] (S : Type*) (Act : Type*) where
  /-- Transition strength: how strongly state s transitions to s' via action a -/
  trans : S → Act → S → Q
  /-- Assumption: total system (every state has successors for every action)
      This simplifies semantics; partial systems can use ⊥ for non-transitions -/
  total : ∀ s a, ∃ s', trans s a s' ≠ ⊥

/-- Convert a Boolean LTS to QLTS using top/bottom values.
    Requires the LTS to be total (every state has at least one successor for each action).
    Requires classical decidability and nontriviality (⊤ ≠ ⊥). -/
noncomputable def QLTS.ofLTS [CompleteLattice Q] [Nontrivial Q]
    (lts : LTS S Act) (h_total : ∀ s a, ∃ s', lts.trans s a s') : QLTS Q S Act where
  trans s a s' := @ite _ (lts.trans s a s') (Classical.propDecidable _) ⊤ ⊥
  total s a := by
    obtain ⟨s', hs'⟩ := h_total s a
    use s'
    simp only [hs', ↓reduceIte]
    exact top_ne_bot

/-! ## Quantale-Valued Satisfaction

The central definition: satisfaction valued in a quantale.
-/

/-- Environment mapping bound variables to quantale-valued predicates -/
def QEnv (Q : Type*) (S : Type*) (n : ℕ) := Fin n → (S → Q)

/-- Empty environment -/
def QEnv.empty : QEnv Q S 0 := Fin.elim0

/-- Extend environment with a new predicate -/
def QEnv.extend (ρ : QEnv Q S n) (P : S → Q) : QEnv Q S (n + 1) :=
  fun i => if h : i.val = 0 then P else ρ ⟨i.val - 1, by omega⟩

/--
Quantale-valued satisfaction for modal μ-calculus formulas.

`qSatisfies qlts ρ φ s` returns the quantale value of satisfaction at state `s`.

**Key semantic choices**:
- Conjunction → infimum (lattice meet)
- Disjunction → supremum (lattice join)
- Diamond → existential quantification as supremum with conjunction
- Box → universal quantification via residuation
- Negation → complement (requires involutive negation in quantale)
-/
noncomputable def qSatisfies (qlts : QLTS Q S Act) : QEnv Q S n → Formula Act n → S → Q
  | _, Formula.tt, _ => ⊤
  | _, Formula.ff, _ => ⊥
  | ρ, Formula.neg φ, s =>
      -- Quantale negation: we use the Heyting complement
      -- a → ⊥ in a Frame (complete Heyting algebra)
      leftResiduate (qSatisfies qlts ρ φ s) ⊥
  | ρ, Formula.conj φ ψ, s => qSatisfies qlts ρ φ s ⊓ qSatisfies qlts ρ ψ s
  | ρ, Formula.disj φ ψ, s => qSatisfies qlts ρ φ s ⊔ qSatisfies qlts ρ ψ s
  | ρ, Formula.diamond a φ, s =>
      -- Diamond: "there exists a strong transition satisfying φ"
      -- ⟨a⟩φ ↦ ⊔_{s'} (trans(s,a,s') * qSat(φ)(s'))
      ⨆ s' : S, qlts.trans s a s' * qSatisfies qlts ρ φ s'
  | ρ, Formula.box a φ, s =>
      -- Box: "all transitions imply φ"
      -- [a]φ ↦ ⊓_{s'} (trans(s,a,s') ⇨ qSat(φ)(s'))
      ⨅ s' : S, leftResiduate (qlts.trans s a s') (qSatisfies qlts ρ φ s')
  | ρ, Formula.mu φ, s =>
      -- Least fixed point: infimum of all pre-fixed points
      -- μX.φ = ⊓ { P : S → Q | φ[P/X] ≤ P }
      ⨅ P : S → Q, ⨅ _ : ∀ t, qSatisfies qlts (ρ.extend P) φ t ≤ P t, P s
  | ρ, Formula.nu φ, s =>
      -- Greatest fixed point: supremum of all post-fixed points
      -- νX.φ = ⊔ { P : S → Q | P ≤ φ[P/X] }
      ⨆ P : S → Q, ⨆ _ : ∀ t, P t ≤ qSatisfies qlts (ρ.extend P) φ t, P s
  | ρ, Formula.var i, s => ρ i s

/-- The quantale value assigned to a state by a formula -/
noncomputable def qSat (qlts : QLTS Q S Act) (ρ : QEnv Q S n) (φ : Formula Act n) : S → Q :=
  qSatisfies qlts ρ φ

/-! ## Basic Properties -/

/-- Truth is maximal -/
theorem qSat_tt (qlts : QLTS Q S Act) (ρ : QEnv Q S n) (s : S) :
    qSatisfies qlts ρ Formula.tt s = ⊤ := rfl

/-- Falsity is minimal -/
theorem qSat_ff (qlts : QLTS Q S Act) (ρ : QEnv Q S n) (s : S) :
    qSatisfies qlts ρ Formula.ff s = ⊥ := rfl

/-- Conjunction is infimum -/
theorem qSat_conj (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (φ ψ : Formula Act n) (s : S) :
    qSatisfies qlts ρ (Formula.conj φ ψ) s =
    qSatisfies qlts ρ φ s ⊓ qSatisfies qlts ρ ψ s := rfl

/-- Disjunction is supremum -/
theorem qSat_disj (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (φ ψ : Formula Act n) (s : S) :
    qSatisfies qlts ρ (Formula.disj φ ψ) s =
    qSatisfies qlts ρ φ s ⊔ qSatisfies qlts ρ ψ s := rfl

/-! ## Monotonicity

Satisfaction is monotone in the environment (for positive formulas).
-/

/-- The predicate transformer associated with a formula body -/
noncomputable def transformer (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (φ : Formula Act (n + 1)) : (S → Q) → (S → Q) :=
  fun P s => qSatisfies qlts (ρ.extend P) φ s

/-- Helper: extend environment monotonically -/
lemma qEnv_extend_mono (ρ : QEnv Q S n) {P₁ P₂ : S → Q} (hle : ∀ s, P₁ s ≤ P₂ s) :
    ∀ i s, (ρ.extend P₁) i s ≤ (ρ.extend P₂) i s := by
  intro i s
  unfold QEnv.extend
  split
  · exact hle s
  · rfl

/-- Helper: Satisfaction is monotone (polarity=true) or antitone (polarity=false)
    in environments when variable i appears with that polarity.
    This is the key technical lemma needed for Knaster-Tarski. -/
lemma qSatisfies_mono_env (qlts : QLTS Q S Act) {n : ℕ}
    (φ : Formula Act n) (i : Fin n) (polarity : Bool)
    (hpos : φ.isPositiveIn i polarity = true) :
    ∀ (ρ₁ ρ₂ : QEnv Q S n),
    (∀ j s, j ≠ i → ρ₁ j s = ρ₂ j s) →
    (∀ s, ρ₁ i s ≤ ρ₂ i s) →
    ∀ s, if polarity then qSatisfies qlts ρ₁ φ s ≤ qSatisfies qlts ρ₂ φ s
         else qSatisfies qlts ρ₂ φ s ≤ qSatisfies qlts ρ₁ φ s := by
  induction φ generalizing polarity with
  | tt => intros; split <;> rfl
  | ff => intros; split <;> rfl
  | neg φ ih =>
    intros ρ₁ ρ₂ h_eq h_le s
    simp only [qSatisfies, Formula.isPositiveIn] at hpos ⊢
    -- Negation flips polarity
    cases polarity with
    | true =>
      -- polarity = true: show leftResiduate (qSat ρ₁ φ) ⊥ ≤ leftResiduate (qSat ρ₂ φ) ⊥
      simp only [Bool.not_true] at hpos
      apply leftResiduate_antitone_left
      exact ih i false hpos ρ₁ ρ₂ h_eq h_le s
    | false =>
      -- polarity = false: show leftResiduate (qSat ρ₂ φ) ⊥ ≤ leftResiduate (qSat ρ₁ φ) ⊥
      simp only [Bool.not_false] at hpos
      apply leftResiduate_antitone_left
      exact ih i true hpos ρ₁ ρ₂ h_eq h_le s
  | conj φ ψ ih_φ ih_ψ =>
    intros ρ₁ ρ₂ h_eq h_le s
    simp only [qSatisfies]
    simp only [Formula.isPositiveIn, Bool.and_eq_true] at hpos
    cases polarity with
    | true =>
      have h1 := ih_φ i true hpos.1 ρ₁ ρ₂ h_eq h_le s
      have h2 := ih_ψ i true hpos.2 ρ₁ ρ₂ h_eq h_le s
      simp at h1 h2
      exact inf_le_inf h1 h2
    | false =>
      have h1 := ih_φ i false hpos.1 ρ₁ ρ₂ h_eq h_le s
      have h2 := ih_ψ i false hpos.2 ρ₁ ρ₂ h_eq h_le s
      simp at h1 h2
      exact inf_le_inf h1 h2
  | disj φ ψ ih_φ ih_ψ =>
    intros ρ₁ ρ₂ h_eq h_le s
    simp only [qSatisfies]
    simp only [Formula.isPositiveIn, Bool.and_eq_true] at hpos
    cases polarity with
    | true =>
      have h1 := ih_φ i true hpos.1 ρ₁ ρ₂ h_eq h_le s
      have h2 := ih_ψ i true hpos.2 ρ₁ ρ₂ h_eq h_le s
      simp at h1 h2
      exact sup_le_sup h1 h2
    | false =>
      have h1 := ih_φ i false hpos.1 ρ₁ ρ₂ h_eq h_le s
      have h2 := ih_ψ i false hpos.2 ρ₁ ρ₂ h_eq h_le s
      simp at h1 h2
      exact sup_le_sup h1 h2
  | diamond a φ ih =>
    intros ρ₁ ρ₂ h_eq h_le s
    simp only [qSatisfies]
    simp only [Formula.isPositiveIn] at hpos
    cases polarity with
    | true =>
      apply iSup_mono; intro s'
      apply mul_le_mul'
      · exact le_refl (qlts.trans s a s')
      · have h := ih i true hpos ρ₁ ρ₂ h_eq h_le s'
        simp at h; exact h
    | false =>
      apply iSup_mono; intro s'
      apply mul_le_mul'
      · exact le_refl (qlts.trans s a s')
      · have h := ih i false hpos ρ₁ ρ₂ h_eq h_le s'
        simp at h; exact h
  | box a φ ih =>
    intros ρ₁ ρ₂ h_eq h_le s
    simp only [qSatisfies]
    simp only [Formula.isPositiveIn] at hpos
    cases polarity with
    | true =>
      apply iInf_mono; intro s'
      have h := ih i true hpos ρ₁ ρ₂ h_eq h_le s'
      simp at h
      exact leftResiduate_mono_right (qlts.trans s a s') h
    | false =>
      apply iInf_mono; intro s'
      have h := ih i false hpos ρ₁ ρ₂ h_eq h_le s'
      simp at h
      exact leftResiduate_mono_right (qlts.trans s a s') h
  | mu φ ih =>
    intros ρ₁ ρ₂ h_eq h_le s
    simp only [qSatisfies, Formula.isPositiveIn] at hpos ⊢
    cases polarity with
    | true =>
      -- polarity = true: show ⨅ prefixed(ρ₁) ≤ ⨅ prefixed(ρ₂)
      -- Strategy: every P that's pre-fixed for ρ₂ is also pre-fixed for ρ₁
      apply le_iInf; intro P; apply le_iInf; intro hP
      -- hP : ∀ t, qSatisfies (ρ₂.extend P) φ t ≤ P t
      -- Need to show: ⨅ prefixed(ρ₁) ≤ P s
      suffices h : ∀ t, qSatisfies qlts (ρ₁.extend P) φ t ≤ P t by
        calc ⨅ P', ⨅ _ : (∀ t, qSatisfies qlts (ρ₁.extend P') φ t ≤ P' t), P' s
            ≤ ⨅ _ : (∀ t, qSatisfies qlts (ρ₁.extend P) φ t ≤ P t), P s := iInf_le _ P
          _ ≤ P s := iInf_le _ h
      intro t
      have h_ih := ih i.succ true hpos (ρ₁.extend P) (ρ₂.extend P)
      simp at h_ih
      calc qSatisfies qlts (ρ₁.extend P) φ t
          ≤ qSatisfies qlts (ρ₂.extend P) φ t := by
            apply h_ih
            · intros j t' hj
              unfold QEnv.extend
              by_cases h0 : j.val = 0
              · simp [h0]
              · -- 4.31: bare `simp [h0]` no longer fires `dif_neg`; reduce the `dite`s explicitly,
                -- then apply `h_eq` at the predecessor index (`≠ i`, else `j = i.succ`).
                simp only [dif_neg h0]
                exact h_eq ⟨j.val - 1, by omega⟩ t' (by
                  intro heq
                  apply hj
                  apply Fin.ext
                  have hval : (↑j - 1 : ℕ) = ↑i := congrArg Fin.val heq
                  simp only [Fin.val_succ]
                  omega)
            · intro t'; unfold QEnv.extend; by_cases h : i.succ.val = 0
              · exfalso; simp [Fin.val_succ] at h
              · simp [h]; convert h_le t' using 1
          _ ≤ P t := hP t
    | false =>
      -- polarity = false: show ⨅ prefixed(ρ₂) ≤ ⨅ prefixed(ρ₁)
      apply le_iInf; intro P; apply le_iInf; intro hP
      suffices h : ∀ t, qSatisfies qlts (ρ₂.extend P) φ t ≤ P t by
        calc ⨅ P', ⨅ _ : (∀ t, qSatisfies qlts (ρ₂.extend P') φ t ≤ P' t), P' s
            ≤ ⨅ _ : (∀ t, qSatisfies qlts (ρ₂.extend P) φ t ≤ P t), P s := iInf_le _ P
          _ ≤ P s := iInf_le _ h
      intro t
      have h_ih := ih i.succ false hpos (ρ₁.extend P) (ρ₂.extend P)
      simp at h_ih
      calc qSatisfies qlts (ρ₂.extend P) φ t
          ≤ qSatisfies qlts (ρ₁.extend P) φ t := by
            apply h_ih
            · intros j t' hj
              unfold QEnv.extend
              by_cases h0 : j.val = 0
              · simp [h0]
              · -- 4.31: bare `simp [h0]` no longer fires `dif_neg`; reduce the `dite`s explicitly,
                -- then apply `h_eq` at the predecessor index (`≠ i`, else `j = i.succ`).
                simp only [dif_neg h0]
                exact h_eq ⟨j.val - 1, by omega⟩ t' (by
                  intro heq
                  apply hj
                  apply Fin.ext
                  have hval : (↑j - 1 : ℕ) = ↑i := congrArg Fin.val heq
                  simp only [Fin.val_succ]
                  omega)
            · intro t'; unfold QEnv.extend; by_cases h : i.succ.val = 0
              · exfalso; simp [Fin.val_succ] at h
              · simp [h]; convert h_le t' using 1
          _ ≤ P t := hP t
  | nu φ ih =>
    intros ρ₁ ρ₂ h_eq h_le s
    simp only [qSatisfies, Formula.isPositiveIn] at hpos ⊢
    cases polarity with
    | true =>
      -- polarity = true: show ⨆ postfixed(ρ₁) ≤ ⨆ postfixed(ρ₂)
      apply iSup_le; intro P; apply iSup_le; intro hP
      suffices h : ∀ t, P t ≤ qSatisfies qlts (ρ₂.extend P) φ t by
        calc P s
            ≤ ⨆ _ : (∀ t, P t ≤ qSatisfies qlts (ρ₂.extend P) φ t), P s := le_iSup (fun _ => P s) h
          _ ≤ ⨆ P', ⨆ _ : (∀ t, P' t ≤ qSatisfies qlts (ρ₂.extend P') φ t), P' s :=
              @le_iSup _ _ _ (fun P' => ⨆ _ : (∀ t, P' t ≤ qSatisfies qlts (ρ₂.extend P') φ t), P' s) P
      intro t
      have h_ih := ih i.succ true hpos (ρ₁.extend P) (ρ₂.extend P)
      simp at h_ih
      calc P t
          ≤ qSatisfies qlts (ρ₁.extend P) φ t := hP t
        _ ≤ qSatisfies qlts (ρ₂.extend P) φ t := by
            apply h_ih
            · intros j t' hj
              unfold QEnv.extend
              by_cases h0 : j.val = 0
              · simp [h0]
              · -- 4.31: bare `simp [h0]` no longer fires `dif_neg`; reduce the `dite`s explicitly,
                -- then apply `h_eq` at the predecessor index (`≠ i`, else `j = i.succ`).
                simp only [dif_neg h0]
                exact h_eq ⟨j.val - 1, by omega⟩ t' (by
                  intro heq
                  apply hj
                  apply Fin.ext
                  have hval : (↑j - 1 : ℕ) = ↑i := congrArg Fin.val heq
                  simp only [Fin.val_succ]
                  omega)
            · intro t'; unfold QEnv.extend; by_cases h : i.succ.val = 0
              · exfalso; simp [Fin.val_succ] at h
              · simp [h]; convert h_le t' using 1
    | false =>
      -- polarity = false: show ⨆ postfixed(ρ₂) ≤ ⨆ postfixed(ρ₁)
      apply iSup_le; intro P; apply iSup_le; intro hP
      suffices h : ∀ t, P t ≤ qSatisfies qlts (ρ₁.extend P) φ t by
        calc P s
            ≤ ⨆ _ : (∀ t, P t ≤ qSatisfies qlts (ρ₁.extend P) φ t), P s := le_iSup (fun _ => P s) h
          _ ≤ ⨆ P', ⨆ _ : (∀ t, P' t ≤ qSatisfies qlts (ρ₁.extend P') φ t), P' s :=
              @le_iSup _ _ _ (fun P' => ⨆ _ : (∀ t, P' t ≤ qSatisfies qlts (ρ₁.extend P') φ t), P' s) P
      intro t
      have h_ih := ih i.succ false hpos (ρ₁.extend P) (ρ₂.extend P)
      simp at h_ih
      calc P t
          ≤ qSatisfies qlts (ρ₂.extend P) φ t := hP t
        _ ≤ qSatisfies qlts (ρ₁.extend P) φ t := by
            apply h_ih
            · intros j t' hj
              unfold QEnv.extend
              by_cases h0 : j.val = 0
              · simp [h0]
              · -- 4.31: bare `simp [h0]` no longer fires `dif_neg`; reduce the `dite`s explicitly,
                -- then apply `h_eq` at the predecessor index (`≠ i`, else `j = i.succ`).
                simp only [dif_neg h0]
                exact h_eq ⟨j.val - 1, by omega⟩ t' (by
                  intro heq
                  apply hj
                  apply Fin.ext
                  have hval : (↑j - 1 : ℕ) = ↑i := congrArg Fin.val heq
                  simp only [Fin.val_succ]
                  omega)
            · intro t'; unfold QEnv.extend; by_cases h : i.succ.val = 0
              · exfalso; simp [Fin.val_succ] at h
              · simp [h]; convert h_le t' using 1
  | var j =>
    intros ρ₁ ρ₂ h_eq h_le s
    simp only [qSatisfies]
    simp only [Formula.isPositiveIn] at hpos
    by_cases h : j = i
    · rw [h]
      cases polarity with
      | true => exact h_le s
      | false =>
        -- When j = i and polarity = false, hpos says: false || false = true, contradiction
        simp [h] at hpos
    · rw [h_eq j s h]
      cases polarity <;> simp

/-- Transformer is monotone for positive formulas (key for Knaster-Tarski)
    A formula is positive if variable 0 appears only in positive positions
    (not under an odd number of negations). This is a standard result from
    Kozen (1983). -/
theorem transformer_mono (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (φ : Formula Act (n + 1)) (hpos : φ.isPositive = true) :
    Monotone (transformer qlts ρ φ) := by
  intro P₁ P₂ hle s
  unfold transformer
  -- Apply the general monotonicity lemma specialized to variable 0
  apply qSatisfies_mono_env qlts φ 0 true hpos (ρ.extend P₁) (ρ.extend P₂)
  · -- Show: environments agree on variables other than 0
    intros j s' hj
    unfold QEnv.extend
    split_ifs with h
    · -- Case: j.val = 0, but hj says j ≠ 0
      exfalso
      exact hj (Fin.ext h)
    · rfl
  · -- Show: environment at variable 0 is monotone
    intro s'
    unfold QEnv.extend
    simp only [Fin.val_zero]
    split_ifs
    · exact hle s'
    · exact hle s'

/-! ## Diamond-Box Duality in Quantale Setting

The classical duality `⟨a⟩φ = ¬[a](¬φ)` holds in a specific sense.
-/

/-- Diamond is bounded by supremum of transitions scaled by ⊤
    This holds when ⊤ acts as a right multiplicative bound -/
theorem diamond_le_sSup_top (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (a : Act) (φ : Formula Act n) (s : S)
    (h_top_bound : ∀ x : Q, x * ⊤ = x) :
    qSatisfies qlts ρ (Formula.diamond a φ) s ≤
    ⨆ s', qlts.trans s a s' := by
  simp only [qSatisfies]
  apply iSup_le
  intro s'
  calc qlts.trans s a s' * qSatisfies qlts ρ φ s'
      ≤ qlts.trans s a s' * ⊤ := by apply mul_le_mul'; exact le_refl _; exact le_top
    _ = qlts.trans s a s' := h_top_bound _
    _ ≤ ⨆ s'', qlts.trans s a s'' := le_iSup _ s'

/-- Box is bounded below by infimum of residuated transitions
    When φ is satisfied maximally (⊤) everywhere, box gives this bound -/
theorem iInf_le_box (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (a : Act) (φ : Formula Act n) (s : S)
    (h_top_sat : ∀ s', qSatisfies qlts ρ φ s' = ⊤) :
    ⨅ s', leftResiduate (qlts.trans s a s') ⊤ ≤
    qSatisfies qlts ρ (Formula.box a φ) s := by
  simp only [qSatisfies]
  -- Since qSat φ s' = ⊤ for all s', the indexed functions are equal pointwise
  have h_eq : (fun s' => leftResiduate (qlts.trans s a s') ⊤) =
              (fun s' => leftResiduate (qlts.trans s a s') (qSatisfies qlts ρ φ s')) := by
    ext s'
    rw [h_top_sat s']
  rw [h_eq]

/-! ## Connection to Boolean Semantics

When Q is a Boolean algebra, quantale semantics specializes appropriately.
The details are subtle and deferred.
-/

/-! ## Fixed Point Approximations

Least and greatest fixed points can be computed as limits of approximations.
-/

/-- The n-th approximation to μ X . φ -/
noncomputable def muApprox (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (φ : Formula Act (n + 1)) : ℕ → S → Q
  | 0 => fun _ => ⊥
  | k + 1 => fun s => qSatisfies qlts (ρ.extend (muApprox qlts ρ φ k)) φ s

/-- The n-th approximation to ν X . φ -/
noncomputable def nuApprox (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (φ : Formula Act (n + 1)) : ℕ → S → Q
  | 0 => fun _ => ⊤
  | k + 1 => fun s => qSatisfies qlts (ρ.extend (nuApprox qlts ρ φ k)) φ s

/-- μ approximations are increasing (requires positivity) -/
theorem muApprox_mono (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (φ : Formula Act (n + 1)) (hpos : φ.isPositive = true) (k : ℕ) (s : S) :
    muApprox qlts ρ φ k s ≤ muApprox qlts ρ φ (k + 1) s := by
  induction k generalizing s with
  | zero =>
    simp only [muApprox]
    exact bot_le
  | succ k ih =>
    simp only [muApprox]
    -- Use transformer_mono: if φ is positive, transformer is monotone
    -- By IH: muApprox k ≤ muApprox (k+1) pointwise
    -- So qSatisfies with k-approx ≤ qSatisfies with (k+1)-approx
    exact transformer_mono qlts ρ φ hpos ih s

/-- ν approximations are decreasing (requires positivity) -/
theorem nuApprox_antimono (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (φ : Formula Act (n + 1)) (hpos : φ.isPositive = true) (k : ℕ) (s : S) :
    nuApprox qlts ρ φ (k + 1) s ≤ nuApprox qlts ρ φ k s := by
  induction k generalizing s with
  | zero =>
    simp only [nuApprox]
    exact le_top
  | succ k ih =>
    simp only [nuApprox]
    -- Use transformer_mono: if φ is positive, transformer is monotone
    -- By IH: nuApprox (k+2) ≤ nuApprox (k+1) pointwise
    -- So qSatisfies with (k+2)-approx ≤ qSatisfies with (k+1)-approx
    exact transformer_mono qlts ρ φ hpos ih s

end Mettapedia.Logic.ModalQuantaleSemantics
