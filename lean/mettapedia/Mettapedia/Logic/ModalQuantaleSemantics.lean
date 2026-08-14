import Mathlib.Algebra.Order.Quantale
import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.Logic.ModalMuCalculus
import Mettapedia.Algebra.TemporalQuantale
import Mettapedia.Order.FiniteSetFixedPoints

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
    Transitions carry quantale values representing "strength" or "evidence".
    An absent transition has weight `⊥`; totality is an optional property of a
    particular system, not part of the carrier. -/
structure QLTS (Q : Type*) [CompleteLattice Q] (S : Type*) (Act : Type*) where
  /-- Transition strength: how strongly state s transitions to s' via action a -/
  trans : S → Act → S → Q

/-- Convert a Boolean LTS to QLTS using top/bottom values.
    Classical decidability selects `⊤` for authored transitions and `⊥` for
    absent transitions. -/
noncomputable def QLTS.ofLTS (lts : LTS S Act) : QLTS Q S Act where
  trans s a s' := @ite _ (lts.trans s a s') (Classical.propDecidable _) ⊤ ⊥

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

omit [IsCommQuantale Q] in
/-- Truth is maximal -/
theorem qSat_tt (qlts : QLTS Q S Act) (ρ : QEnv Q S n) (s : S) :
    qSatisfies qlts ρ Formula.tt s = ⊤ := rfl

omit [IsCommQuantale Q] in
/-- Falsity is minimal -/
theorem qSat_ff (qlts : QLTS Q S Act) (ρ : QEnv Q S n) (s : S) :
    qSatisfies qlts ρ Formula.ff s = ⊥ := rfl

omit [IsCommQuantale Q] in
/-- Conjunction is infimum -/
theorem qSat_conj (qlts : QLTS Q S Act) (ρ : QEnv Q S n)
    (φ ψ : Formula Act n) (s : S) :
    qSatisfies qlts ρ (Formula.conj φ ψ) s =
    qSatisfies qlts ρ φ s ⊓ qSatisfies qlts ρ ψ s := rfl

omit [IsCommQuantale Q] in
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

omit [CommSemigroup Q] [IsCommQuantale Q] in
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
              · simp; convert h_le t' using 1
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
              · simp; convert h_le t' using 1
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
              · simp; convert h_le t' using 1
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
              · simp; convert h_le t' using 1
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

omit [IsCommQuantale Q] in
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

/-! ## Boolean specialization

Ordinary truth is the commutative quantale whose multiplication is
conjunction.  The instances are local to this namespace: they are used only
to prove that `qSatisfies` recovers the pre-existing Boolean semantics and do
not change global notation or typeclass search for propositions.
-/

namespace Boolean

open Mettapedia.Order.FiniteSetFixedPoints

local instance : Mul Prop where
  mul := And

local instance : CommSemigroup Prop where
  mul_assoc := fun _ _ _ => propext and_assoc
  mul_comm := fun _ _ => propext and_comm

local instance : IsCommQuantale Prop :=
  IsCommQuantale.ofCommSemigroup (by
    intro proposition propositions
    change (proposition ∧ sSup propositions) =
      iSup (fun value : Prop =>
        iSup fun _ : value ∈ propositions => proposition ∧ value)
    apply propext
    simp)

@[simp] theorem prop_mul_iff (left right : Prop) :
    left * right ↔ left ∧ right := Iff.rfl

/-- Quantale residuation specializes to ordinary implication. -/
theorem prop_leftResiduate_iff (premise conclusion : Prop) :
    leftResiduate premise conclusion ↔ (premise → conclusion) := by
  constructor
  · intro residuated premiseProof
    exact modusPonens_left premise conclusion ⟨residuated, premiseProof⟩
  · intro implication
    exact (residuate_galois premise conclusion (premise → conclusion)).mp
      (fun conjunction => implication conjunction.2) implication

/-- View an ordinary transition relation as a proposition-valued weighted
transition system. -/
def ofLTS (lts : LTS S Act) : QLTS Prop S Act where
  trans := lts.trans

/-- Proposition-valued quantale semantics is exactly the ordinary Boolean
semantics, including least and greatest fixed points. -/
theorem qSatisfies_iff_satisfies (lts : LTS S Act) (ρ : Env S n)
    (formula : Formula Act n) (state : S) :
    qSatisfies (ofLTS lts) ρ formula state ↔
      satisfies lts ρ formula state := by
  induction formula generalizing state with
  | tt => rfl
  | ff => rfl
  | neg formula inductionHypothesis =>
      simp only [qSatisfies, satisfies, prop_leftResiduate_iff]
      exact not_congr (inductionHypothesis ρ state)
  | conj left right leftHypothesis rightHypothesis =>
      simp only [qSatisfies, satisfies]
      exact and_congr (leftHypothesis ρ state) (rightHypothesis ρ state)
  | disj left right leftHypothesis rightHypothesis =>
      simp only [qSatisfies, satisfies]
      exact or_congr (leftHypothesis ρ state) (rightHypothesis ρ state)
  | diamond action formula inductionHypothesis =>
      simp only [qSatisfies, satisfies, ofLTS, LTS.successors,
        Set.mem_setOf_eq, prop_mul_iff, iSup_Prop_eq]
      exact exists_congr fun target =>
        and_congr Iff.rfl (inductionHypothesis ρ target)
  | box action formula inductionHypothesis =>
      simp only [qSatisfies, satisfies, ofLTS, LTS.successors,
        Set.mem_setOf_eq, prop_leftResiduate_iff, iInf_Prop_eq]
      exact forall_congr' fun target =>
        imp_congr Iff.rfl (inductionHypothesis ρ target)
  | mu body inductionHypothesis =>
      simp only [qSatisfies, satisfies, iInf_Prop_eq]
      constructor
      · intro least candidate preFixed
        exact least candidate (fun target satisfied =>
          preFixed target
            ((inductionHypothesis (ρ.extend candidate) target).mp satisfied))
      · intro least candidate preFixed
        exact least candidate (fun target satisfied =>
          preFixed target
            ((inductionHypothesis (ρ.extend candidate) target).mpr satisfied))
  | nu body inductionHypothesis =>
      simp only [qSatisfies, satisfies, iSup_Prop_eq]
      constructor
      · rintro ⟨candidate, postFixed, member⟩
        exact ⟨candidate, member, fun target targetMember =>
          (inductionHypothesis (ρ.extend candidate) target).mp
            (postFixed target targetMember)⟩
      · rintro ⟨candidate, member, postFixed⟩
        exact ⟨candidate, (fun target targetMember =>
          (inductionHypothesis (ρ.extend candidate) target).mpr
            (postFixed target targetMember)), member⟩
  | var index => rfl

/-- Boolean satisfaction is monotone or antitone in one environment variable
according to the syntactically checked polarity of that variable.  This is a
direct specialization of `qSatisfies_mono_env`, not a second structural
induction. -/
theorem satisfies_mono_env (lts : LTS S Act) {n : Nat}
    (formula : Formula Act n) (index : Fin n) (polarity : Bool)
    (positive : formula.isPositiveIn index polarity = true) :
    ∀ (left right : Env S n),
      (∀ other state, other ≠ index → left other state = right other state) →
      (∀ state, left index state → right index state) →
      ∀ state, if polarity then satisfies lts left formula state →
        satisfies lts right formula state else
        satisfies lts right formula state → satisfies lts left formula state := by
  intro left right agree inclusion state
  have quantaleMonotonicity := qSatisfies_mono_env
    (ofLTS lts) formula index polarity positive left right agree inclusion state
  cases polarity with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at quantaleMonotonicity ⊢
      intro satisfied
      exact (qSatisfies_iff_satisfies lts left formula state).mp
        (quantaleMonotonicity
          ((qSatisfies_iff_satisfies lts right formula state).mpr satisfied))
  | true =>
      simp only [↓reduceIte] at quantaleMonotonicity ⊢
      intro satisfied
      exact (qSatisfies_iff_satisfies lts right formula state).mp
        (quantaleMonotonicity
          ((qSatisfies_iff_satisfies lts left formula state).mpr satisfied))

/-- The predicate transformer denoted by one positive fixed-point body,
bundled as Mathlib's monotone `OrderHom`. -/
noncomputable def bodyOrderHom (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true) :
    Set S →o Set S where
  toFun candidate := sat lts (ρ.extend candidate) body
  monotone' := by
    intro left right inclusion state satisfied
    exact satisfies_mono_env lts body 0 true positive
      (ρ.extend left) (ρ.extend right)
      (by
        intro index _state indexNotZero
        unfold Env.extend
        split
        · exfalso
          exact indexNotZero (Fin.ext ‹_›)
        · rfl)
      (by
        intro _state member
        exact inclusion member)
      state satisfied

/-- The impredicative least-fixed-point clause in `satisfies` is Mathlib's
Knaster--Tarski least fixed point for a positive body. -/
theorem satisfies_mu_iff_mem_lfp (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) :
    satisfies lts ρ (.mu body) state ↔
      state ∈ (bodyOrderHom lts ρ body positive).lfp := by
  let transformer := bodyOrderHom lts ρ body positive
  constructor
  · intro least
    apply least transformer.lfp
    intro target satisfied
    exact transformer.map_le_lfp le_rfl satisfied
  · intro member candidate preFixed
    exact transformer.lfp_le preFixed member

/-- The impredicative greatest-fixed-point clause in `satisfies` is Mathlib's
Knaster--Tarski greatest fixed point for a positive body. -/
theorem satisfies_nu_iff_mem_gfp (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) :
    satisfies lts ρ (.nu body) state ↔
      state ∈ (bodyOrderHom lts ρ body positive).gfp := by
  let transformer := bodyOrderHom lts ρ body positive
  constructor
  · rintro ⟨candidate, member, postFixed⟩
    exact transformer.le_gfp postFixed member
  · intro member
    exact ⟨transformer.gfp, member,
      fun target targetMember => transformer.gfp_le_map le_rfl targetMember⟩

/-- A positive least fixed point satisfies its usual unfolding equation. -/
theorem satisfies_mu_unfold_iff (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) :
    satisfies lts ρ (.mu body) state ↔
      satisfies lts
        (ρ.extend (sat lts ρ (.mu body))) body state := by
  let transformer := bodyOrderHom lts ρ body positive
  have satEq : sat lts ρ (.mu body) = transformer.lfp := by
    ext target
    exact satisfies_mu_iff_mem_lfp lts ρ body positive target
  change state ∈ sat lts ρ (.mu body) ↔
    state ∈ transformer (sat lts ρ (.mu body))
  rw [satEq, transformer.map_lfp]

/-- A positive greatest fixed point satisfies its usual unfolding equation. -/
theorem satisfies_nu_unfold_iff (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) :
    satisfies lts ρ (.nu body) state ↔
      satisfies lts
        (ρ.extend (sat lts ρ (.nu body))) body state := by
  let transformer := bodyOrderHom lts ρ body positive
  have satEq : sat lts ρ (.nu body) = transformer.gfp := by
    ext target
    exact satisfies_nu_iff_mem_gfp lts ρ body positive target
  change state ∈ sat lts ρ (.nu body) ↔
    state ∈ transformer (sat lts ρ (.nu body))
  rw [satEq, transformer.map_gfp]

/-- On a finite state carrier, least-fixed-point satisfaction is decided by
at most `Nat.card S` iterations from the empty set. -/
theorem satisfies_mu_iff_mem_iterate_empty [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) :
    satisfies lts ρ (.mu body) state ↔
      state ∈
        ((bodyOrderHom lts ρ body positive : Set S →o Set S) :
          Set S → Set S)^[Nat.card S] (∅ : Set S) := by
  rw [satisfies_mu_iff_mem_lfp]
  rw [Mettapedia.Order.FiniteSetFixedPoints.lfp_eq_iterate_empty]

/-- On a finite state carrier, greatest-fixed-point satisfaction is decided
by at most `Nat.card S` iterations from the universal set. -/
theorem satisfies_nu_iff_mem_iterate_univ [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) :
    satisfies lts ρ (.nu body) state ↔
      state ∈
        ((bodyOrderHom lts ρ body positive : Set S →o Set S) :
          Set S → Set S)^[Nat.card S] (Set.univ : Set S) := by
  rw [satisfies_nu_iff_mem_gfp]
  rw [Mettapedia.Order.FiniteSetFixedPoints.gfp_eq_iterate_univ]

/-! ### Semantic ranks consumed by finite evaluation games -/

/-- First finite approximation at which a state satisfies a positive least
fixed point. -/
noncomputable def muSemanticRank [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (satisfied : satisfies lts ρ (.mu body) state) : Nat :=
  lfpEntryRank (bodyOrderHom lts ρ body positive) state
    ((satisfies_mu_iff_mem_lfp lts ρ body positive state).mp satisfied)

theorem muSemanticRank_mem [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (satisfied : satisfies lts ρ (.mu body) state) :
    state ∈ lowerApproximation (bodyOrderHom lts ρ body positive)
      (muSemanticRank lts ρ body positive state satisfied) := by
  unfold muSemanticRank
  apply lfpEntryRank_mem

theorem muSemanticRank_pos [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (satisfied : satisfies lts ρ (.mu body) state) :
    0 < muSemanticRank lts ρ body positive state satisfied := by
  unfold muSemanticRank
  apply lfpEntryRank_pos

theorem muSemanticRank_le_card [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (satisfied : satisfies lts ρ (.mu body) state) :
    muSemanticRank lts ρ body positive state satisfied ≤ Nat.card S := by
  unfold muSemanticRank
  apply lfpEntryRank_le_card

/-- Membership in a lower approximation supplies genuine least-fixed-point
satisfaction, with semantic rank bounded by that approximation index. -/
theorem exists_muSemanticRank_le_of_mem_lowerApproximation [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (index : Nat)
    (atIndex : state ∈ lowerApproximation
      (bodyOrderHom lts ρ body positive) index) :
    ∃ satisfied : satisfies lts ρ (.mu body) state,
      muSemanticRank lts ρ body positive state satisfied ≤ index := by
  have member : state ∈ (bodyOrderHom lts ρ body positive).lfp :=
    lowerApproximation_le_lfp
      (bodyOrderHom lts ρ body positive) index atIndex
  let satisfied : satisfies lts ρ (.mu body) state :=
    (satisfies_mu_iff_mem_lfp lts ρ body positive state).mpr member
  refine ⟨satisfied, ?_⟩
  unfold muSemanticRank
  exact lfpEntryRank_min
    (bodyOrderHom lts ρ body positive) state member atIndex

/-- Entering the body of a true least fixed point spends one semantic-rank
step and interprets its bound variable by the previous approximation. -/
theorem muSemanticRank_unfold [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (satisfied : satisfies lts ρ (.mu body) state) :
    ∃ previous,
      muSemanticRank lts ρ body positive state satisfied = previous + 1 ∧
        satisfies lts
          (ρ.extend (lowerApproximation
            (bodyOrderHom lts ρ body positive) previous)) body state := by
  obtain ⟨previous, rankEq⟩ := Nat.exists_eq_succ_of_ne_zero
    (muSemanticRank_pos lts ρ body positive state satisfied).ne'
  refine ⟨previous, rankEq, ?_⟩
  have enters := muSemanticRank_mem lts ρ body positive state satisfied
  rw [rankEq, lowerApproximation_succ] at enters
  exact enters

/-- First finite approximation at which a state is eliminated while refuting
a positive greatest fixed point. -/
noncomputable def nuRefutationRank [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (refuted : ¬ satisfies lts ρ (.nu body) state) : Nat :=
  gfpExitRank (bodyOrderHom lts ρ body positive) state (by
    intro member
    exact refuted
      ((satisfies_nu_iff_mem_gfp lts ρ body positive state).mpr member))

theorem nuRefutationRank_not_mem [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (refuted : ¬ satisfies lts ρ (.nu body) state) :
    state ∉ upperApproximation (bodyOrderHom lts ρ body positive)
      (nuRefutationRank lts ρ body positive state refuted) := by
  unfold nuRefutationRank
  apply gfpExitRank_not_mem

theorem nuRefutationRank_pos [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (refuted : ¬ satisfies lts ρ (.nu body) state) :
    0 < nuRefutationRank lts ρ body positive state refuted := by
  unfold nuRefutationRank
  apply gfpExitRank_pos

theorem nuRefutationRank_le_card [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (refuted : ¬ satisfies lts ρ (.nu body) state) :
    nuRefutationRank lts ρ body positive state refuted ≤ Nat.card S := by
  unfold nuRefutationRank
  apply gfpExitRank_le_card

/-- Absence from an upper approximation supplies genuine greatest-fixed-point
refutation, with elimination rank bounded by that approximation index. -/
theorem exists_nuRefutationRank_le_of_not_mem_upperApproximation [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (index : Nat)
    (notAtIndex : state ∉ upperApproximation
      (bodyOrderHom lts ρ body positive) index) :
    ∃ refuted : ¬ satisfies lts ρ (.nu body) state,
      nuRefutationRank lts ρ body positive state refuted ≤ index := by
  have missing : state ∉ (bodyOrderHom lts ρ body positive).gfp := by
    intro member
    exact notAtIndex
      (gfp_le_upperApproximation
        (bodyOrderHom lts ρ body positive) index member)
  let refuted : ¬ satisfies lts ρ (.nu body) state := fun satisfied =>
    missing ((satisfies_nu_iff_mem_gfp lts ρ body positive state).mp satisfied)
  refine ⟨refuted, ?_⟩
  unfold nuRefutationRank
  exact gfpExitRank_min
    (bodyOrderHom lts ρ body positive) state missing notAtIndex

/-- Refuting a greatest fixed point likewise spends one elimination-rank
step and refutes its body at the previous upper approximation. -/
theorem nuRefutationRank_unfold [Finite S]
    (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) (refuted : ¬ satisfies lts ρ (.nu body) state) :
    ∃ previous,
      nuRefutationRank lts ρ body positive state refuted = previous + 1 ∧
        ¬ satisfies lts
          (ρ.extend (upperApproximation
            (bodyOrderHom lts ρ body positive) previous)) body state := by
  obtain ⟨previous, rankEq⟩ := Nat.exists_eq_succ_of_ne_zero
    (nuRefutationRank_pos lts ρ body positive state refuted).ne'
  refine ⟨previous, rankEq, ?_⟩
  have exits := nuRefutationRank_not_mem lts ρ body positive state refuted
  rw [rankEq, upperApproximation_succ] at exits
  exact exits

end Boolean

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
