/-
# Coin Flip: Classical Probability Through the K&S Pipeline

This demonstrates the full K&S pipeline on the simplest probability space:
a single coin flip (Bernoulli trial).

## The Pipeline

```
Events (4-element lattice) --[KSModel]--> NNReal --[Θ = id]--> ℝ
```

## Probability Space (Durrett Example 1.6.12)

- Ω = {Heads, Tails}
- Events E = P(Ω) = {∅, {H}, {T}, {H,T}} (4 elements)
- P({H}) = p, P({T}) = 1-p for parameter p ∈ [0,1]

## What This Demonstrates

1. A real probability space (not just the toy Three' chain)
2. The full Events → Scale → ℝ pipeline
3. Classical additivity: P(A ∪ B) = P(A) + P(B) for disjoint A, B
-/

import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Model

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples

open KnuthSkillingAlgebraBase

/-! ## The Event Space: 4-Element Boolean Algebra

The power set of a 2-element set:
- empty = ∅ (impossible)
- heads = {H}
- tails = {T}
- full = {H, T} (certain)

This is NOT a linear order (heads and tails are incomparable).
-/

/-- The 4-element coin flip event space -/
inductive CoinEvent : Type
  | empty : CoinEvent  -- ∅
  | heads : CoinEvent  -- {H}
  | tails : CoinEvent  -- {T}
  | full  : CoinEvent  -- {H, T}
  deriving DecidableEq, Repr

namespace CoinEvent

/-- Lattice ordering (subset inclusion):
    empty ≤ everything, everything ≤ full, heads ⊥ tails -/
def le : CoinEvent → CoinEvent → Prop
  | empty, _ => True
  | _, full => True
  | heads, heads => True
  | tails, tails => True
  | _, _ => False

instance : LE CoinEvent where le := le

instance : DecidableRel (· ≤ · : CoinEvent → CoinEvent → Prop) :=
  fun a b => by cases a <;> cases b <;> simp only [LE.le, le] <;> infer_instance

/-- Supremum (union) -/
def coinSup : CoinEvent → CoinEvent → CoinEvent
  | empty, b => b
  | a, empty => a
  | full, _ => full
  | _, full => full
  | heads, heads => heads
  | tails, tails => tails
  | heads, tails => full
  | tails, heads => full

/-- Infimum (intersection) -/
def coinInf : CoinEvent → CoinEvent → CoinEvent
  | full, b => b
  | a, full => a
  | empty, _ => empty
  | _, empty => empty
  | heads, heads => heads
  | tails, tails => tails
  | heads, tails => empty
  | tails, heads => empty

instance instTopCoinEvent : Top CoinEvent where top := full
instance instBotCoinEvent : Bot CoinEvent where bot := empty

-- Verify lattice properties
theorem le_refl' : ∀ a : CoinEvent, a ≤ a := by
  intro a; cases a <;> simp only [LE.le, le]

theorem le_trans' : ∀ a b c : CoinEvent, a ≤ b → b ≤ c → a ≤ c := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp only [LE.le, le] <;> intro _ _ <;> trivial

theorem le_antisymm' : ∀ a b : CoinEvent, a ≤ b → b ≤ a → a = b := by
  intro a b hab hba
  cases a <;> cases b <;> simp only [LE.le, le] at hab hba <;> rfl

theorem le_sup_left' : ∀ a b : CoinEvent, a ≤ coinSup a b := by
  intro a b; cases a <;> cases b <;> simp only [LE.le, le, coinSup]

theorem le_sup_right' : ∀ a b : CoinEvent, b ≤ coinSup a b := by
  intro a b; cases a <;> cases b <;> simp only [LE.le, le, coinSup]

theorem sup_le' : ∀ a b c : CoinEvent, a ≤ c → b ≤ c → coinSup a b ≤ c := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp only [LE.le, le, coinSup] <;> intro _ _ <;> trivial

theorem inf_le_left' : ∀ a b : CoinEvent, coinInf a b ≤ a := by
  intro a b; cases a <;> cases b <;> simp only [LE.le, le, coinInf]

theorem inf_le_right' : ∀ a b : CoinEvent, coinInf a b ≤ b := by
  intro a b; cases a <;> cases b <;> simp only [LE.le, le, coinInf]

theorem le_inf' : ∀ a b c : CoinEvent, a ≤ b → a ≤ c → a ≤ coinInf b c := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp only [LE.le, le, coinInf] <;> intro _ _ <;> trivial

theorem le_top' : ∀ a : CoinEvent, a ≤ full := by
  intro a; cases a <;> simp only [LE.le, le]

theorem bot_le' : ∀ a : CoinEvent, empty ≤ a := by
  intro a; cases a <;> simp only [LE.le, le]

theorem le_sup_inf' : ∀ a b c : CoinEvent, coinInf (coinSup a b) (coinSup a c) ≤ coinSup a (coinInf b c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp only [LE.le, le, coinSup, coinInf]

instance : Preorder CoinEvent where
  le_refl := le_refl'
  le_trans := le_trans'

instance : PartialOrder CoinEvent where
  le_antisymm := le_antisymm'

instance : SemilatticeSup CoinEvent where
  sup := coinSup
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := sup_le'

instance : SemilatticeInf CoinEvent where
  inf := coinInf
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := le_inf'

instance : Lattice CoinEvent where
  __ := inferInstanceAs (SemilatticeSup CoinEvent)
  __ := inferInstanceAs (SemilatticeInf CoinEvent)

instance : DistribLattice CoinEvent where
  le_sup_inf := le_sup_inf'

instance : BoundedOrder CoinEvent where
  top := full
  le_top := le_top'
  bot := empty
  bot_le := bot_le'

instance : PlausibilitySpace CoinEvent := inferInstance

/-! ## Computation Lemmas -/

-- Explicit computation lemmas for ⊔
@[simp] theorem sup_empty_left (b : CoinEvent) : empty ⊔ b = b := by cases b <;> rfl
@[simp] theorem sup_empty_right (a : CoinEvent) : a ⊔ empty = a := by cases a <;> rfl
@[simp] theorem sup_full_left (b : CoinEvent) : full ⊔ b = full := by cases b <;> rfl
@[simp] theorem sup_full_right (a : CoinEvent) : a ⊔ full = full := by cases a <;> rfl
@[simp] theorem sup_heads_heads : heads ⊔ heads = heads := rfl
@[simp] theorem sup_tails_tails : tails ⊔ tails = tails := rfl
@[simp] theorem sup_heads_tails : heads ⊔ tails = full := rfl
@[simp] theorem sup_tails_heads : tails ⊔ heads = full := rfl

-- Explicit computation lemmas for ⊓
@[simp] theorem inf_empty_left (b : CoinEvent) : empty ⊓ b = empty := by cases b <;> rfl
@[simp] theorem inf_empty_right (a : CoinEvent) : a ⊓ empty = empty := by cases a <;> rfl
@[simp] theorem inf_full_left (b : CoinEvent) : full ⊓ b = b := by cases b <;> rfl
@[simp] theorem inf_full_right (a : CoinEvent) : a ⊓ full = a := by cases a <;> rfl
@[simp] theorem inf_heads_heads : heads ⊓ heads = heads := rfl
@[simp] theorem inf_tails_tails : tails ⊓ tails = tails := rfl
@[simp] theorem inf_heads_tails : heads ⊓ tails = empty := rfl
@[simp] theorem inf_tails_heads : tails ⊓ heads = empty := rfl

/-! ## Disjointness for CoinEvent -/

/-- Characterize disjoint pairs -/
theorem disjoint_characterize (a b : CoinEvent) :
    Disjoint a b ↔ (a = empty ∨ b = empty ∨ (a = heads ∧ b = tails) ∨ (a = tails ∧ b = heads)) := by
  constructor
  · intro h
    rw [disjoint_iff] at h
    -- h : a ⊓ b = ⊥ (i.e., a ⊓ b = empty)
    cases a with
    | empty => left; rfl
    | heads =>
      cases b with
      | empty => right; left; rfl
      | heads => simp at h  -- heads ⊓ heads = heads ≠ empty
      | tails => right; right; left; exact ⟨rfl, rfl⟩
      | full => simp at h  -- heads ⊓ full = heads ≠ empty
    | tails =>
      cases b with
      | empty => right; left; rfl
      | heads => right; right; right; exact ⟨rfl, rfl⟩
      | tails => simp at h  -- tails ⊓ tails = tails ≠ empty
      | full => simp at h  -- tails ⊓ full = tails ≠ empty
    | full =>
      cases b with
      | empty => right; left; rfl
      | heads => simp at h  -- full ⊓ heads = heads ≠ empty
      | tails => simp at h  -- full ⊓ tails = tails ≠ empty
      | full => simp at h  -- full ⊓ full = full ≠ empty
  · intro h
    rw [disjoint_iff]
    rcases h with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Bot.bot]

/-! ## The Coin Flip Model -/

/-- A coin flip KSModel with parameter p ∈ [0,1].

    The valuation assigns:
    - v(empty) = 0
    - v(heads) = p (probability of Heads)
    - v(tails) = 1-p (probability of Tails)
    - v(full) = 1 (certain event)

    Note: We use NNReal as our K&S algebra (op = +, ident = 0). -/
noncomputable def coinFlipModel (p : NNReal) (hp : p ≤ 1) : KSModel CoinEvent NNReal where
  v := fun a => match a with
    | empty => 0
    | heads => p
    | tails => 1 - p
    | full => 1
  mono := fun a b hab => by
    cases a with
    | empty => exact zero_le _
    | heads =>
      cases b with
      | empty => simp only [LE.le, le] at hab
      | heads => exact le_refl _
      | tails => simp only [LE.le, le] at hab
      | full => exact hp
    | tails =>
      cases b with
      | empty => simp only [LE.le, le] at hab
      | heads => simp only [LE.le, le] at hab
      | tails => exact le_refl _
      | full => exact tsub_le_self
    | full =>
      cases b with
      | empty => simp only [LE.le, le] at hab
      | heads => simp only [LE.le, le] at hab
      | tails => simp only [LE.le, le] at hab
      | full => exact le_refl _
  v_bot := rfl
  v_sup_of_disjoint := fun {a b} h => by
    rw [disjoint_characterize] at h
    simp only [nnreal_op_is_add]
    rcases h with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- a = empty: v(empty ⊔ b) = v(b) = 0 + v(b)
      cases b <;> simp
    · -- b = empty: v(a ⊔ empty) = v(a) = v(a) + 0
      cases a <;> simp
    · -- a = heads, b = tails: v(full) = 1 = p + (1-p)
      simp only [sup_heads_tails]
      exact (add_tsub_cancel_of_le hp).symm
    · -- a = tails, b = heads: v(full) = 1 = (1-p) + p
      simp only [sup_tails_heads]
      exact (tsub_add_cancel_of_le hp).symm

/-- Standard fair coin: p = 1/2 -/
noncomputable def fairCoinModel : KSModel CoinEvent NNReal :=
  coinFlipModel (1/2) (by norm_num)

/-! ## Verification: Classical Probability Axioms -/

/-- P(∅) = 0 -/
theorem coinFlip_empty (p : NNReal) (hp : p ≤ 1) :
    (coinFlipModel p hp).v empty = 0 := rfl

/-- P(Ω) = 1 -/
theorem coinFlip_total (p : NNReal) (hp : p ≤ 1) :
    (coinFlipModel p hp).v full = 1 := rfl

/-- P(Heads) = p -/
theorem coinFlip_heads (p : NNReal) (hp : p ≤ 1) :
    (coinFlipModel p hp).v heads = p := rfl

/-- P(Tails) = 1 - p -/
theorem coinFlip_tails (p : NNReal) (hp : p ≤ 1) :
    (coinFlipModel p hp).v tails = 1 - p := rfl

/-- Additivity: P(Heads ∪ Tails) = P(Heads) + P(Tails) -/
theorem coinFlip_additivity (p : NNReal) (hp : p ≤ 1) :
    (coinFlipModel p hp).v (heads ⊔ tails) =
    (coinFlipModel p hp).v heads + (coinFlipModel p hp).v tails := by
  -- heads ⊔ tails = full in CoinEvent
  have h_sup : (heads : CoinEvent) ⊔ tails = full := rfl
  rw [h_sup, coinFlip_total, coinFlip_heads, coinFlip_tails]
  -- 1 = p + (1-p)
  exact (add_tsub_cancel_of_le hp).symm

/-- P(Heads) + P(Tails) = 1 -/
theorem coinFlip_sum_to_one (p : NNReal) (hp : p ≤ 1) :
    (coinFlipModel p hp).v heads + (coinFlipModel p hp).v tails = 1 := by
  simp only [coinFlip_heads, coinFlip_tails, add_tsub_cancel_of_le hp]

/-! ## The Full Pipeline: Events → NNReal → ℝ -/

/-- For NNReal, the representation Θ is just coercion to ℝ.

    This gives us the full pipeline:
    - Events E (CoinEvent)
    - Scale S (NNReal) via coinFlipModel
    - Reals ℝ via Θ = (↑·)

    The composed valuation v_ℝ : CoinEvent → ℝ is a classical probability measure. -/
noncomputable def coinFlipWithRepresentation (p : NNReal) (hp : p ≤ 1) :
    KSModelWithRepresentation CoinEvent NNReal where
  toKSModel := coinFlipModel p hp
  Θ := fun x => (x : ℝ)  -- coercion NNReal → ℝ
  Θ_orderEmb := fun x y => ⟨NNReal.coe_le_coe.mpr, NNReal.coe_le_coe.mp⟩
  Θ_ident := by simp [nnreal_ident_is_zero]
  Θ_hom := fun x y => by simp [nnreal_op_is_add, NNReal.coe_add]

/-- The composed valuation v_ℝ gives classical probability in ℝ -/
noncomputable def coinFlipProbability (p : NNReal) (hp : p ≤ 1) : CoinEvent → ℝ :=
  (coinFlipWithRepresentation p hp).v_ℝ

/-- P_ℝ(Heads) = p (as a real number) -/
theorem coinFlip_real_heads (p : NNReal) (hp : p ≤ 1) :
    coinFlipProbability p hp heads = (p : ℝ) := by
  unfold coinFlipProbability KSModelWithRepresentation.v_ℝ coinFlipWithRepresentation
  simp only [Function.comp_apply, coinFlip_heads]

/-- P_ℝ(Tails) = 1 - p (as a real number) -/
theorem coinFlip_real_tails (p : NNReal) (hp : p ≤ 1) :
    coinFlipProbability p hp tails = 1 - (p : ℝ) := by
  unfold coinFlipProbability KSModelWithRepresentation.v_ℝ coinFlipWithRepresentation
  simp only [Function.comp_apply, coinFlip_tails, NNReal.coe_sub hp, NNReal.coe_one]

/-! ## Summary -/

/-- The coin flip demonstrates the full K&S pipeline:
    1. Events form a PlausibilitySpace (4-element Boolean algebra)
    2. KSModel connects events to NNReal scale
    3. Representation Θ embeds NNReal into ℝ
    4. Composed v_ℝ is a classical probability measure -/
theorem coinFlip_is_ks_compatible :
    (∃ _ : PlausibilitySpace CoinEvent, True) ∧
    (∃ _ : KSModel CoinEvent NNReal, True) ∧
    (∃ _ : KSModelWithRepresentation CoinEvent NNReal, True) := by
  exact ⟨⟨inferInstance, trivial⟩,
         ⟨fairCoinModel, trivial⟩,
         ⟨coinFlipWithRepresentation (1/2) (by norm_num), trivial⟩⟩

end CoinEvent

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples
