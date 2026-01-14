/-
# Three-Element Chain: Minimal Non-Boolean Distributive Lattice

Demonstrates that K&S valuations work on non-Boolean distributive lattices.

## The Lattice
The 3-element chain: ⊥ < mid < ⊤
- Distributive: chains are always distributive
- NOT Boolean: `mid` has no complement (no `x` with `mid ⊔ x = ⊤` and `mid ⊓ x = ⊥`)

## The Valuation
v(⊥) = 0, v(mid) = p, v(⊤) = 1 for any 0 < p < 1

## Why This Matters
- Shows K&S framework genuinely doesn't require negation/complements
- Minimal counterexample to "probability requires Boolean algebras"
- Disjointness is vacuous in chains (only ⊥ is disjoint from anything)
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Bridge

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples

/-! ## The Three-Element Chain Type -/

/-- Three-element chain: Bot < Mid < Top -/
inductive Three : Type where
  | bot : Three
  | mid : Three
  | top : Three
  deriving DecidableEq, Repr

namespace Three

/-- Convert Three to Nat for ordering -/
def toNat : Three → ℕ
  | bot => 0
  | mid => 1
  | top => 2

@[simp] lemma bot_toNat : Three.bot.toNat = 0 := rfl
@[simp] lemma mid_toNat : Three.mid.toNat = 1 := rfl
@[simp] lemma top_toNat : Three.top.toNat = 2 := rfl

lemma toNat_injective : Function.Injective toNat := fun a b h => by
  cases a <;> cases b <;> simp_all [toNat]

/-- Linear order on Three -/
instance : LinearOrder Three where
  le := fun a b => a.toNat ≤ b.toNat
  lt := fun a b => a.toNat < b.toNat
  max := fun a b => if a.toNat ≤ b.toNat then b else a
  min := fun a b => if a.toNat ≤ b.toNat then a else b
  toDecidableEq := inferInstance
  toDecidableLE := fun a b => inferInstanceAs (Decidable (a.toNat ≤ b.toNat))
  toDecidableLT := fun a b => inferInstanceAs (Decidable (a.toNat < b.toNat))
  le_refl := fun a => Nat.le_refl _
  le_trans := fun _ _ _ => Nat.le_trans
  le_total := fun a b => Nat.le_total _ _
  le_antisymm := fun a b hab hba => toNat_injective (Nat.le_antisymm hab hba)
  lt_iff_le_not_ge := fun _ _ => Nat.lt_iff_le_not_le

/-- Three forms a lattice (as a chain, sup = max, inf = min) -/
instance : Lattice Three where
  sup := max
  inf := min
  le_sup_left := le_max_left
  le_sup_right := le_max_right
  sup_le := fun _ _ _ hac hbc => max_le hac hbc
  inf_le_left := min_le_left
  inf_le_right := min_le_right
  le_inf := fun _ _ _ hab hac => le_min hab hac

/-- Three is a distributive lattice (all chains are) -/
instance : DistribLattice Three where
  le_sup_inf := fun _ _ _ => le_sup_inf

/-- Three has bounded order -/
instance : BoundedOrder Three where
  top := top
  le_top := fun a => by cases a <;> decide
  bot := bot
  bot_le := fun a => by cases a <;> decide

/-- Three is a PlausibilitySpace -/
instance : PlausibilitySpace Three := inferInstance

/-! ## Non-Boolean Property -/

/-- Key theorem: Three is NOT Boolean. There is no complement for `mid`.

    For `mid` to have a complement `c`, we need:
    - `mid ⊔ c = top` (join is top)
    - `mid ⊓ c = bot` (meet is bot)

    But in a chain:
    - If c = bot: mid ⊔ bot = mid ≠ top ✗
    - If c = mid: mid ⊓ mid = mid ≠ bot ✗
    - If c = top: mid ⊓ top = mid ≠ bot ✗

    No element works! -/
theorem not_boolean : ¬∃ (compl : Three → Three),
    (∀ a, a ⊔ compl a = ⊤) ∧ (∀ a, a ⊓ compl a = ⊥) := by
  intro ⟨compl, hsup, hinf⟩
  have h1 : mid ⊔ compl mid = ⊤ := hsup mid
  have h2 : mid ⊓ compl mid = ⊥ := hinf mid
  cases hc : compl mid with
  | bot =>
    -- mid ⊔ bot = max(mid, bot) = mid ≠ top
    simp only [hc] at h1
    -- h1 : mid ⊔ bot = ⊤, but mid ⊔ bot = mid by definition
    have : mid ⊔ bot = mid := by decide
    rw [this] at h1
    exact absurd h1 (by decide)
  | mid =>
    -- mid ⊓ mid = min(mid, mid) = mid ≠ bot
    simp only [hc] at h2
    have : mid ⊓ mid = mid := by decide
    rw [this] at h2
    exact absurd h2 (by decide)
  | top =>
    -- mid ⊓ top = min(mid, top) = mid ≠ bot
    simp only [hc] at h2
    have : mid ⊓ top = mid := by decide
    rw [this] at h2
    exact absurd h2 (by decide)

/-! ## Valuation on Three -/

/-- A valuation on Three with parameter p ∈ (0,1) -/
def threeValuation (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : Valuation Three where
  val := fun a => match a with
    | bot => 0
    | mid => p
    | top => 1
  monotone := fun a b hab => by
    cases a <;> cases b <;> simp only []
    case bot.bot => exact le_refl _
    case bot.mid => exact le_of_lt hp0
    case bot.top => exact le_of_lt (by linarith : (0 : ℝ) < 1)
    case mid.bot => exact absurd hab (by decide)
    case mid.mid => exact le_refl _
    case mid.top => exact le_of_lt hp1
    case top.bot => exact absurd hab (by decide)
    case top.mid => exact absurd hab (by decide)
    case top.top => exact le_refl _
  val_bot := rfl
  val_top := rfl

/-- Standard valuation with p = 1/2 -/
noncomputable def standardValuation : Valuation Three :=
  threeValuation (1/2) (by norm_num) (by norm_num)

/-! ## Disjointness in Chains -/

/-- In a chain, two elements are disjoint iff at least one is bot -/
theorem disjoint_iff_has_bot (a b : Three) : Disjoint a b ↔ a = bot ∨ b = bot := by
  constructor
  · intro h
    rw [disjoint_iff] at h
    -- h : a ⊓ b = ⊥
    cases a <;> cases b <;> simp_all
  · intro h
    cases h with
    | inl ha => subst ha; exact disjoint_bot_left
    | inr hb => subst hb; exact disjoint_bot_right

/-- bot as Three equals ⊥ as BoundedOrder -/
@[simp] lemma bot_eq_boundedBot : (bot : Three) = ⊥ := rfl

/-- Additivity on disjoint joins holds (trivially, since one must be ⊥) -/
theorem valuation_additive_on_disjoint (v : Valuation Three) (a b : Three)
    (h : Disjoint a b) : v.val (a ⊔ b) = v.val a + v.val b := by
  rw [disjoint_iff_has_bot] at h
  cases h with
  | inl ha =>
    subst ha
    simp only [bot_eq_boundedBot, bot_sup_eq, v.val_bot, zero_add]
  | inr hb =>
    subst hb
    simp only [bot_eq_boundedBot, sup_bot_eq, v.val_bot, add_zero]

/-! ## AdditiveValuation Instance -/

/-- An AdditiveValuation on Three with parameter p ∈ (0,1)

In a chain, additivity on disjoint joins is trivial since the only
disjoint pairs involve ⊥. This demonstrates K&S works on non-Boolean lattices. -/
def threeAdditiveValuation (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    AdditiveValuation Three where
  val := fun a => match a with
    | bot => 0
    | mid => p
    | top => 1
  monotone := fun a b hab => by
    cases a <;> cases b <;> simp only []
    case bot.bot => exact le_refl _
    case bot.mid => exact le_of_lt hp0
    case bot.top => exact le_of_lt (by linarith : (0 : ℝ) < 1)
    case mid.bot => exact absurd hab (by decide)
    case mid.mid => exact le_refl _
    case mid.top => exact le_of_lt hp1
    case top.bot => exact absurd hab (by decide)
    case top.mid => exact absurd hab (by decide)
    case top.top => exact le_refl _
  val_bot := rfl
  val_top := rfl
  additive_disjoint := fun {a b} h => by
    rw [disjoint_iff_has_bot] at h
    cases h with
    | inl ha =>
      subst ha
      simp only [bot_eq_boundedBot, bot_sup_eq, zero_add]
    | inr hb =>
      subst hb
      simp only [bot_eq_boundedBot, sup_bot_eq, add_zero]

/-- Standard additive valuation with p = 1/2 -/
noncomputable def standardAdditiveValuation : AdditiveValuation Three :=
  threeAdditiveValuation (1/2) (by norm_num) (by norm_num)

/-! ## Summary -/

/--
The Three-element chain demonstrates:
1. K&S valuations exist on non-Boolean distributive lattices
2. No complement operation is needed
3. Additivity on disjoint joins is well-defined (trivially, in this case)

This is the minimal example showing K&S genuinely generalizes beyond Boolean algebras.
-/
theorem three_is_ks_compatible :
    (∃ _ : PlausibilitySpace Three, True) ∧
    (∃ _ : Valuation Three, True) ∧
    (∃ _ : AdditiveValuation Three, True) ∧
    ¬∃ (compl : Three → Three), (∀ a, a ⊔ compl a = ⊤) ∧ (∀ a, a ⊓ compl a = ⊥) := by
  exact ⟨⟨inferInstance, trivial⟩, ⟨standardValuation, trivial⟩,
         ⟨standardAdditiveValuation, trivial⟩, not_boolean⟩

end Three

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples
