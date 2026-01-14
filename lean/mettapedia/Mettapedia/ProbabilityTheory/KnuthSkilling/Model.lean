/-
# KSModel: Bridge from Events to Plausibility Scale

This module provides the formal connection between:
- `PlausibilitySpace E` (distributive lattice of events)
- `KnuthSkillingAlgebraBase S` (linearly ordered plausibility scale with ⊕)

## The Key Insight

Rather than trying to "induce" ⊕ on range(v) by picking representative events
(which leads to well-definedness nightmares), we keep the scale S already
equipped with its K&S algebra structure.

The bridge is the single axiom: `v(a ⊔ b) = v(a) ⊕ v(b)` for disjoint `a, b`.

## Full Pipeline

The complete K&S framework forms a pipeline:
1. **Events → Scale**: A `KSModel` maps events E to scale S with v(a ⊔ b) = v(a) ⊕ v(b)
2. **Scale → Reals**: The representation theorem embeds S into (ℝ, +)
3. **Composition**: Events map to ℝ via Θ ∘ v, yielding standard probability

## References

- Knuth & Skilling, "Foundations of Inference" (2012), Sections 3-4
- This approach follows a suggestion by GPT-5 Pro to avoid well-definedness issues
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open KnuthSkillingAlgebraBase

/-! ## KSModel: The Bridge Structure -/

/-- A `KSModel` connects a PlausibilitySpace (events) to a KnuthSkillingAlgebra (scale).

The key axiom `v_sup_of_disjoint` says that for disjoint events a, b:
  v(a ⊔ b) = v(a) ⊕ v(b)

This mirrors K&S's conceptual approach: ⊕ is the scalar operation that makes
v additive on disjoint joins.

**Note**: We don't require `v_top` because the K&S algebra has no inherent maximum.
Normalization (v(⊤) = 1) happens when we compose with the representation theorem
and choose a scale factor for Θ. -/
structure KSModel (E S : Type*)
    [PlausibilitySpace E] [KnuthSkillingAlgebraBase S] where
  /-- The valuation function from events to the plausibility scale -/
  v : E → S
  /-- Monotonicity: larger events have larger plausibility -/
  mono : Monotone v
  /-- The impossible event maps to the identity element -/
  v_bot : v ⊥ = ident
  /-- Additivity on disjoint joins: the fundamental K&S axiom -/
  v_sup_of_disjoint : ∀ {a b : E}, Disjoint a b → v (a ⊔ b) = op (v a) (v b)

namespace KSModel

variable {E S : Type*} [PlausibilitySpace E] [KnuthSkillingAlgebraBase S]
variable (m : KSModel E S)

/-! ### Basic Properties -/

/-- The valuation is nonnegative (in K&S sense: v(a) ≥ ident) -/
theorem v_ident_le (a : E) : ident ≤ m.v a := by
  have h := m.mono (bot_le : (⊥ : E) ≤ a)
  simp only [m.v_bot] at h
  exact h

/-- Joining with ⊥ doesn't change the value -/
theorem v_sup_bot (a : E) : m.v (a ⊔ ⊥) = m.v a := by
  simp only [sup_bot_eq]

/-- Joining ⊥ from the left doesn't change the value -/
theorem v_bot_sup (a : E) : m.v (⊥ ⊔ a) = m.v a := by
  simp only [bot_sup_eq]

/-- Alternative form: v(⊥ ⊔ a) = ident ⊕ v(a) = v(a) -/
theorem v_bot_sup' (a : E) : m.v (⊥ ⊔ a) = op ident (m.v a) := by
  rw [m.v_sup_of_disjoint disjoint_bot_left, m.v_bot]

/-- Verify the identity law is consistent -/
theorem v_bot_sup_consistent (a : E) : op ident (m.v a) = m.v a := by
  rw [op_ident_left]

/-! ### Compatibility with K&S Axioms -/

/-- The operation ⊕ is associative (inherited from S) -/
theorem op_assoc' (x y z : S) : op (op x y) z = op x (op y z) :=
  op_assoc x y z

/-- Three-way additivity for pairwise disjoint events -/
theorem v_sup_three {a b c : E}
    (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) :
    m.v (a ⊔ b ⊔ c) = op (op (m.v a) (m.v b)) (m.v c) := by
  have h_ab_c : Disjoint (a ⊔ b) c := by
    rw [disjoint_iff] at hab hac hbc ⊢
    calc (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) := inf_sup_right a b c
      _ = ⊥ ⊔ ⊥ := by rw [hac, hbc]
      _ = ⊥ := sup_idem ⊥
  calc m.v (a ⊔ b ⊔ c)
      = op (m.v (a ⊔ b)) (m.v c) := m.v_sup_of_disjoint h_ab_c
    _ = op (op (m.v a) (m.v b)) (m.v c) := by rw [m.v_sup_of_disjoint hab]

/-- Three-way additivity, right-associated form -/
theorem v_sup_three' {a b c : E}
    (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) :
    m.v (a ⊔ b ⊔ c) = op (m.v a) (op (m.v b) (m.v c)) := by
  rw [m.v_sup_three hab hac hbc, op_assoc]

/-! ### Monotonicity Consequences -/

/-- If a ≤ b, then v(a) ≤ v(b) -/
theorem v_le_of_le {a b : E} (h : a ≤ b) : m.v a ≤ m.v b :=
  m.mono h

-- Note: Strict monotonicity (a < b → v(a) < v(b)) requires additional structure
-- (separation property). For now, we only have weak monotonicity.

end KSModel

/-! ## Composition with Representation Theorem -/

/-- When we have a KSModel and a representation Θ : S → ℝ, we can compose them
    to get a valuation v_ℝ : E → ℝ that satisfies the classical probability axioms. -/
structure KSModelWithRepresentation (E S : Type*)
    [PlausibilitySpace E] [KnuthSkillingAlgebraBase S] extends KSModel E S where
  /-- The representation into reals -/
  Θ : S → ℝ
  /-- Θ is an order embedding -/
  Θ_orderEmb : ∀ x y : S, x ≤ y ↔ Θ x ≤ Θ y
  /-- Θ maps identity to 0 -/
  Θ_ident : Θ ident = 0
  /-- Θ is a homomorphism -/
  Θ_hom : ∀ x y : S, Θ (op x y) = Θ x + Θ y

namespace KSModelWithRepresentation

variable {E S : Type*} [PlausibilitySpace E] [KnuthSkillingAlgebraBase S]
variable (m : KSModelWithRepresentation E S)

/-- The composed valuation: events → ℝ -/
def v_ℝ : E → ℝ := m.Θ ∘ m.v

/-- The composed valuation is monotone -/
theorem v_ℝ_mono : Monotone m.v_ℝ := fun a b h => by
  unfold v_ℝ
  simp only [Function.comp_apply]
  exact (m.Θ_orderEmb _ _).mp (m.mono h)

/-- The composed valuation maps ⊥ to 0 -/
theorem v_ℝ_bot : m.v_ℝ ⊥ = 0 := by
  unfold v_ℝ
  simp only [Function.comp_apply, m.v_bot, m.Θ_ident]

/-- The composed valuation is additive on disjoint joins -/
theorem v_ℝ_sup_of_disjoint {a b : E} (h : Disjoint a b) :
    m.v_ℝ (a ⊔ b) = m.v_ℝ a + m.v_ℝ b := by
  unfold v_ℝ
  simp only [Function.comp_apply]
  rw [m.v_sup_of_disjoint h, m.Θ_hom]

/-- The composed valuation is nonnegative -/
theorem v_ℝ_nonneg (a : E) : 0 ≤ m.v_ℝ a := by
  have h := m.v_ident_le a
  rw [← m.Θ_ident]
  exact (m.Θ_orderEmb _ _).mp h

end KSModelWithRepresentation

/-! ## NNReal as a K&S Algebra

The nonnegative reals NNReal with addition form a KnuthSkillingAlgebraBase:
- op = (+) : addition
- ident = 0 : the additive identity
- All K&S axioms are satisfied
-/

/-- NNReal with addition forms a KnuthSkillingAlgebraBase. -/
noncomputable instance instKSAlgebraNNReal : KnuthSkillingAlgebraBase NNReal where
  op := (· + ·)
  ident := 0
  op_assoc := add_assoc
  op_ident_right := add_zero
  op_ident_left := zero_add
  op_strictMono_left := fun _ => fun _ _ h => add_lt_add_right h _
  op_strictMono_right := fun _ => fun _ _ h => add_lt_add_left h _
  ident_le := zero_le

/-- In instKSAlgebraNNReal, op is addition -/
theorem nnreal_op_is_add : @op NNReal instKSAlgebraNNReal = (· + ·) := rfl

/-- In instKSAlgebraNNReal, ident is zero -/
theorem nnreal_ident_is_zero : @ident NNReal instKSAlgebraNNReal = 0 := rfl

/-! ## Example: Three-Element Chain with NNReal Scale -/

/-- The three-element chain as a PlausibilitySpace -/
inductive Three' : Type where
  | bot : Three'
  | mid : Three'
  | top : Three'
  deriving DecidableEq

namespace Three'

def toNat : Three' → ℕ
  | bot => 0
  | mid => 1
  | top => 2

instance : LinearOrder Three' where
  le := fun a b => a.toNat ≤ b.toNat
  lt := fun a b => a.toNat < b.toNat
  le_refl := fun _ => Nat.le_refl _
  le_trans := fun _ _ _ => Nat.le_trans
  le_antisymm := fun a b hab hba => by
    cases a <;> cases b <;> simp_all [toNat]
  le_total := fun a b => Nat.le_total _ _
  lt_iff_le_not_ge := fun _ _ => Nat.lt_iff_le_not_le
  toDecidableEq := inferInstance
  toDecidableLE := fun a b => inferInstanceAs (Decidable (a.toNat ≤ b.toNat))
  toDecidableLT := fun a b => inferInstanceAs (Decidable (a.toNat < b.toNat))
  max := fun a b => if a.toNat ≤ b.toNat then b else a
  min := fun a b => if a.toNat ≤ b.toNat then a else b

instance : Lattice Three' where
  sup := max
  inf := min
  le_sup_left := le_max_left
  le_sup_right := le_max_right
  sup_le := fun _ _ _ hac hbc => max_le hac hbc
  inf_le_left := min_le_left
  inf_le_right := min_le_right
  le_inf := fun _ _ _ hab hac => le_min hab hac

instance : DistribLattice Three' where
  le_sup_inf := fun _ _ _ => le_sup_inf

instance : BoundedOrder Three' where
  top := top
  le_top := fun a => by cases a <;> decide
  bot := bot
  bot_le := fun a => by cases a <;> decide

instance : PlausibilitySpace Three' := inferInstance

/-- In Three', disjointness means at least one is bot -/
theorem disjoint_iff_has_bot (a b : Three') : Disjoint a b ↔ a = bot ∨ b = bot := by
  constructor
  · intro h
    rw [disjoint_iff] at h
    cases a <;> cases b <;> simp_all
  · intro h
    cases h with
    | inl ha => subst ha; exact disjoint_bot_left
    | inr hb => subst hb; exact disjoint_bot_right

/-- A KSModel on Three' with scale NNReal.
    v(bot) = 0, v(mid) = p, v(top) = 1 for a given p ∈ (0,1). -/
noncomputable def threeKSModel (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1) :
    KSModel Three' NNReal where
  v := fun a => match a with
    | bot => 0
    | mid => p
    | top => 1
  mono := fun a b hab => by
    cases a <;> cases b <;> simp only []
    case bot.bot => exact le_refl _
    case bot.mid => exact le_of_lt hp0
    case bot.top => exact zero_le _
    case mid.bot => exact absurd hab (by decide)
    case mid.mid => exact le_refl _
    case mid.top => exact le_of_lt hp1
    case top.bot => exact absurd hab (by decide)
    case top.mid => exact absurd hab (by decide)
    case top.top => exact le_refl _
  v_bot := rfl
  v_sup_of_disjoint := fun {a b} h => by
    rw [disjoint_iff_has_bot] at h
    cases h with
    | inl ha =>
      subst ha
      simp only [nnreal_op_is_add, zero_add]
      cases b <;> rfl
    | inr hb =>
      subst hb
      simp only [nnreal_op_is_add, add_zero]
      cases a <;> rfl

/-- Standard model with p = 1/2 -/
noncomputable def standardThreeKSModel : KSModel Three' NNReal :=
  threeKSModel (1/2 : NNReal) (by norm_num) (by norm_num)

/-- Verify the model satisfies the key K&S axiom -/
theorem threeKSModel_additive (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1)
    {a b : Three'} (h : Disjoint a b) :
    (threeKSModel p hp0 hp1).v (a ⊔ b) =
    @op NNReal instKSAlgebraNNReal ((threeKSModel p hp0 hp1).v a) ((threeKSModel p hp0 hp1).v b) :=
  (threeKSModel p hp0 hp1).v_sup_of_disjoint h

/-- Three' is not Boolean -/
theorem not_boolean : ¬∃ (compl : Three' → Three'),
    (∀ a, a ⊔ compl a = ⊤) ∧ (∀ a, a ⊓ compl a = ⊥) := by
  intro ⟨compl, hsup, hinf⟩
  have h1 : mid ⊔ compl mid = ⊤ := hsup mid
  have h2 : mid ⊓ compl mid = ⊥ := hinf mid
  cases hc : compl mid with
  | bot =>
    simp only [hc] at h1
    have : mid ⊔ bot = mid := by decide
    rw [this] at h1
    exact absurd h1 (by decide)
  | mid =>
    simp only [hc] at h2
    have : mid ⊓ mid = mid := by decide
    rw [this] at h2
    exact absurd h2 (by decide)
  | top =>
    simp only [hc] at h2
    have : mid ⊓ top = mid := by decide
    rw [this] at h2
    exact absurd h2 (by decide)

/-- Summary: Three' is a K&S compatible non-Boolean lattice -/
theorem three_is_ks_compatible :
    (∃ _ : PlausibilitySpace Three', True) ∧
    (∃ _ : KSModel Three' NNReal, True) ∧
    ¬∃ (compl : Three' → Three'), (∀ a, a ⊔ compl a = ⊤) ∧ (∀ a, a ⊓ compl a = ⊥) :=
  ⟨⟨inferInstance, trivial⟩, ⟨standardThreeKSModel, trivial⟩, not_boolean⟩

end Three'

end Mettapedia.ProbabilityTheory.KnuthSkilling
