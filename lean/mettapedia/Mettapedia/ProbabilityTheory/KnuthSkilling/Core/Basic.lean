/-
# Knuth-Skilling Foundations: Basic Definitions

## K&S Symmetries (from "Foundations of Inference" 2012)
- Symmetry 0 (Fidelity): x̄ < ȳ ⟹ x < y
- Symmetry 1 (Monotonicity): x̄ < ȳ ⟹ x̄⊕z̄ < ȳ⊕z̄
- Symmetry 2 (Associativity): (x̄ ⊕ ȳ) ⊕ z̄ = x̄ ⊕ (ȳ ⊕ z̄)
- Symmetry 3 (Product Distributivity): formalized at the scalar level in
  `Mettapedia/ProbabilityTheory/KnuthSkilling/Multiplicative/Basic.lean`
  (after Appendix A regrades `⊕` to `+` on `ℝ`).
- (Lattice-level bookkeeping for direct products lives in
  `Mettapedia/ProbabilityTheory/KnuthSkilling/Multiplicative/DirectProduct.lean`.)
- Symmetry 4 (Product Associativity): used in Appendix B either via an additive order-isomorphism
  representation `Θ(x ⊗ t) = Θ x + Θ t` (see `.../Multiplicative/Main.lean`), or via the
  Lean-friendly direct route in `.../Multiplicative/Proofs/Direct/DirectProof.lean` that derives scaled
  multiplication from distributivity + associativity + regularity (without “Appendix A again”).
- Symmetry 5 (Chaining Associativity): PARTIAL

## Formalization Notes
- Symmetries 0+1 merge into `op_strictMono_{left,right}` (equivalent via identity)
- ⊕ is for DISJOINT events only (violating this breaks monotonicity)
- LinearOrder required (K&S line 1339: trichotomy assumed)
- Archimedean is DERIVABLE from KSSeparation (see SandwichSeparation.lean)
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Hammer
import Mettapedia.ProbabilityTheory.Structures.Valuation.Basic
import Mettapedia.ProbabilityTheory.Common.Lattice

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open MeasureTheory Classical

/-! ## PlausibilitySpace and Valuation -/

/-- A `PlausibilitySpace` is a distributive lattice with top and bottom. -/
class PlausibilitySpace (α : Type*) extends DistribLattice α, BoundedOrder α

instance instPlausibilitySpace (α : Type*)
    [DistribLattice α] [BoundedOrder α] : PlausibilitySpace α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with }

/-- A valuation assigns reals to events, monotone with val(⊥)=0, val(⊤)=1. -/
structure Valuation (α : Type*) [PlausibilitySpace α] where
  val : α → ℝ
  monotone : Monotone val
  val_bot : val ⊥ = 0
  val_top : val ⊤ = 1

namespace Valuation

variable {α : Type*} [PlausibilitySpace α] (v : Valuation α)

theorem nonneg (a : α) : 0 ≤ v.val a := by
  have h := v.monotone (bot_le : (⊥ : α) ≤ a); simpa [v.val_bot] using h

theorem le_one (a : α) : v.val a ≤ 1 := by
  have h := v.monotone (le_top : a ≤ (⊤ : α)); simpa [v.val_top] using h

theorem bounded (a : α) : 0 ≤ v.val a ∧ v.val a ≤ 1 := ⟨v.nonneg a, v.le_one a⟩

/-- Conditional valuation: v(a|b) = v(a ⊓ b) / v(b) when v(b) ≠ 0 -/
noncomputable def condVal (a b : α) : ℝ :=
  if _ : v.val b = 0 then 0 else v.val (a ⊓ b) / v.val b

end Valuation

scoped notation "𝕍[" v "](" a ")" => Valuation.val v a
scoped notation "𝕍[" v "](" a " | " b ")" => Valuation.condVal v a b

/-! ## Boolean cardinality lemmas (for XOR independence example) -/

@[simp] lemma card_A : Fintype.card {x : Bool × Bool | x.1 = true} = 2 := by decide
@[simp] lemma card_B : Fintype.card {x : Bool × Bool | x.2 = true} = 2 := by decide
@[simp] lemma card_C : Fintype.card {x : Bool × Bool | x.1 ≠ x.2} = 2 := by decide
@[simp] lemma card_A_inter_B :
    Fintype.card {x : Bool × Bool | x.1 = true ∧ x.2 = true} = 1 := by decide
@[simp] lemma card_A_inter_C :
    Fintype.card {x : Bool × Bool | x.1 = true ∧ x.1 ≠ x.2} = 1 := by decide
@[simp] lemma card_B_inter_C :
    Fintype.card {x : Bool × Bool | x.2 = true ∧ x.1 ≠ x.2} = 1 := by decide
@[simp] lemma card_A_inter_B_inter_C :
    Fintype.card {x : Bool × Bool | x.1 = true ∧ x.2 = true ∧ x.1 ≠ x.2} = 0 := by decide
@[simp] lemma card_eq : Fintype.card {x : Bool × Bool | x.1 = x.2} = 2 := by decide

lemma set_inter_setOf {α : Type*} (p q : α → Prop) :
    {x | p x} ∩ {x | q x} = {x | p x ∧ q x} := by ext; simp [Set.mem_inter_iff]

@[simp] lemma card_setOf_fst_true :
    Fintype.card {x : Bool × Bool | x.1 = true} = 2 := by decide
@[simp] lemma card_setOf_snd_true :
    Fintype.card {x : Bool × Bool | x.2 = true} = 2 := by decide
@[simp] lemma card_setOf_ne :
    Fintype.card {x : Bool × Bool | x.1 ≠ x.2} = 2 := by decide
@[simp] lemma card_setOf_not_eq :
    Fintype.card {x : Bool × Bool | ¬x.1 = x.2} = 2 := by decide
@[simp] lemma card_inter_fst_snd :
    Fintype.card ↑({x : Bool × Bool | x.1 = true} ∩ {x | x.2 = true} : Set (Bool × Bool)) = 1 := by decide
@[simp] lemma card_inter_fst_ne :
    Fintype.card ↑({x : Bool × Bool | x.1 = true} ∩ {x | x.1 ≠ x.2} : Set (Bool × Bool)) = 1 := by decide
@[simp] lemma card_inter_snd_ne :
    Fintype.card ↑({x : Bool × Bool | x.2 = true} ∩ {x | x.1 ≠ x.2} : Set (Bool × Bool)) = 1 := by decide
@[simp] lemma card_inter_fst_snd_ne :
    Fintype.card ↑(({x : Bool × Bool | x.1 = true} ∩ {x | x.2 = true}) ∩ {x | x.1 ≠ x.2} : Set (Bool × Bool)) = 0 := by decide

/-! ## ArchimedeanDensity -/

/-- For any ε > 0, exists n with 1/n < ε. Used for grid density arguments. -/
class ArchimedeanDensity where
  density : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ (1 : ℝ) / n < ε

instance : ArchimedeanDensity where
  density := fun ε hε => by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    use n + 1
    constructor
    · omega
    · have h_inv_pos : 0 < 1 / ε := by positivity
      have hn_pos : (0 : ℝ) < n := by linarith
      have hn1_pos : (0 : ℝ) < n + 1 := by linarith
      calc (1 : ℝ) / (n + 1 : ℕ) = 1 / ((n : ℝ) + 1) := by norm_cast
        _ < 1 / (n : ℝ) := by apply one_div_lt_one_div_of_lt hn_pos; linarith
        _ < 1 / (1 / ε) := by apply one_div_lt_one_div_of_lt (by positivity) hn
        _ = ε := by field_simp

/-! ## Unbundled Axiom Predicates

Following the "unbundled predicates + bundled convenience classes" pattern (à la mathlib),
we define each axiom as a standalone `def` predicate. This enables:
- Minimal hypothesis tracking in theorem statements
- Clear documentation of which axioms are used where
- Ergonomic bundled classes that reference these predicates -/

/-- Associativity of a binary operation. -/
def OpAssoc (op : α → α → α) : Prop :=
  ∀ x y z, op (op x y) z = op x (op y z)

/-- Strict left-monotonicity: `x₁ < x₂ → op x₁ y < op x₂ y`. -/
def OpStrictMonoLeft [Preorder α] (op : α → α → α) : Prop :=
  ∀ y, StrictMono (fun x => op x y)

/-- Strict right-monotonicity: `y₁ < y₂ → op x y₁ < op x y₂`. -/
def OpStrictMonoRight [Preorder α] (op : α → α → α) : Prop :=
  ∀ x, StrictMono (fun y => op x y)

/-- Left identity property: `op e x = x` for all `x`. -/
def OpIdentLeft (op : α → α → α) (e : α) : Prop :=
  ∀ x, op e x = x

/-- Right identity property: `op x e = x` for all `x`. -/
def OpIdentRight (op : α → α → α) (e : α) : Prop :=
  ∀ x, op x e = x

/-- Element is the order minimum: `e ≤ x` for all `x`. -/
def IdentIsMin [LE α] (e : α) : Prop :=
  ∀ x, e ≤ x

/-! ## KSSemigroupBase: Core semigroup structure (identity-free)

The Hölder/Alimov embedding theorem does NOT require identity.
This class captures the minimal structure needed for the representation theorem.
Identity is optional - it provides canonical normalization Θ(ident) = 0. -/

/-- Core K&S semigroup structure WITHOUT identity element.
    This is sufficient for the Hölder/Alimov embedding theorem.
    Identity is optional - it provides canonical normalization.

    Mathematical content:
    - Linearly ordered set with associative, strictly monotonic operation
    - No identity element required
    - Embeds into (ℝ, +) when no anomalous pairs exist -/
class KSSemigroupBase (α : Type*) extends LinearOrder α where
  /-- The combining operation ⊕ -/
  op : α → α → α
  /-- Symmetry 2: Associativity -/
  op_assoc : ∀ x y z : α, op (op x y) z = op x (op y z)
  /-- Symmetry 0+1: Left multiplication is strictly monotonic -/
  op_strictMono_left : ∀ y : α, StrictMono (fun x => op x y)
  /-- Symmetry 0+1: Right multiplication is strictly monotonic -/
  op_strictMono_right : ∀ x : α, StrictMono (fun y => op x y)

/-! ## Semigroup Monotonicity Lemmas

These lemmas derive non-strict monotonicity from strict monotonicity.
They work on `KSSemigroupBase` without requiring identity. -/

namespace KSSemigroupBase

variable {α : Type*} [KSSemigroupBase α]

/-! ### Connection to Unbundled Predicates -/

/-- The bundled associativity field satisfies the unbundled predicate. -/
theorem opAssoc : OpAssoc (op (α := α)) := op_assoc

/-- The bundled left strict monotonicity field satisfies the unbundled predicate. -/
theorem opStrictMonoLeft : OpStrictMonoLeft (op (α := α)) := fun y => op_strictMono_left y

/-- The bundled right strict monotonicity field satisfies the unbundled predicate. -/
theorem opStrictMonoRight : OpStrictMonoRight (op (α := α)) := fun x => op_strictMono_right x

/-! ### Derived Monotonicity Lemmas -/

/-- `op` is monotone in the left argument (derived from strict monotonicity). -/
theorem op_mono_left (y : α) {x₁ x₂ : α} (h : x₁ ≤ x₂) : op x₁ y ≤ op x₂ y := by
  rcases h.lt_or_eq with hlt | heq
  · exact le_of_lt (op_strictMono_left y hlt)
  · rw [heq]

/-- `op` is monotone in the right argument (derived from strict monotonicity). -/
theorem op_mono_right (x : α) {y₁ y₂ : α} (h : y₁ ≤ y₂) : op x y₁ ≤ op x y₂ := by
  rcases h.lt_or_eq with hlt | heq
  · exact le_of_lt (op_strictMono_right x hlt)
  · rw [heq]

end KSSemigroupBase

/-! ## KnuthSkillingMonoidBase / KnuthSkillingAlgebraBase

We keep `KSSemigroupBase` as the default, identity-free base.

When an identity element is needed, we distinguish:
- `KnuthSkillingMonoidBase`: identity + left/right identity laws (no `ident_le`)
- `KnuthSkillingAlgebraBase`: adds `ident_le : ∀ x, ident ≤ x` (probability-theory convenience)
-/

/-- Core K&S structure with an identity element (but **without** assuming the identity is
the minimum element). -/
class KnuthSkillingMonoidBase (α : Type*) extends KSSemigroupBase α where
  /-- Identity element (certain event in probability, additive zero in log-space) -/
  ident : α
  /-- Right identity: x ⊕ ident = x -/
  op_ident_right : ∀ x : α, op x ident = x
  /-- Left identity: ident ⊕ x = x -/
  op_ident_left : ∀ x : α, op ident x = x

/-- Core K&S structure used for probability theory: identity is also the minimum element. -/
class KnuthSkillingAlgebraBase (α : Type*) extends KnuthSkillingMonoidBase α where
  /-- Positivity: identity is the minimum element -/
  ident_le : ∀ x : α, ident ≤ x

-- Re-export semigroup fields so `open KnuthSkillingMonoidBase`/`open KnuthSkillingAlgebraBase`
-- brings them into scope. Also re-export toLinearOrder for backward compatibility.
namespace KnuthSkillingMonoidBase
export KSSemigroupBase (op op_assoc op_strictMono_left op_strictMono_right toLinearOrder)

variable {α : Type*} [KnuthSkillingMonoidBase α]

/-! ### Connection to Unbundled Predicates -/

/-- The bundled left identity field satisfies the unbundled predicate. -/
theorem opIdentLeft : OpIdentLeft (op (α := α)) ident := op_ident_left

/-- The bundled right identity field satisfies the unbundled predicate. -/
theorem opIdentRight : OpIdentRight (op (α := α)) ident := op_ident_right

end KnuthSkillingMonoidBase

namespace KnuthSkillingAlgebraBase
export KSSemigroupBase (op op_assoc op_strictMono_left op_strictMono_right toLinearOrder)
export KnuthSkillingMonoidBase (ident op_ident_left op_ident_right)

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-! ### Connection to Unbundled Predicates -/

/-- The bundled identity-is-minimum field satisfies the unbundled predicate. -/
theorem identIsMin : IdentIsMin (ident (α := α)) := ident_le

end KnuthSkillingAlgebraBase

/-! ## KnuthSkillingAlgebra: Alias for Base

Archimedean is NOT an axiom—it's derivable from KSSeparation (see SandwichSeparation.lean).
We keep `KnuthSkillingAlgebra` as an alias for backward compatibility. -/

abbrev KnuthSkillingAlgebra := KnuthSkillingAlgebraBase

/-! ## Identity-Free Positivity (Eric Luap's Approach)

Following Eric Luap's OrderedSemigroups library, we define positivity WITHOUT
reference to an identity element. This is mathematically equivalent to `ident < a`
when identity exists, but works in the identity-free `KSSemigroupBase` setting.

Reference: github.com/ericluap/OrderedSemigroups/blob/main/OrderedSemigroups/Sign.lean -/

variable {α : Type*}

/-- An element is positive if left-multiplying by it increases everything.
    This is equivalent to `ident < a` when identity exists (see `isPositive_iff_ident_lt`).

    Note: We use `x < op a x` (left multiplication increases) rather than
    Eric's `a * x > x` to match our `op` convention. -/
def IsPositive [KSSemigroupBase α] (a : α) : Prop :=
  ∀ x : α, x < KSSemigroupBase.op a x

/-- An element is negative if left-multiplying by it decreases everything. -/
def IsNegative [KSSemigroupBase α] (a : α) : Prop :=
  ∀ x : α, KSSemigroupBase.op a x < x

/-- An element acts as identity if left-multiplying by it preserves everything. -/
def IsOne [KSSemigroupBase α] (a : α) : Prop :=
  ∀ x : α, KSSemigroupBase.op a x = x

section PositivityWithIdentity
variable {α : Type*} [KnuthSkillingMonoidBase α]

open KSSemigroupBase KnuthSkillingMonoidBase

/-- Eric's positivity ↔ traditional positivity (with identity).
    When identity exists, `IsPositive a` is equivalent to `ident < a`. -/
theorem isPositive_iff_ident_lt (a : α) : IsPositive a ↔ ident < a := by
  constructor
  · intro h
    have := h ident
    rw [op_ident_right] at this
    exact this
  · intro h x
    calc x = op ident x := (op_ident_left x).symm
      _ < op a x := op_strictMono_left x h

/-- Eric's negativity ↔ traditional negativity (with identity). -/
theorem isNegative_iff_lt_ident (a : α) : IsNegative a ↔ a < ident := by
  constructor
  · intro h
    have := h ident
    rw [op_ident_right] at this
    exact this
  · intro h x
    calc op a x < op ident x := op_strictMono_left x h
      _ = x := op_ident_left x

/-- In K&S probability framework, all elements are positive (ident is minimum). -/
theorem isPositive_of_ne_ident {α : Type*} [KnuthSkillingAlgebraBase α]
    (a : α) (ha : a ≠ ident) : IsPositive a := by
  rw [isPositive_iff_ident_lt]
  exact lt_of_le_of_ne (KnuthSkillingAlgebraBase.ident_le a) (Ne.symm ha)

/-- The identity element is the unique `IsOne` element. -/
theorem isOne_iff_eq_ident (a : α) : IsOne a ↔ a = ident := by
  constructor
  · intro h
    have := h ident
    rw [op_ident_right] at this
    exact this
  · intro h x
    rw [h, op_ident_left]

end PositivityWithIdentity

/-! ## ℕ+ Iteration (Identity-Free)

Iteration using positive naturals ℕ+ (n ≥ 1) instead of ℕ.
This avoids the need for identity as a base case.

Reference: github.com/ericluap/OrderedSemigroups -/

/-- Helper: iterate operation n times starting from n=1.
    This is the ℕ-indexed version used internally. -/
private def iterate_op_pnat_aux [inst : KSSemigroupBase α] (x : α) : ℕ → α
  | 0 => x      -- n=0 maps to x^1 = x
  | n + 1 => inst.op x (iterate_op_pnat_aux x n)

/-- Iterate operation n times for n ∈ ℕ+ (n ≥ 1). No identity needed.
    - iterate_op_pnat x 1 = x
    - iterate_op_pnat x (n+1) = op x (iterate_op_pnat x n) -/
def iterate_op_pnat [KSSemigroupBase α] (x : α) (n : ℕ+) : α :=
  iterate_op_pnat_aux x (n.val - 1)

section IteratePNat
variable {α : Type*} [KSSemigroupBase α]

open KSSemigroupBase

theorem iterate_op_pnat_one (x : α) : iterate_op_pnat x 1 = x := rfl

/-- Key recursion: x^(n+1) = x ⊕ x^n -/
theorem iterate_op_pnat_succ (x : α) (n : ℕ+) :
    iterate_op_pnat x (n + 1) = op x (iterate_op_pnat x n) := by
  simp only [iterate_op_pnat, PNat.add_coe, PNat.val_ofNat, Nat.add_sub_cancel]
  -- Need to show: iterate_op_pnat_aux x n.val = op x (iterate_op_pnat_aux x (n.val - 1))
  -- Since n.val ≥ 1, we can write n.val = m + 1 for some m ≥ 0
  obtain ⟨m, hm⟩ : ∃ m, n.val = m + 1 := ⟨n.val - 1, (Nat.sub_add_cancel n.pos).symm⟩
  simp only [hm, Nat.add_sub_cancel, iterate_op_pnat_aux]

/-- Associativity for ℕ+ iteration: x^(m+n) = x^m ⊕ x^n -/
theorem iterate_op_pnat_add (x : α) (m n : ℕ+) :
    iterate_op_pnat x (m + n) = op (iterate_op_pnat x m) (iterate_op_pnat x n) := by
  induction m using PNat.recOn with
  | one =>
    -- Base: x^(1+n) = x ⊕ x^n
    -- Note: 1 + n = n + 1 for PNat, so this follows from iterate_op_pnat_succ
    rw [iterate_op_pnat_one]
    have h : (1 : ℕ+) + n = n + 1 := by
      apply Subtype.ext; show 1 + n.val = n.val + 1; omega
    rw [h, iterate_op_pnat_succ]
  | succ m ih =>
    -- Inductive: x^((m+1)+n) = x^(m+1) ⊕ x^n
    -- (m+1)+n = (m+n)+1, so LHS = x ⊕ x^(m+n) = x ⊕ (x^m ⊕ x^n) = (x ⊕ x^m) ⊕ x^n = x^(m+1) ⊕ x^n
    have h_add : m + 1 + n = m + n + 1 := by
      apply Subtype.ext; show (m + 1).val + n.val = (m + n).val + 1; simp [PNat.add_coe]; omega
    rw [h_add, iterate_op_pnat_succ, ih, ← op_assoc, ← iterate_op_pnat_succ]

/-- Strict monotonicity of ℕ+ iteration for positive elements.
    Key insight: IsPositive x says y < op x y, and iterate_op_pnat x (n+1) = op x (iterate_op_pnat x n),
    so iterate_op_pnat x n < iterate_op_pnat x (n+1). -/
theorem iterate_op_pnat_strictMono (x : α) (hx : IsPositive x) :
    StrictMono (iterate_op_pnat x) := by
  intro m n hmn
  -- Show iterate_op_pnat x m < iterate_op_pnat x n when m < n
  -- Since m < n, there exists k ≥ 1 such that n = m + k
  obtain ⟨k, hk_pos, hk⟩ : ∃ k : ℕ+, 0 < k.val ∧ n = m + k := by
    have hdiff : m.val < n.val := hmn
    use ⟨n.val - m.val, by omega⟩
    constructor
    · exact Nat.sub_pos_of_lt hdiff
    · apply Subtype.ext
      show n.val = m.val + (n.val - m.val)
      omega
  rw [hk]
  -- Now show iterate_op_pnat x m < iterate_op_pnat x (m + k)
  -- Use induction on k
  clear hmn hk_pos hk n
  induction k using PNat.recOn with
  | one =>
    -- Base: show iterate_op_pnat x m < iterate_op_pnat x (m + 1)
    rw [iterate_op_pnat_succ]
    exact hx (iterate_op_pnat x m)
  | succ k ih =>
    -- Inductive: assume iterate_op_pnat x m < iterate_op_pnat x (m + k)
    -- show iterate_op_pnat x m < iterate_op_pnat x (m + (k + 1))
    have h1 : m + (k + 1) = (m + k) + 1 := by
      apply Subtype.ext; show m.val + (k + 1).val = (m + k).val + 1; simp [PNat.add_coe]; omega
    rw [h1, iterate_op_pnat_succ]
    calc iterate_op_pnat x m
        < iterate_op_pnat x (m + k) := ih
      _ < op x (iterate_op_pnat x (m + k)) := hx _

/-- Non-strict monotonicity of ℕ+ iteration for positive elements.
    Derived from strict monotonicity. -/
theorem iterate_op_pnat_mono (x : α) (hx : IsPositive x) {m n : ℕ+} (h : m ≤ n) :
    iterate_op_pnat x m ≤ iterate_op_pnat x n := by
  rcases h.lt_or_eq with hlt | heq
  · exact le_of_lt (iterate_op_pnat_strictMono x hx hlt)
  · rw [heq]

/-- Strict monotonicity in the base for fixed ℕ+ exponent. -/
theorem iterate_op_pnat_strictMono_base {a b : α} (hab : a < b) (n : ℕ+) :
    iterate_op_pnat a n < iterate_op_pnat b n := by
  induction n using PNat.recOn with
  | one =>
    simp [iterate_op_pnat_one, hab]
  | succ n ih =>
    -- a^(n+1) = a ⊕ a^n, b^(n+1) = b ⊕ b^n
    rw [iterate_op_pnat_succ, iterate_op_pnat_succ]
    calc
      op a (iterate_op_pnat a n) < op a (iterate_op_pnat b n) := op_strictMono_right a ih
      _ < op b (iterate_op_pnat b n) := op_strictMono_left (iterate_op_pnat b n) hab

/-- Monotonicity in the base for fixed ℕ+ exponent. -/
theorem iterate_op_pnat_mono_base {a b : α} (hab : a ≤ b) (n : ℕ+) :
    iterate_op_pnat a n ≤ iterate_op_pnat b n := by
  rcases hab.lt_or_eq with hlt | heq
  · exact le_of_lt (iterate_op_pnat_strictMono_base hlt n)
  · rw [heq]

/-- Positivity is preserved under ℕ+ iteration. -/
theorem iterate_op_pnat_pos (x : α) (hx : IsPositive x) (n : ℕ+) :
    IsPositive (iterate_op_pnat x n) := by
  induction n using PNat.recOn with
  | one =>
    -- iterate_op_pnat x 1 = x
    simp only [iterate_op_pnat_one]
    exact hx
  | succ n ih =>
    -- iterate_op_pnat x (n + 1) = op x (iterate_op_pnat x n)
    intro y
    rw [iterate_op_pnat_succ]
    -- Need: y < op (op x (iterate_op_pnat x n)) y
    -- By associativity: = op x (op (iterate_op_pnat x n) y)
    -- Since ih : IsPositive (iterate_op_pnat x n), we have y < op (iterate_op_pnat x n) y
    -- Since hx : IsPositive x, we have op (iterate_op_pnat x n) y < op x (op (iterate_op_pnat x n) y)
    calc y < op (iterate_op_pnat x n) y := ih y
      _ < op x (op (iterate_op_pnat x n) y) := hx _
      _ = op (op x (iterate_op_pnat x n)) y := (op_assoc x _ y).symm

end IteratePNat

/-! Note: Connection between ℕ+ iteration and ℕ iteration (`iterate_op_pnat_eq_iterate_op`)
    is proven in `Algebra.lean` where `iterate_op` is defined. -/

/-! ## Connection to Common Infrastructure -/

section CommonFramework

open Mettapedia.ProbabilityTheory.Common

variable {α : Type*} [PlausibilitySpace α]

def Valuation.toNormalizedValuation (v : Valuation α) : NormalizedValuation α where
  val := v.val
  mono := fun _ _ h => v.monotone h
  val_bot := v.val_bot
  val_top := v.val_top

theorem Valuation.bounded_common (v : Valuation α) (a : α) :
    0 ≤ v.val a ∧ v.val a ≤ 1 := v.toNormalizedValuation.bounded a

theorem Valuation.nonneg_common (v : Valuation α) (a : α) :
    0 ≤ v.val a := v.toNormalizedValuation.nonneg a

theorem Valuation.le_one_common (v : Valuation α) (a : α) :
    v.val a ≤ 1 := v.toNormalizedValuation.le_one a

end CommonFramework

end Mettapedia.ProbabilityTheory.KnuthSkilling
