/-
# Knuth-Skilling Foundations: Basic Definitions

## K&S Symmetries (from "Foundations of Inference" 2012)
- Symmetry 0 (Fidelity): x̄ < ȳ ⟹ x < y
- Symmetry 1 (Monotonicity): x̄ < ȳ ⟹ x̄⊕z̄ < ȳ⊕z̄
- Symmetry 2 (Associativity): (x̄ ⊕ ȳ) ⊕ z̄ = x̄ ⊕ (ȳ ⊕ z̄)
- Symmetry 3 (Product Distributivity): formalized at the scalar level in
  `Mettapedia/ProbabilityTheory/KnuthSkilling/ProductTheorem/Basic.lean`
  (after Appendix A regrades `⊕` to `+` on `ℝ`).
- (Lattice-level bookkeeping for direct products lives in
  `Mettapedia/ProbabilityTheory/KnuthSkilling/ProductTheorem/DirectProduct.lean`.)
- Symmetry 4 (Product Associativity): used via an additive order-isomorphism
  representation `Θ(x ⊗ t) = Θ x + Θ t` (see `.../ProductTheorem/Main.lean`);
  the associativity-to-representation step is the Appendix A theorem applied to `⊗`.
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
import Mettapedia.ProbabilityTheory.Common.Valuation
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

/-! ## KnuthSkillingAlgebraBase: Core axioms without Archimedean -/

/-- Core K&S structure. Archimedean derivable from KSSeparation (SandwichSeparation.lean). -/
class KnuthSkillingAlgebraBase (α : Type*) extends LinearOrder α where
  op : α → α → α                                                    -- ⊕ combination
  ident : α                                                         -- ⊥ impossibility
  op_assoc : ∀ x y z : α, op (op x y) z = op x (op y z)             -- Sym 2: associativity
  op_ident_right : ∀ x : α, op x ident = x                          -- identity (unnumbered)
  op_ident_left : ∀ x : α, op ident x = x                           -- identity (unnumbered)
  op_strictMono_left : ∀ y : α, StrictMono (fun x => op x y)        -- Sym 0+1: fidelity+mono
  op_strictMono_right : ∀ x : α, StrictMono (fun y => op x y)       -- Sym 0+1: fidelity+mono
  ident_le : ∀ x : α, ident ≤ x                                     -- positivity

/-! ## KnuthSkillingAlgebra: Alias for Base

Archimedean is NOT an axiom—it's derivable from KSSeparation (see SandwichSeparation.lean).
We keep `KnuthSkillingAlgebra` as an alias for backward compatibility. -/

abbrev KnuthSkillingAlgebra := KnuthSkillingAlgebraBase

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
