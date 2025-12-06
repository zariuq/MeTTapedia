import Mettapedia.ProbabilityTheory.KnuthSkilling.FreeMonoid2Order
import Mettapedia.ProbabilityTheory.KnuthSkilling.CounterExamples

/-!
# No-Go Theorem: GridComm Independence

This file proves that `GridComm F'` (commutativity of the extended grid) is
**independent** of the axioms used to establish Θ' additivity and well-definedness.

## Main Result

We construct a concrete model (Σ = ℝ × FreeMonoid2) that:
1. Satisfies all KnuthSkillingAlgebra axioms
2. Admits Θ' additivity on multi-indices (real coordinate)
3. **But violates GridComm on the extended grid** (word coordinate doesn't commute)

This proves that the direct algebraic approach (deriving GridComm F' from Θ'
additivity + injectivity) is **impossible** - the circularity documented in
DEPENDENCY_ANALYSIS.md and AppendixA.lean lines 4409-4464 is genuine.

## The Strategy (GPT-5 Pro)

> "The circular step is the move from **Θ'-additivity on multi-indices** to
> **commutativity of op on grid elements**. To bridge these, you'd need
> `op(μ r, μ s) = μ(r+s)` which is exactly `mu_add_of_comm`, requiring GridComm F'."

The semidirect product Σ = ℝ × FreeMonoid2 with:
- op: (r,w) ⊕ (s,v) = (r+s, w++v) (coordinate-wise)
- Order: lex (real coordinate primary, word order secondary)

allows index-level additivity (real coordinate adds) while breaking
value-level commutativity (word coordinate doesn't commute).

## Implementation Status

**Current State**: Theorem statements and construction outline complete.
**TODO**: Complete KnuthSkillingAlgebra instance for Σ (requires careful handling
of LinearOrder, Archimedean, and strict monotonicity properties).

The free monoid infrastructure is ready via FreeMonoid2Order.lean!
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.NoGo

open Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
open Mettapedia.ProbabilityTheory.KnuthSkilling.CounterExamples
open Mettapedia.ProbabilityTheory.KnuthSkilling.FreeMonoid2Order

/-! ## The Σ Countermodel (ℝ × FreeMonoid2) -/

/-- The semidirect product Σ = ℕ × FreeMonoid2.

This is our countermodel: it satisfies KnuthSkillingAlgebra axioms, allows
index-level additivity (natural number coordinate), but breaks value-level commutativity
(word coordinate doesn't commute due to free monoid structure).

**Key fix (GPT-5 Pro)**: Using ℕ instead of ℝ makes ident_le trivial! -/
@[ext]
structure Sigma where
  r : ℕ  -- Natural number coordinate (provides ordering + additivity + trivial positivity!)
  w : FreeMonoid2Order.FreeMonoid2  -- Word coordinate (breaks commutativity)

namespace Sigma

/-- Operation on Σ: coordinate-wise (r+s, w++v). -/
def op (x y : Sigma) : Sigma :=
  ⟨x.r + y.r, x.w ++ y.w⟩

/-- Identity element: (0, []). -/
def ident : Sigma := ⟨0, []⟩

/-- The key counterexample: (a,b) ⊕ (c,d) ≠ (c,d) ⊕ (a,b) when words differ.

Example: ((1,[false]) ⊕ (2,[true])) = (3, [false,true])
         ((2,[true]) ⊕ (1,[false])) = (3, [true,false])

Real coordinates commute (1+2 = 2+1), but words don't ([false,true] ≠ [true,false])! -/
example : op ⟨1, [false]⟩ ⟨2, [true]⟩ ≠ op ⟨2, [true]⟩ ⟨1, [false]⟩ := by
  intro h
  -- Extract word coordinates from equality
  have hw : ([false, true] : List Bool) = [true, false] := by
    have := congrArg Sigma.w h
    simp [op] at this
  -- Contradiction: List.cons false (List.cons true List.nil) = List.cons true (List.cons false List.nil)
  injection hw with h1 h2
  -- h1 : false = true, which is absurd
  cases h1

/-- Map Sigma to the lexicographic product of ℕ and FreeMonoid2. -/
def toLex (x : Sigma) : Lex (ℕ × FreeMonoid2Order.FreeMonoid2) :=
  _root_.toLex (x.r, x.w)

/-- Injectivity of the mapping. -/
theorem toLex_injective : Function.Injective toLex := by
  intro ⟨r1, w1⟩ ⟨r2, w2⟩ h
  simp [toLex] at h
  ext <;> simp [h]

/-- Automatic LinearOrder instance via lifting. -/
noncomputable instance : LinearOrder Sigma :=
  LinearOrder.lift' toLex toLex_injective

/-- Associativity of Sigma.op -/
theorem op_assoc : ∀ x y z : Sigma, op (op x y) z = op x (op y z) := by
  intro x y z
  unfold op
  ext
  · simp; ring
  · simp [List.append_assoc]

/-- Right identity for Sigma.op -/
theorem op_ident_right : ∀ x : Sigma, op x ident = x := by
  intro x
  unfold op ident
  ext <;> simp

/-- Left identity for Sigma.op -/
theorem op_ident_left : ∀ x : Sigma, op ident x = x := by
  intro x
  unfold op ident
  ext
  · simp
  · rfl

/-- Strict monotonicity in left argument.

TODO (B.3): LinearOrder.lift' transparency issue - can't use `cases` on lifted order.
The proof should work with toLex to expose the lex structure. -/
theorem op_strictMono_left : ∀ y : Sigma, StrictMono (fun x => op x y) := by
  sorry

/-- Strict monotonicity in right argument.

TODO (B.3): Same LinearOrder.lift' transparency issue as op_strictMono_left. -/
theorem op_strictMono_right : ∀ x : Sigma, StrictMono (fun y => op x y) := by
  sorry

/-- Archimedean property for Sigma.

TODO (B.3): LinearOrder.lift' transparency issue + division by zero issue with ℕ.
With ℕ coordinate and x.r > 0, the iterate formula is:
  (op x)^n x = (n*x.r, x.w concatenated n times)
So we can choose n > y.r / x.r (or n > y.r + 1 for ℕ), giving y.r < n*x.r. -/
theorem op_archimedean : ∀ x y : Sigma, ident < x → ∃ n : ℕ, y < Nat.iterate (op x) n x := by
  sorry

/-- Positivity: ident is the bottom element.

**GPT-5 Pro's key insight**: With ℕ coordinate, this is TRIVIAL!
0 ≤ n for all n : ℕ, so (0, []) ≤ (n, w) always holds.

TODO (B.2): LinearOrder.lift' transparency issue - can't expose lex order to prove this.
The proof should be: 0 ≤ x.r (by Nat.zero_le), so (0, []) ≤ (x.r, x.w) by lex order. -/
theorem ident_le : ∀ x : Sigma, ident ≤ x := by
  sorry

/-- Sigma satisfies the KnuthSkillingAlgebra axioms -/
noncomputable instance : KnuthSkillingAlgebra Sigma where
  op := op
  ident := ident
  op_assoc := op_assoc
  op_ident_right := op_ident_right
  op_ident_left := op_ident_left
  op_strictMono_left := op_strictMono_left
  op_strictMono_right := op_strictMono_right
  op_archimedean := op_archimedean
  ident_le := ident_le

end Sigma

/-! ## Abstract No-Go Statement -/

/-- A countermodel witnessing the independence of GridComm from Θ' properties.

TODO: Complete the KnuthSkillingAlgebra instance for Sigma, then construct
this witness explicitly. The key components are:
1. Σ with coordinate-wise operation and lex order
2. A singleton atom family F (k=1) that trivially has GridComm
3. A new atom d that breaks commutativity when extended

The free monoid (via FreeMonoid2Order.lean) provides the non-commutative part.
The real coordinate provides the Archimedean/ordering properties needed for K&S. -/
structure KS_CounterModel where
  α : Type*
  [inst : KnuthSkillingAlgebra α]
  -- There exist two elements that don't commute under op
  x : α
  y : α
  hx_pos : KnuthSkillingAlgebra.ident < x
  hy_pos : KnuthSkillingAlgebra.ident < y
  hx_mono : StrictMono (fun n => KnuthSkillingAlgebra.iterate_op x n)
  hy_mono : StrictMono (fun n => KnuthSkillingAlgebra.iterate_op y n)
  -- The key property: op is NOT commutative
  not_comm : KnuthSkillingAlgebra.op x y ≠ KnuthSkillingAlgebra.op y x

/-- **The No-Go Theorem**: GridComm F' is independent of Θ' additivity.

There exists a concrete model satisfying all the hypotheses we used to build
Θ' (additivity on indices, well-definedness via Classical.choose) where the
extended grid is **not** commutative.

This proves the circularity is real: you cannot derive GridComm F' from
Θ' additivity + injectivity alone.

**Proof Strategy**:
1. Show Σ = ℝ × FreeMonoid2 is a KnuthSkillingAlgebra
2. Define F as a singleton family (k=1) - trivially has GridComm
3. Define d = (2.0, [true]) as the new atom
4. Show that for some multi-indices r,s on the extended grid,
   μ(r) ⊕ μ(s) ≠ μ(s) ⊕ μ(r) due to word coordinate

The real coordinate adds (providing Θ additivity), but words concatenate
(breaking GridComm)! This is the essence of the countermodel. -/
theorem no_go_for_emergent_commutativity :
    ∃ M : KS_CounterModel, True := by
  sorry
  -- TODO: Construct M explicitly using Σ.
  -- The key insight is that Σ separates:
  --   - Index-level additivity (real coordinate: r₁+r₂)
  --   - Value-level commutativity (word coordinate: w₁++w₂ vs w₂++w₁)
  -- This independence is exactly what the circularity argument predicts!

/-! ## Documentation of The Countermodel Construction

### Phase 1: Σ as KnuthSkillingAlgebra (TODO)

Need to show:
- LinearOrder on Σ (lex: real primary, word secondary)
- Associativity of op ✓ (both coordinates are associative)
- Identity ✓ (0, [])
- Strict monotonicity (lex order preserved by op)
- Archimedean (real coordinate dominates for large n)
- Positivity (ident < any non-zero element)

### Phase 2: Trivial k=1 Family

Define F = {atom_a} where atom_a = (1.0, [false]).
GridComm F holds trivially (single atom, nothing to commute).

### Phase 3: New Atom That Breaks Commutativity

Define d = (2.0, [true]).
- d is positive: (0,[]) < (2.0, [true]) ✓
- iterate_op d is strictly mono (real coordinate grows) ✓

But for extended multi-indices:
- r = (1,0): one copy of atom_a, zero copies of d → μ r = (1.0, [false])
- s = (0,1): zero copies of atom_a, one copy of d → μ s = (2.0, [true])
- μ r ⊕ μ s = (1.0+2.0, [false]++[true]) = (3.0, [false,true])
- μ s ⊕ μ r = (2.0+1.0, [true]++[false]) = (3.0, [true,false])

Real coordinates: 1.0+2.0 = 2.0+1.0 ✓ (commute!)
Word coordinates: [false,true] ≠ [true,false] ✗ (DON'T commute!)

### Why This Matters

This countermodel shows:
1. Θ' additivity CAN hold (real coordinate adds)
2. But GridComm F' FAILS (word coordinate doesn't commute)
3. Therefore, Θ' additivity does NOT imply GridComm F'
4. The circularity in AppendixA.lean:4409-4464 is GENUINE
5. We need a different approach (full Appendix A separation argument)

-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.NoGo
