import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.SandwichSeparation

/-!
# K&S Neighbor Theory: Sequential (Noncommutative) Semantics

When commutativity (or the separation axiom that implies it) is dropped, the K&S “value scale”
need not behave like a commutative additive scale. In particular, it is misleading to describe
all weakenings as “imprecise probability” (intervals): the noncommutative neighbors are better
understood as **sequential / process** semantics, where “combination” composes effects and order
matters.

This file provides a minimal, fully-checked formalization of that idea.

We work over the core K&S base structure:
- `KnuthSkillingAlgebraBase` (associativity + identity + strict monotonicity)

and define a general notion of *process semantics* (monoid action-style), plus the canonical
instance given by right-multiplication.
-/

namespace Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.SequentialSemantics

open Classical
open Mettapedia.ProbabilityTheory.KnuthSkilling
open KnuthSkillingAlgebraBase

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-!
## §1: Process semantics for a K&S-style monoid

The key idea is to interpret a “value” as a transformation on some state space, and interpret
`x ⊕ y` as sequential composition (first `x`, then `y`).

This is the opposite of the commutative/additive picture (where values *are* real numbers and
composition is `+`).
-/

structure ProcessSemantics (α : Type*) [KnuthSkillingAlgebraBase α] where
  /-- State space on which plausibility values act. -/
  State : Type*
  /-- Apply a plausibility value as a state transformer. -/
  step : α → State → State
  /-- Identity acts as the identity transformation. -/
  step_ident : ∀ s, step ident s = s
  /-- Sequential composition: `x ⊕ y` acts as “do `x`, then do `y`”. -/
  step_op : ∀ x y s, step (op x y) s = step y (step x s)

namespace ProcessSemantics

/-- The canonical sequential semantics: interpret `x` by right-multiplication `s ↦ s ⊕ x`. -/
def canonical : ProcessSemantics α where
  State := α
  step := fun x s => op s x
  step_ident := by
    intro s
    simpa using (op_ident_right s)
  step_op := by
    intro x y s
    -- (s ⊕ (x ⊕ y)) = ((s ⊕ x) ⊕ y) by associativity.
    simp [op_assoc]

/-- The underlying step function of the canonical semantics, as a plain endomorphism of `α`. -/
def canonicalStep (x : α) : α → α :=
  fun s => op s x

@[simp] theorem canonicalStep_def (x s : α) : canonicalStep (α := α) x s = op s x := rfl

/-- `canonicalStep` composes according to `op`: `step (x ⊕ y) = step y ∘ step x`. -/
theorem canonicalStep_op (x y : α) :
    canonicalStep (α := α) (op x y) = fun s => canonicalStep (α := α) y (canonicalStep (α := α) x s) := by
  funext s
  simp [canonicalStep, op_assoc]

/-- If `op` is commutative, then the canonical step-functions commute. -/
theorem canonical_steps_commute (hcomm : ∀ x y : α, op x y = op y x) (x y : α) :
    (fun s => canonicalStep (α := α) x (canonicalStep (α := α) y s)) =
      fun s => canonicalStep (α := α) y (canonicalStep (α := α) x s) := by
  funext s
  -- Expand and rewrite `x ⊕ y = y ⊕ x`.
  change op (op s y) x = op (op s x) y
  -- Use associativity to reassociate, then commutativity to swap, then reassociate back.
  calc
    op (op s y) x = op s (op y x) := by simp [op_assoc]
    _ = op s (op x y) := by simp [hcomm x y]
    _ = op (op s x) y := by simp [op_assoc]

/-- If `op` is *not* commutative, then (witnessed at `ident`) the canonical step-functions do not
commute. -/
theorem canonical_steps_not_commute_of_noncomm (hnoncomm : ∃ x y : α, op x y ≠ op y x) :
    ∃ x y : α,
      (fun s => canonicalStep (α := α) x (canonicalStep (α := α) y s)) ≠
        fun s => canonicalStep (α := α) y (canonicalStep (α := α) x s) := by
  rcases hnoncomm with ⟨x, y, hxy⟩
  refine ⟨x, y, ?_⟩
  intro hEq
  -- Evaluate at `ident` and unfold `step`.
  have hAt :
      canonicalStep (α := α) x (canonicalStep (α := α) y ident) =
        canonicalStep (α := α) y (canonicalStep (α := α) x ident) := by
    have := congrArg (fun f => f ident) hEq
    simpa using this
  -- Reduce to `y ⊕ x = x ⊕ y`, contradicting `hxy`.
  -- `ident ⊕ z = z`.
  have : op y x = op x y := by
    simp [canonicalStep, op_ident_left] at hAt
    simpa using hAt
  exact hxy this.symm

end ProcessSemantics

end Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.SequentialSemantics
