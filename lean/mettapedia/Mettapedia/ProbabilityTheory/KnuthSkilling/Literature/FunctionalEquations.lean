import Mathlib.Data.Real.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Functional equations background (Aczél / CDE method / worked examples)

This file collects *Lean-facing* definitions and small proved lemmas that sit behind the
functional-equation parts of:

- Aczél, “Lectures on Functional Equations and Their Applications” (excerpt pp. 319–324),
  local PDF: `literature/KS_codex/Aczel_excerpt_pp319-324.pdf`.
- Evans Chen, “Introduction to Functional Equations”,
  local PDF: `literature/KS_codex/FuncEq_Intro_EvanChen.pdf`.
- “CDE method for solving functional equations”,
  local PDF: `literature/KS_codex/CDE_Method_FuncEq.pdf`.

The *core reusable abstraction* for K&S-adjacent work is:

> If a binary operation is conjugate to addition by an order isomorphism `Θ`, then it is
> automatically associative and commutative (because `(+ )` is).

We record that implication as a fully proved lemma; deeper “existence of `Θ`” theorems
(e.g. Aczél-style representation theorems) are tracked as explicit `Prop` interfaces.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

open Classical

/-!
## Additive representation by an order isomorphism

This is the “generator” / “regraduation” form used throughout Cox/Aczél/K&S discussions:

`Θ (op x y) = Θ x + Θ y`.

We take `Θ : α ≃o ℝ` as the canonical target since most applications here ultimately compare to the
real line.
-/

/-- An operation `op` on a linearly ordered type `α` is *additively representable* if there is an
order isomorphism `Θ : α ≃o ℝ` making `op` correspond to addition under `Θ`.

We keep this as a data structure (in `Type`) so downstream code can extract the witness `Θ`.
-/
structure AdditiveOrderIsoRep (α : Type*) [LinearOrder α] (op : α → α → α) where
  Θ : α ≃o ℝ
  map_op : ∀ x y : α, Θ (op x y) = Θ x + Θ y

namespace AdditiveOrderIsoRep

variable {α : Type*} [LinearOrder α] {op : α → α → α}

theorem op_comm (h : AdditiveOrderIsoRep α op) : ∀ x y : α, op x y = op y x := by
  intro x y
  apply h.Θ.injective
  calc
    h.Θ (op x y) = h.Θ x + h.Θ y := h.map_op x y
    _ = h.Θ y + h.Θ x := by simp [add_comm]
    _ = h.Θ (op y x) := (h.map_op y x).symm

theorem op_assoc (h : AdditiveOrderIsoRep α op) : ∀ x y z : α, op (op x y) z = op x (op y z) := by
  intro x y z
  apply h.Θ.injective
  calc
    h.Θ (op (op x y) z) = h.Θ (op x y) + h.Θ z := h.map_op (op x y) z
    _ = (h.Θ x + h.Θ y) + h.Θ z := by simp [h.map_op]
    _ = h.Θ x + (h.Θ y + h.Θ z) := by simp [add_assoc]
    _ = h.Θ x + h.Θ (op y z) := by simp [h.map_op]
    _ = h.Θ (op x (op y z)) := (h.map_op x (op y z)).symm

theorem strictMono_left (h : AdditiveOrderIsoRep α op) (z : α) : StrictMono fun x => op x z := by
  intro x y hxy
  -- Apply `Θ` and use strict monotonicity of `(· + Θ z)` on `ℝ`.
  have : h.Θ (op x z) < h.Θ (op y z) := by
    simpa [h.map_op] using add_lt_add_right (h.Θ.strictMono hxy) (h.Θ z)
  exact (h.Θ.lt_iff_lt).1 this

theorem strictMono_right (h : AdditiveOrderIsoRep α op) (z : α) : StrictMono fun y => op z y := by
  intro x y hxy
  have : h.Θ (op z x) < h.Θ (op z y) := by
    simpa [h.map_op] using add_lt_add_left (h.Θ.strictMono hxy) (h.Θ z)
  exact (h.Θ.lt_iff_lt).1 this

end AdditiveOrderIsoRep

/-!
## Aczél-style theorem interface

Aczél proves existence of such a `Θ` for associative, strictly monotone (and usually continuous)
operations on real intervals.

We keep the theorem statement as a `Prop` interface so K&S-facing files can depend on the *shape*
of the result without introducing `sorry`.
-/

/-- A “minimal” hypothesis package for an Aczél-style associativity theorem on `ℝ`.

This is not claimed to be the exact weakest set; it is intended as a *search target* and a place to
record what the PDFs assume. -/
structure AczelHypothesis (op : ℝ → ℝ → ℝ) : Prop where
  assoc : ∀ x y z : ℝ, op (op x y) z = op x (op y z)
  strictMono_left : ∀ z : ℝ, StrictMono fun x => op x z
  strictMono_right : ∀ z : ℝ, StrictMono fun y => op z y
  continuous : Continuous (fun p : ℝ × ℝ => op p.1 p.2)

/-- “Aczél conclusion”: an additive order-isomorphism representation on `ℝ`. -/
def AczelConclusion (op : ℝ → ℝ → ℝ) : Prop :=
  Nonempty (AdditiveOrderIsoRep ℝ op)

/-- A placeholder interface for Aczél’s representation theorem in the form used by Cox/K&S:
associativity + order/monotonicity (+ continuity) implies additive representability. -/
def AczelTheoremSpec : Prop :=
  ∀ op : ℝ → ℝ → ℝ, AczelHypothesis op → AczelConclusion op

end Mettapedia.ProbabilityTheory.KnuthSkilling.Literature
