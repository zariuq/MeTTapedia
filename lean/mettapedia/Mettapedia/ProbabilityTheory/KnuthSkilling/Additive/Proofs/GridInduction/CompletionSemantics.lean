import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.CredalSets

/-!
# Completion Semantics API (Credal / Interval Semantics)

This file is a small **stable API layer** for the “weak neighbor” interpretation of K&S-like
axioms:

*If the axioms do not determine a unique real-valued representation `Θ`, interpret each term by
the set of values it can take across all completions (models).*

For real-valued completions, this induces an **interval semantics** by taking `sInf`/`sSup` across
the completion family.

This API is intended for reuse in the paper writeup and in the hypercube neighbor analysis.

See also:
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Additive/Proofs/GridInduction/CredalSets.lean`
  (definitions and core lemmas).
- `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/Neighbors.lean`
  (how this relates to nearby vertices).
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.CompletionSemantics

open Classical
open Set
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.CredalSets

variable {α : Type*}

/-!
## §1: Interval semantics from a family of completions
-/

/-- From any nonempty family of additive real-valued completions `Θ`, build an interval semantics
for `op` satisfying Minkowski containment. -/
noncomputable def intervalSemantics (op : α → α → α)
    (ι : Type*) [Nonempty ι]
    (Θ : ι → α → ℝ)
    (hAssoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hAdd : ∀ i x y, Θ i (op x y) = Θ i x + Θ i y)
    (hBddBelow : ∀ x, BddBelow (range fun i => Θ i x))
    (hBddAbove : ∀ x, BddAbove (range fun i => Θ i x)) :
    IntervalAddSemantics α :=
  IntervalAddSemantics.ofThetaFamily op ι Θ hAssoc hAdd hBddBelow hBddAbove

/-!
## §2: Unique completion ⇒ point semantics

If the completion family is a singleton (formally, `Subsingleton ι`), the induced interval is a
point interval `[c,c]`, i.e. the semantics is *precise*.
-/

/-- In the singleton-completion case, the interval semantics is point-valued at each `x`. -/
theorem intervalSemantics_precise_of_subsingleton (op : α → α → α)
    {ι : Type*} [Subsingleton ι] [Nonempty ι]
    (Θ : ι → α → ℝ)
    (hAssoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hAdd : ∀ i x y, Θ i (op x y) = Θ i x + Θ i y)
    (hBddBelow : ∀ x, BddBelow (range fun i => Θ i x))
    (hBddAbove : ∀ x, BddAbove (range fun i => Θ i x))
    (x : α) :
    ((intervalSemantics op ι Θ hAssoc hAdd hBddBelow hBddAbove).μ x).lower =
      ((intervalSemantics op ι Θ hAssoc hAdd hBddBelow hBddAbove).μ x).upper := by
  -- Reduce to the corresponding lemma about `intervalOf`.
  simpa [intervalSemantics, IntervalAddSemantics.ofThetaFamily] using
    (intervalOf_unique (α := α) (ι := ι) (Θ := Θ) (hBddBelow := hBddBelow) (hBddAbove := hBddAbove) x)

/-- In the singleton-completion case, the induced interval is exactly `[Θ i₀ x, Θ i₀ x]`. -/
theorem intervalSemantics_mu_eq_const_of_subsingleton (op : α → α → α)
    {ι : Type*} [Subsingleton ι] [Nonempty ι]
    (Θ : ι → α → ℝ)
    (hAssoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hAdd : ∀ i x y, Θ i (op x y) = Θ i x + Θ i y)
    (hBddBelow : ∀ x, BddBelow (range fun i => Θ i x))
    (hBddAbove : ∀ x, BddAbove (range fun i => Θ i x))
    (i0 : ι) (x : α) :
    (intervalSemantics op ι Θ hAssoc hAdd hBddBelow hBddAbove).μ x =
      constInterval (Θ i0 x) := by
  classical
  have hEq : Set.range (fun i => Θ i x) = {Θ i0 x} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      have : i = i0 := Subsingleton.elim i i0
      simp [this]
    · intro hr
      rcases hr with rfl
      exact ⟨i0, rfl⟩
  -- Unfold the interval semantics and compute `sInf`/`sSup` for the singleton range.
  simp [intervalSemantics, IntervalAddSemantics.ofThetaFamily, IntervalAddSemantics.intervalOf, hEq, constInterval]

/-- A canonical point-valued semantics packaged as `IntervalAddSemantics`:
interpret each term by the point interval `[Θ x, Θ x]`. -/
def pointSemantics (op : α → α → α) (Θ : α → ℝ)
    (hAssoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hAdd : ∀ x y, Θ (op x y) = Θ x + Θ y) : IntervalAddSemantics α where
  op := op
  μ := fun x => constInterval (Θ x)
  assoc := hAssoc
  containment := by
    intro x y
    -- Rewrite `+` on intervals to the definitional `Interval.add`, then compute.
    change
      (constInterval (Θ (op x y))).containedIn
        (Interval.add (constInterval (Θ x)) (constInterval (Θ y)))
    simp [Interval.containedIn, Interval.add, constInterval, hAdd]

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.CompletionSemantics
