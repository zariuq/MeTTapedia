import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA

open Classical KnuthSkillingAlgebra

/-!
## Main Theorem

This file is the public location of the main representation theorem and its corollaries.

The original monolithic proof development is preserved (commented-out) in
`Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/ProofDraft.lean`.

Goal: keep the library building green while we incrementally port/fix that proof.
-/

/-!
### Main Representation Theorem

**Status**: Blocked by one explicit missing hypothesis (see
`Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Core/Induction/ThetaPrime.lean`):
- `ChooseδBaseAdmissible`: the chosen `δ := chooseδ hk R d hd` is strictly base-admissible for
  every base `r0` and level `u > 0` (K&S Appendix A.3.4 “fixdelta → fixm” / base-invariance step).
  - In the globally `B = ∅` regime, this implies the earlier strict-gap interface
    `BEmptyStrictGapSpec`, and conversely can be recovered from it (see
    `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Core/Induction/Goertzel.lean`).
  - The previous proof attempt used `ZQuantized_chooseδ_if_B_nonempty`, but this implication is
    **not** derivable in general and can fail even in the additive model
    (see `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Counterexamples/ZQuantizedBNonempty.lean`).
    The extension theorem no longer depends on `ZQuantized…`.
  - `Goertzel.lean` further isolates a smaller explicit hypothesis package sufficient for proving
    `ChooseδBaseAdmissible` in the B-empty branch (`AppendixA34Extra`), including:
    - `AppendixA34Extra.newAtomCommutes` (`NewAtomCommutes F d`): the new atom commutes with the old μ-grid
      (needed for the `(μ ⊕ d^u)^m` decomposition in the base-indexed A-side scaling argument).
    - `AppendixA34Extra.C_strict0`: strict C-side inaccessibility at base `0`, implied by the strict-separation
      strengthening `KSSeparationStrict` (or by `KSSeparation` if `α` is densely ordered).

**Proof Strategy** (GPT-5 Pro's "Triple Family Trick"):
1. For any x ≠ ident, choose reference atom `a` with `ident < a`
2. Build 2-atom family F₂ = {a, x} with MultiGridRep R₂
3. Define Θ(x) := R₂.Θ_grid ⟨x, mem_proof⟩

**Well-definedness**: The choice of reference atom `a` doesn't affect Θ(x).
- Given two choices a₁, a₂, build 3-atom family F₃ = {a₁, a₂, x}
- `extend_grid_rep_with_atom` gives consistent extension
- `Theta'_well_defined` shows Θ(x) is uniquely determined

**Order preservation**: For a ≤ b, build 3-atom family {ref, a, b}
- If a < b: R.strictMono gives Θ(a) < Θ(b)
- If a = b: Trivial

**Additivity**: For Θ(x ⊕ y) = Θ(x) + Θ(y), build 3-atom family {ref, x, y}
- R.add gives Θ(μ(r + s)) = Θ(μ(r)) + Θ(μ(s)) on grid
- Need: x ⊕ y is representable on the grid

**Blocking Issue**: The extension step `extend_grid_rep_with_atom` is currently proved assuming
`ChooseδBaseAdmissible`. Discharging that interface (or refactoring to avoid it) is the remaining
work needed to derive `associativity_representation` from just `[KnuthSkillingAlgebra α] [KSSeparation α]`.
-/
/-!
### Main Representation Theorem (K&S Appendix A)

**Status**: Blocked (explicit hypothesis).

The `Core/` development builds cleanly and the proof is modularized, but the top-level
“triple family” globalization step (defining `Θ : α → ℝ` independent of auxiliary atom choices)
has not yet been fully ported here.

Once the remaining `Core/` pieces are consolidated into a usable global construction, replace
the explicit hypothesis below by an instance/proof built from `Core/`.
-/

/-!
### Explicit Blocker

`Core/` proves the inductive extension step on finite atom families *assuming* the missing
K&S Appendix A.3.4 strict-gap argument (see `.../Core/Induction/ThetaPrime.lean`).

What remains here is the globalization (“triple family trick”): define a single `Θ : α → ℝ`
independent of the auxiliary atom family choices, and prove it is an order embedding and additive.

To keep `AppendixA` placeholder-free while making the dependency explicit, we package this final step
as a `Prop`-class. -/

/-- The remaining globalization step of K&S Appendix A, packaged as an explicit assumption. -/
class AppendixAGlobalization (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] : Prop where
  /-- Existence of an order embedding `Θ : α → ℝ` turning `op` into `+`. -/
  exists_Theta :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y

/-- **K&S Appendix A main theorem**: existence of an order embedding `Θ : α → ℝ` turning `op` into `+`.

This is the public API theorem; it is currently postulated while the globalization proof is being
ported from the historical draft into the refactored `Core/` development. -/
theorem associativity_representation
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [AppendixAGlobalization α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  exact AppendixAGlobalization.exists_Theta (α := α)

theorem op_comm_of_associativity
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [AppendixAGlobalization α] :
    ∀ x y : α, op x y = op y x := by
  classical
  obtain ⟨Θ, hΘ_order, _, hΘ_add⟩ := associativity_representation (α := α)
  exact commutativity_from_representation Θ hΘ_order hΘ_add

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
