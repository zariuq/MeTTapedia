import Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.SemigroupRepresentations
import Mathlib.Order.Monotone.Defs

/-!
# Goertzel v3 “Group Fix” (formalized)

This file records a precise, *formal* version of the “add inverses” patch idea for the K&S
Appendix A representation step.

Mathlib already provides the relevant Hölder-style embedding for **Archimedean linearly ordered
abelian groups** via `Mathlib/Data/Real/Embedding.lean`:

* `Archimedean.exists_orderAddMonoidHom_real_injective`

This yields an injective ordered additive hom `Θ : G →+o ℝ`, hence a strictly monotone additive
representation.  In particular, once such a `Θ` exists, commutativity of the induced operation is
immediate (because `+` on `ℝ` is commutative and `Θ` is injective).

Important scope note:
* This file does **not** attempt to prove the non-abelian theorem “Archimedean bi-ordered group is
  abelian” (Hölder 1901).  Instead, it isolates the *exact* abelian-group statement already in
  mathlib, which is sufficient for a “group vertex” in the probability hypercube and for checking
  the downstream K&S pipeline under a stronger algebraic hypothesis.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open Classical

namespace GoertzelGroupFix

open Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

/-- Hölder embedding (mathlib): an Archimedean ordered additive commutative group embeds into `ℝ`. -/
theorem holderEmbeddingSpec_of_archimedean (G : Type*) [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [Archimedean G] :
    HolderEmbeddingSpec G :=
  Literature.holderEmbeddingSpec_of_archimedean (G := G)

/-- Extract a strictly monotone additive representation `Θ : G → ℝ` from the Hölder embedding. -/
theorem existsTheta_strictMono_additive (G : Type*) [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [Archimedean G] :
    ∃ Θ : G → ℝ, StrictMono Θ ∧ ∀ x y : G, Θ (x + y) = Θ x + Θ y := by
  rcases holderEmbeddingSpec_of_archimedean (G := G) with ⟨f, hf⟩
  refine ⟨f, ?_, ?_⟩
  · exact (f.monotone'.strictMono_of_injective hf)
  · intro x y
    simp

end GoertzelGroupFix

end Mettapedia.ProbabilityTheory.KnuthSkilling
