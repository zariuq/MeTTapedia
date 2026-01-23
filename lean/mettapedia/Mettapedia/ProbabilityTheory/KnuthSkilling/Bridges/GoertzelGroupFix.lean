import Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.SemigroupRepresentations
import Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.HolderNonAbelian
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Monoid.Defs
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

This file now includes a non-abelian variant too:
* Clay–Rolfsen (arXiv:1511.05088, Lemma 2.4): an Archimedean bi-ordered group is abelian.
  We formalize this as `HolderNonAbelian.add_comm_of_biOrdered_archimedean`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open Classical

namespace GoertzelGroupFix

open Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

/-- Clay–Rolfsen (arXiv:1511.05088, Lemma 2.4), additive form:
an Archimedean bi-ordered group is commutative. -/
theorem add_comm_of_biOrdered_archimedeanNC (G : Type*) [AddGroup G] [LinearOrder G]
    [IsBiOrderedAddGroup G] [ArchimedeanNC G] :
    ∀ x y : G, x + y = y + x :=
  HolderNonAbelian.add_comm_of_biOrdered_archimedean (G := G)

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

/-- Goertzel’s “group fix”, non-abelian version:

Assuming bi-orderability and the (noncommutative) Archimedean axiom `ArchimedeanNC`, we first
*derive* commutativity (Clay–Rolfsen Lemma 2.4), then apply mathlib’s Hölder embedding. -/
theorem existsTheta_strictMono_additive_of_biOrdered_archimedeanNC (G : Type*)
    [AddGroup G] [LinearOrder G] [IsBiOrderedAddGroup G] [ArchimedeanNC G] :
    ∃ Θ : G → ℝ, StrictMono Θ ∧ ∀ x y : G, Θ (x + y) = Θ x + Θ y := by
  classical
  have hadd : ∀ x y : G, x + y = y + x := add_comm_of_biOrdered_archimedeanNC (G := G)
  letI : AddCommGroup G := { toAddGroup := (inferInstance : AddGroup G), add_comm := hadd }
  letI : IsOrderedAddMonoid G :=
    { add_le_add_left := fun a b hab c => HolderNonAbelian.add_le_add_left (G := G) hab c
      add_le_add_right := fun a b hab c => HolderNonAbelian.add_le_add_right (G := G) hab c }
  letI : Archimedean G :=
    { arch := fun x {y} hy => ArchimedeanNC.arch (G := G) x hy }
  exact existsTheta_strictMono_additive (G := G)

end GoertzelGroupFix

end Mettapedia.ProbabilityTheory.KnuthSkilling
