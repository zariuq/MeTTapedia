import Mettapedia.CategoryTheory.PredicateDoctrine
import Mathlib.CategoryTheory.Monoidal.Cartesian.InfSemilattice
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Adjunction.Limits

/-!+# Closed predicate fibres and their actual substitution comparisons

Heyting implication is the chosen exponential of the order category: its
adjunction is built from the implication residuation law. The doctrine's
substitution functors preserve limits and colimits by their independently
constructed quantifier adjunctions. Their actual canonical exponential
comparisons are invertible by the earned implication substitution equation.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.PredicateDoctrine

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open scoped _root_.CategoryTheory.SemilatticeInf

universe u v w z

namespace HeytingClosed

variable (H : Type w) [HeytingAlgebra H]

/-- The implication action is the actual exponential right adjoint. -/
def implicationFunctor (φ : H) : H ⥤ H :=
  (show Monotone (fun ψ : H => φ ⇨ ψ) from
    fun _ _ below => himp_le_himp_left below).functor

private def implicationHomEquiv (φ ψ χ : H) :
    (φ ⊓ ψ ⟶ χ) ≃ (ψ ⟶ φ ⇨ χ) where
  toFun arrow := homOfLE (le_himp_iff'.mpr arrow.le)
  invFun arrow := homOfLE (le_himp_iff'.mp arrow.le)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The tensor--exponential adjunction retains both residuation directions. -/
noncomputable def implicationAdjunction (φ : H) : tensorLeft φ ⊣ implicationFunctor H φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := implicationHomEquiv H φ
      homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
      homEquiv_naturality_right := by intros; apply Subsingleton.elim }

/-- Chosen Cartesian closure of a Heyting algebra viewed as an order category. -/
noncomputable scoped instance monoidalClosed : MonoidalClosed H where
  closed φ :=
    { rightAdj := implicationFunctor H φ
      adj := implicationAdjunction H φ }

open scoped HeytingClosed

theorem exponential_object (φ ψ : H) : (ihom φ).obj ψ = φ ⇨ ψ := rfl

/-- The complete categorical evaluator is exactly the Heyting evaluation
inequality, rather than an unrelated chosen right adjoint. -/
theorem evaluation_readout (φ ψ : H) :
    (ihom.ev φ).app ψ = homOfLE (inf_himp_le : φ ⊓ (φ ⇨ ψ) ≤ ψ) :=
  Subsingleton.elim _ _

end HeytingClosed

open scoped HeytingClosed

variable {B : Type u} [Category.{v} B]

namespace FirstOrder

variable (D : FirstOrder.{u,v,w} B)

/-- Substitution preserves every existing fibre limit because it is a
right adjoint, independently of the chosen product presentation. -/
theorem reindex_preservesLimits {X Y : B} (f : X ⟶ Y) :
    PreservesLimitsOfSize.{z,z} (D.toIndexedHeyting.reindexFunctor f) :=
  (D.existsAdjunction f).rightAdjoint_preservesLimits

/-- The other quantifier adjunction also gives preservation of every existing
fibre colimit, in particular the initial predicate and binary joins. -/
theorem reindex_preservesColimits {X Y : B} (f : X ⟶ Y) :
    PreservesColimitsOfSize.{z,z} (D.toIndexedHeyting.reindexFunctor f) :=
  (D.forallAdjunction f).leftAdjoint_preservesColimits

noncomputable instance reindex_preservesFiniteProducts {X Y : B} (f : X ⟶ Y) :
    PreservesFiniteProducts (D.toIndexedHeyting.reindexFunctor f) := by
  have : PreservesLimitsOfSize.{0,0} (D.toIndexedHeyting.reindexFunctor f) :=
    D.reindex_preservesLimits f
  infer_instance

/-- The component of the actual exponential comparison is the equality
comparison supplied by implication substitution. Its inverse is earned from
that equality, not postulated as part of the doctrine. -/
theorem exponentialComparison_eq {X Y : B} (f : X ⟶ Y) (φ ψ : D.Fiber Y) :
    (expComparison (D.toIndexedHeyting.reindexFunctor f) φ).natTrans.app ψ =
      eqToHom (D.reindex_himp f φ ψ) :=
  Subsingleton.elim _ _

noncomputable instance reindex_monoidalClosed {X Y : B} (f : X ⟶ Y) :
    MonoidalClosedFunctor (D.toIndexedHeyting.reindexFunctor f) where
  comparison_iso φ := by
    suffices ∀ ψ : D.Fiber Y,
        IsIso ((expComparison (D.toIndexedHeyting.reindexFunctor f) φ).natTrans.app ψ) from
      NatIso.isIso_of_isIso_app _
    intro ψ
    refine ⟨⟨eqToHom (D.reindex_himp f φ ψ).symm, ?_, ?_⟩⟩ <;>
      apply Subsingleton.elim

/-- The inverse of the canonical comparison recovers the independently
computed exponential before substitution. -/
theorem exponentialComparison_inv {X Y : B} (f : X ⟶ Y) (φ ψ : D.Fiber Y) :
    inv ((expComparison (D.toIndexedHeyting.reindexFunctor f) φ).natTrans.app ψ) =
      eqToHom (D.reindex_himp f φ ψ).symm :=
  Subsingleton.elim _ _

end FirstOrder

end Mettapedia.CategoryTheory.PredicateDoctrine
