import Mettapedia.CategoryTheory.PredicateDoctrine

/-!
# Parametrized equality and simple quantifier base change

The contraction of a variable in a parameter context has an actual pullback
square under every change of parameters. Product projection squares are also
pullbacks. Their universal properties are proved from the chosen products;
the doctrine's Beck--Chevalley equations then give stable equality and both
simple quantifiers in those exact squares.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.PredicateDoctrine

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory

universe u v w
variable {B : Type u} [Category.{v} B] [CartesianMonoidalCategory B]

/-- Duplicate the variable while retaining the full parameter context. -/
def contraction (Γ A : B) : Γ ⊗ A ⟶ Γ ⊗ (A ⊗ A) :=
  lift (fst Γ A) (lift (snd Γ A) (snd Γ A))

theorem contraction_square {Γ Δ : B} (σ : Γ ⟶ Δ) (A : B) :
    (σ ⊗ₘ 𝟙 A) ≫ contraction Δ A = contraction Γ A ≫ (σ ⊗ₘ 𝟙 (A ⊗ A)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [contraction, Category.assoc]
  · apply CartesianMonoidalCategory.hom_ext <;> simp [contraction, Category.assoc]

/-- This is the full equality-contraction pullback, with no surjectivity or
object-coverage premise replacing the universal property. -/
theorem contraction_isPullback {Γ Δ : B} (σ : Γ ⟶ Δ) (A : B) :
    IsPullback (σ ⊗ₘ 𝟙 A) (contraction Γ A) (contraction Δ A)
      (σ ⊗ₘ 𝟙 (A ⊗ A)) where
  w := contraction_square σ A
  isLimit' := ⟨PullbackCone.IsLimit.mk (contraction_square σ A)
    (fun s => lift (s.snd ≫ fst Γ (A ⊗ A)) (s.fst ≫ snd Δ A))
    (fun s => by
      apply CartesianMonoidalCategory.hom_ext
      · have matched := congrArg (fun k => k ≫ fst Δ (A ⊗ A)) s.condition
        simpa [contraction, Category.assoc] using matched.symm
      · simp [Category.assoc])
    (fun s => by
      apply CartesianMonoidalCategory.hom_ext
      · simp [contraction]
      · apply CartesianMonoidalCategory.hom_ext
        · have matched := congrArg
            (fun k => k ≫ snd Δ (A ⊗ A) ≫ fst A A) s.condition
          simpa [contraction, Category.assoc] using matched
        · have matched := congrArg
            (fun k => k ≫ snd Δ (A ⊗ A) ≫ snd A A) s.condition
          simpa [contraction, Category.assoc] using matched)
    (fun s m first second => by
      apply CartesianMonoidalCategory.hom_ext
      · have matched := congrArg (fun k => k ≫ fst Γ (A ⊗ A)) second
        simpa [contraction, Category.assoc] using matched
      · have matched := congrArg (fun k => k ≫ snd Δ A) first
        simpa [Category.assoc] using matched)⟩

/-- Changing parameters preserves the actual product projection square. -/
theorem projection_isPullback {Γ Δ : B} (σ : Γ ⟶ Δ) (A : B) :
    IsPullback (σ ⊗ₘ 𝟙 A) (fst Γ A) (fst Δ A) σ where
  w := by simp
  isLimit' := ⟨PullbackCone.IsLimit.mk (by simp)
    (fun s => lift s.snd (s.fst ≫ snd Δ A))
    (fun s => by
      apply CartesianMonoidalCategory.hom_ext
      · simpa [Category.assoc] using s.condition.symm
      · simp)
    (fun s => by simp)
    (fun s m first second => by
      apply CartesianMonoidalCategory.hom_ext
      · simpa using second
      · have matched := congrArg (fun k => k ≫ snd Δ A) first
        simpa [Category.assoc] using matched)⟩

namespace FirstOrder

variable (D : FirstOrder.{u,v,w} B)

def equalityWithParameters (Γ A : B) : D.Fiber (Γ ⊗ (A ⊗ A)) :=
  D.existsAlong (contraction Γ A) ⊤

def contractionAdjunction (Γ A : B) :
    D.existsFunctor (contraction Γ A) ⊣
      D.toIndexedHeyting.reindexFunctor (contraction Γ A) :=
  D.existsAdjunction _

theorem contraction_frobenius (Γ A : B) (φ : D.Fiber (Γ ⊗ A))
    (ψ : D.Fiber (Γ ⊗ (A ⊗ A))) :
    D.existsAlong (contraction Γ A) (φ ⊓ D.reindex (contraction Γ A) ψ) =
      D.existsAlong (contraction Γ A) φ ⊓ ψ :=
  D.frobenius _ _ _

/-- Fibred equality is stable under arbitrary actual parameter maps. -/
theorem equality_parameter_substitution {Γ Δ : B} (σ : Γ ⟶ Δ) (A : B) :
    D.reindex (σ ⊗ₘ 𝟙 (A ⊗ A)) (D.equalityWithParameters Δ A) =
      D.equalityWithParameters Γ A := by
  change D.reindex (σ ⊗ₘ 𝟙 (A ⊗ A)) (D.existsAlong (contraction Δ A) ⊤) = _
  rw [D.exists_baseChange _ _ _ _ (contraction_isPullback σ A), D.reindex_top]
  rfl

theorem simple_exists_substitution {Γ Δ : B} (σ : Γ ⟶ Δ) (A : B)
    (φ : D.Fiber (Δ ⊗ A)) :
    D.reindex σ (D.existsAlong (fst Δ A) φ) =
      D.existsAlong (fst Γ A) (D.reindex (σ ⊗ₘ 𝟙 A) φ) :=
  D.exists_baseChange _ _ _ _ (projection_isPullback σ A) φ

theorem simple_forall_substitution {Γ Δ : B} (σ : Γ ⟶ Δ) (A : B)
    (φ : D.Fiber (Δ ⊗ A)) :
    D.reindex σ (D.forallAlong (fst Δ A) φ) =
      D.forallAlong (fst Γ A) (D.reindex (σ ⊗ₘ 𝟙 A) φ) :=
  D.forall_baseChange _ _ _ _ (projection_isPullback σ A) φ

end FirstOrder

end Mettapedia.CategoryTheory.PredicateDoctrine
