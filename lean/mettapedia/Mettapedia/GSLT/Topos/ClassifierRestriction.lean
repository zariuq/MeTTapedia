import Mettapedia.GSLT.Topos.PresheafLogicalTransport
import Mettapedia.GSLT.Topos.SubobjectClassifier

/-!
# The classifier comparison for theory restriction

The canonical map from the restricted truth object to the source truth
object takes inverse images of sieves. It classifies the restricted
predicate, coherently with substitution, identities and composition.
Invertibility requires more than preservation of finite limits.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ClassifierRestriction

open _root_.CategoryTheory Opposite
open LogicalTransport

universe u
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]

def comparison (F : C ⥤ D) : F.op ⋙ omegaFunctor (C := D) ⟶ omegaFunctor (C := C) where
  app X := TypeCat.ofHom (Sieve.functorPullback F)
  naturality X Y arrow := by
    apply ConcreteCategory.hom_ext
    intro sieve
    change Sieve (F.obj X.unop) at sieve
    apply Sieve.ext
    intro Z f
    change sieve (F.map f ≫ F.map arrow.unop) ↔ sieve (F.map (f ≫ arrow.unop))
    rw [F.map_comp]

theorem truth (F : C ⥤ D) (X : Cᵒᵖ) :
    (comparison F).app X (⊤ : Sieve (F.obj X.unop)) = (⊤ : Sieve X.unop) := rfl

/-- Actual characteristic maps commute with the canonical comparison. -/
theorem characteristic (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) (predicate : Subfunctor P) :
    Functor.whiskerLeft F.op (chiOfSubfunctor P predicate) ≫ comparison F =
      chiOfSubfunctor (F.op ⋙ P) (restrictPredicate F predicate) := by
  ext X value
  apply Sieve.ext
  intro Z arrow
  rfl

theorem comparison_id : comparison (𝟭 C) = 𝟙 (omegaFunctor (C := C)) := by
  ext X sieve
  apply Sieve.ext
  intro Z arrow
  rfl

theorem comparison_comp (F : C ⥤ D) (G : D ⥤ E) :
    comparison (F ⋙ G) = Functor.whiskerLeft F.op (comparison G) ≫ comparison F := by
  ext X sieve
  apply Sieve.ext
  intro Z arrow
  rfl

/-- Fullness and essential surjectivity recover every target sieve;
faithfulness recovers every source sieve. -/
noncomputable def componentEquiv (F : C ⥤ D)
    [F.Full] [F.Faithful] [F.EssSurj] (X : C) :
    Sieve (F.obj X) ≃ Sieve X where
  toFun := Sieve.functorPullback F
  invFun := Sieve.functorPushforward F
  left_inv sieve := (Sieve.essSurjFullFunctorGaloisInsertion F X).l_u_eq sieve
  right_inv _ := Sieve.functorPullback_functorPushforward_eq F

/-- This isomorphism is the canonical classifier comparison, not an
unrelated chosen equivalence of truth-value carriers. -/
noncomputable def comparisonIso (F : C ⥤ D)
    [F.Full] [F.Faithful] [F.EssSurj] :
    F.op ⋙ omegaFunctor (C := D) ≅ omegaFunctor (C := C) :=
  NatIso.ofComponents (fun X => Equiv.toIso (componentEquiv F X.unop))
    (by intro X Y f; exact (comparison F).naturality f)

theorem comparisonIso_hom (F : C ⥤ D)
    [F.Full] [F.Faithful] [F.EssSurj] :
    (comparisonIso F).hom = comparison F := rfl

end Mettapedia.GSLT.Topos.ClassifierRestriction
