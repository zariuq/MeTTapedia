import Mettapedia.TypeTheory.PresheafNativeClosedSubstitution
import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

/-!
# Closed native substitution and its canonical comparisons

Actual native context substitution preserves its own chosen exponential
objects. The complete display-to-slice equivalence reflects product limits
and exponential comparison isomorphisms. Its natural substitution square
therefore earns closedness of native reindexing itself. Evaluation, unit
and composition retain the chosen product and exponential comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativeClosedAction

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits (PreservesLimitsOfSize preservesLimits_of_natIso
  preservesLimits_of_reflects_of_preserves)
open MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open Mettapedia.GSLT.Core.ContextualLadder
open PresheafNativeClosedSubstitution NativeLocalTheoryTransformation
open Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q R : Cᵒᵖ ⥤ Type u}

abbrev substitution (change : Q ⟶ P) :=
  TypeOver.reindexFunctor (C := (nativeLocalModel C).toCwf) change

/-- Product preservation follows from the complete native-to-slice
substitution square, rather than equality of carrier types. -/
instance substitution_preservesLimits (change : Q ⟶ P) :
    PreservesLimitsOfSize.{u,u} (substitution change) := by
  have : PreservesLimitsOfSize.{u,u} (substitution change ⋙ toSlice Q) :=
    preservesLimits_of_natIso (reindexingIso change).symm
  exact preservesLimits_of_reflects_of_preserves (substitution change) (toSlice Q)

/-- Logical slice pullback and the closed native decoder force
invertibility of the actual native exponential comparison. -/
noncomputable instance substitution_closed (change : Q ⟶ P) :
    MonoidalClosedFunctor (substitution change) := by
  have : MonoidalClosedFunctor (toSlice P ⋙ PresheafClosedComprehension.substitution change) :=
    closed_composition (toSlice P) (PresheafClosedComprehension.substitution change)
  have : MonoidalClosedFunctor (substitution change ⋙ toSlice Q) :=
    closed_of_naturalIso (reindexingIso change)
  exact closed_of_composition (substitution change) (toSlice Q)

/-- This is the canonical comparison in the actual native display
category; neither endpoint is replaced by its slice interpretation. -/
noncomputable def exponentialComparison (change : Q ⟶ P)
    (A B : TypeOver (nativeLocalModel C).toCwf P) :
    (substitution change).obj ((ihom A).obj B) ≅
      (ihom ((substitution change).obj A)).obj ((substitution change).obj B) :=
  asIso ((expComparison (substitution change) A).natTrans.app B)

/-- Every actual native evaluation follows the same supplied
substitution and complete function comparison. -/
theorem exponential_evaluation (change : Q ⟶ P)
    (A B : TypeOver (nativeLocalModel C).toCwf P) :
    (substitution change).obj A ◁ (exponentialComparison change A B).hom ≫
        (ihom.ev ((substitution change).obj A)).app ((substitution change).obj B) =
      inv (prodComparison (substitution change) A ((ihom A).obj B)) ≫
        (substitution change).map ((ihom.ev A).app B) :=
  expComparison_ev (substitution change) A B

set_option backward.isDefEq.respectTransparency false in
/-- The supplied complete body, including its evidence substitution,
is retained by native abstraction and subsequent context substitution. -/
theorem abstraction_substitution (change : Q ⟶ P)
    {A B X : TypeOver (nativeLocalModel C).toCwf P} (body : A ⊗ X ⟶ B) :
    (substitution change).map (curry body) ≫ (exponentialComparison change A B).hom =
      curry (inv (prodComparison (substitution change) A X) ≫
        (substitution change).map body) := by
  change (substitution change).map (curry body) ≫
      (expComparison (substitution change) A).natTrans.app B =
    curry (inv (prodComparison (substitution change) A X) ≫
      (substitution change).map body)
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, uncurry_expComparison]
  rw [← Category.assoc, ← prodComparison_inv_natural_whiskerLeft,
    Category.assoc, ← Functor.map_comp, whiskerLeft_curry_ihom_ev_app]

def unitComparison (P : Cᵒᵖ ⥤ Type u) :
    substitution (𝟙 P) ≅ 𝟭 (TypeOver (nativeLocalModel C).toCwf P) :=
  TypeOver.identityReindexIso (C := (nativeLocalModel C).toCwf) P

def compositionComparison (first : Q ⟶ P) (second : R ⟶ Q) :
    substitution (second ≫ first) ≅ substitution first ⋙ substitution second :=
  TypeOver.compositionReindexIso (C := (nativeLocalModel C).toCwf) first second

/-- Unit coherence compares the actual chosen native exponential
presentations through the native substitution unitor. -/
theorem exponential_unit (A B : TypeOver (nativeLocalModel C).toCwf P) :
    (exponentialComparison (𝟙 P) A B).hom ≫
        (pre ((unitComparison P).inv.app A)).app ((substitution (𝟙 P)).obj B) ≫
        (ihom A).map ((unitComparison P).hom.app B) =
      (unitComparison P).hom.app ((ihom A).obj B) := by
  exact (exponential_naturalIso (unitComparison P) A B).trans
    ((congrArg (fun arrow => (unitComparison P).hom.app ((ihom A).obj B) ≫ arrow)
      (exponential_identity A B)).trans (Category.comp_id _))

/-- Direct and staged substitution have the same complete function
comparison after the earned native compositor is retained. -/
theorem exponential_composition (first : Q ⟶ P) (second : R ⟶ Q)
    (A B : TypeOver (nativeLocalModel C).toCwf P) :
    (exponentialComparison (second ≫ first) A B).hom ≫
        (pre ((compositionComparison first second).inv.app A)).app
          ((substitution (second ≫ first)).obj B) ≫
        (ihom ((substitution first ⋙ substitution second).obj A)).map
          ((compositionComparison first second).hom.app B) =
      (compositionComparison first second).hom.app ((ihom A).obj B) ≫
        (substitution second).map (exponentialComparison first A B).hom ≫
        (exponentialComparison second ((substitution first).obj A)
          ((substitution first).obj B)).hom := by
  exact (exponential_naturalIso (compositionComparison first second) A B).trans
    (congrArg (fun arrow =>
      (compositionComparison first second).hom.app ((ihom A).obj B) ≫ arrow)
      (Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.exponential_composition
        (substitution first) (substitution second) A B))

end Mettapedia.TypeTheory.PresheafNativeClosedAction
