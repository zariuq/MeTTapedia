import Mettapedia.TypeTheory.IndexedPolynomialInterpretation
import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of indexed method systems and composite interpretations

Objects share a base and a goal family. Arrows implement each method as a
target plan and preserve typed hole substitution. The instance is scoped:
this category of interpretations does not replace other notions of polynomial
morphism. Its composition and equations are the proved free-plan operations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.PlanCategory

universe u
variable (Base : Type u) (Index : Base → Type u)

noncomputable scoped instance category :
    CategoryTheory.Category (IndexedPolynomial.{u,u,u,u} Base Index) where
  Hom P Q := PlanInterpretation P Q
  id _ := PlanInterpretation.identity
  comp F G := F.comp G
  id_comp F := PlanInterpretation.identity_comp F
  comp_id F := PlanInterpretation.comp_identity F
  assoc F G J := PlanInterpretation.comp_assoc F G J

#print axioms category

end Mettapedia.TypeTheory.IndexedPolynomial.PlanCategory
