import Mettapedia.CategoryTheory.InternalCategoryFunctorCategory
import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportMaps

/-!
# Actual functorial action on internal categories

A functor preserving matching pullbacks acts on whole internal categories
and their complete internal functors. The pair and triple universal
properties earn the action on composition; the original functor laws
then earn its identity and composition laws on internal maps.
Recovering distinct internal maps requires faithfulness of the supplied
base functor; preservation of pullbacks alone supplies no such inverse.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportFunctor

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryFunctorCategory

universe u v w z

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {D : Type w} [Category.{z} D] [HasPullbacks D]
variable (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]

def action : InternalCategory C ⥤ InternalCategory D where
  obj original := InternalCategoryFiniteLimitTransport.category F original
  map := InternalCategoryFiniteLimitTransportMaps.map F
  map_id original := by
    apply map_ext
    · change F.map (𝟙 original.vertex) = 𝟙 (F.obj original.vertex)
      exact F.map_id original.vertex
    · change F.map (𝟙 original.edge) = 𝟙 (F.obj original.edge)
      exact F.map_id original.edge
  map_comp before after := by
    apply map_ext
    · change F.map (before.vertex ≫ after.vertex) = F.map before.vertex ≫ F.map after.vertex
      exact F.map_comp _ _
    · change F.map (before.edge ≫ after.edge) = F.map before.edge ≫ F.map after.edge
      exact F.map_comp _ _

theorem complete_vertex {first second : InternalCategory C} (mapping : first ⟶ second) :
    ((action F).map mapping).vertex = F.map mapping.vertex := rfl

theorem complete_edge {first second : InternalCategory C} (mapping : first ⟶ second) :
    ((action F).map mapping).edge = F.map mapping.edge := rfl

theorem faithful [F.Faithful] : (action F).Faithful where
  map_injective := by
    intro first second before after equal
    apply map_ext
    · apply F.map_injective
      exact congrArg (fun mapping : (action F).obj first ⟶ (action F).obj second => mapping.vertex) equal
    · apply F.map_injective
      exact congrArg (fun mapping : (action F).obj first ⟶ (action F).obj second => mapping.edge) equal

end Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportFunctor
