import Mettapedia.TypeTheory.ElementaryToposHigherOrderDependentSigma
import Mettapedia.CategoryTheory.InducedBicategoryPseudofunctor

/-!
# The global internal-language action

Every elementary topos is assigned its constructed higher-order dependent
language. Every geometric inverse-image map retains the complete predicate
and type endpoint maps and the comprehension comparison. Ordinary natural
transformations retain the full compatibility cube. Identity, composition
and horizontal substitution inherit the earned laws of the actual
image-comprehension action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ElementaryToposNativeLanguageAction

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open Mettapedia.CategoryTheory
open ElementaryToposImageComprehensionAction
open ElementaryToposHigherOrderDependentSigma

universe u v

attribute [local irreducible] ElementaryToposHigherOrderDependentSigma.profile

def map {source target : ElementaryTopos.{u,v}} (route : source ⟶ target) :
    language source ⟶ language target :=
  InducedBicategory.mkHom (globalAmbientAction.{u,v}.map route)

def map₂ {source target : ElementaryTopos.{u,v}} {first second : source ⟶ target}
    (change : first ⟶ second) : map first ⟶ map second :=
  InducedBicategory.mkHom₂ (globalAmbientAction.{u,v}.map₂ change)

theorem map_identity (topos : ElementaryTopos.{u,v}) :
    map (𝟙 topos) = 𝟙 (language topos) := by
  apply InducedBicategory.hom_ext
  exact globalAmbientAction.{u,v}.map_id topos

theorem map_composition {source middle target : ElementaryTopos.{u,v}}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    map (first ≫ second) = map first ≫ map second := by
  apply InducedBicategory.hom_ext
  exact globalAmbientAction.{u,v}.map_comp first second

def action : StrictPseudofunctor ElementaryTopos.{u,v}
    HigherOrderDependentSigma.TwoCategory.{max u v,v,max u v,max u v,v} :=
  InducedBicategoryPseudofunctor.restrict globalAmbientAction.{u,v}
    (fun object => Nonempty
      (HigherOrderDependentSigma.Profile.{max u v,v,max u v,max u v,v} object))
    (fun topos => ⟨profile topos⟩)

theorem map_strong {source target : ElementaryTopos.{u,v}} (route : source ⟶ target) :
    HigherOrderDependentSigma.Strong (action.map route) :=
  globalAmbientAction_strong route

@[simp] theorem action_predicate_map {source target : ElementaryTopos.{u,v}}
    (route : source ⟶ target) :
    (action.map route).hom.hom.left =
      FibrationTwoCategory.predicateMap (ElementaryToposObjectUniverseLift.map route).functor :=
  rfl

@[simp] theorem action_type_map {source target : ElementaryTopos.{u,v}}
    (route : source ⟶ target) :
    (action.map route).hom.hom.right =
      FibrationTwoCategory.codomainMap (ElementaryToposObjectUniverseLift.map route).functor := rfl

@[simp] theorem action_predicate_cell {source target : ElementaryTopos.{u,v}}
    {first second : source ⟶ target} (change : first ⟶ second) :
    (action.map₂ change).hom.hom.left =
      FibrationTwoCategory.predicateCell (ElementaryToposObjectUniverseLift.map₂ change) := rfl

@[simp] theorem action_type_cell {source target : ElementaryTopos.{u,v}}
    {first second : source ⟶ target} (change : first ⟶ second) :
    (action.map₂ change).hom.hom.right =
      FibrationTwoCategory.codomainCell (ElementaryToposObjectUniverseLift.map₂ change) := rfl

end Mettapedia.TypeTheory.ElementaryToposNativeLanguageAction
