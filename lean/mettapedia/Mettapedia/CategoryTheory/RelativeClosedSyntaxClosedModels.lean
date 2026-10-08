import Mettapedia.CategoryTheory.RelativeClosedSyntaxSemanticModels

/-!
# Weak closed diagrams of an authored presentation

Objects are actual finite-limit and closed functors out of the generated
typed-arrow quotient. Morphisms are their ordinary natural transformations.
An independently realized assignment supplies such an object by the earned
forty-rule interpretation and its independently proved preservation laws.
Postcomposition uses the actual canonical closed comparison composition.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.ClosedModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory

universe k w z

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (signature : Signature (C := C) (symbols := symbols))
variable (D : Type w) [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

structure Diagram where
  functor : Object signature ⥤ D
  finiteLimits : PreservesFiniteLimits functor
  closed : MonoidalClosedFunctor functor

attribute [instance] Diagram.finiteLimits Diagram.closed

variable {signature D}

instance : Category (Diagram signature D) where
  Hom first second := first.functor ⟶ second.functor
  id mapping := 𝟙 mapping.functor
  comp before after := before ≫ after
  id_comp input := Category.id_comp (obj := Object signature ⥤ D) input
  comp_id input := Category.comp_id (obj := Object signature ⥤ D) input
  assoc before middle after := Category.assoc (obj := Object signature ⥤ D) before middle after

omit [HasFiniteLimits D] in
@[ext] theorem Diagram.ext {first second : Diagram signature D}
    (same : first.functor = second.functor) : first = second := by
  cases first
  cases second
  cases same
  rfl

def forget : Diagram signature D ⥤ (Object signature ⥤ D) where
  obj := Diagram.functor
  map input := input
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (forget (signature := signature) (D := D)).Full where
  map_surjective input := ⟨input, rfl⟩

instance : (forget (signature := signature) (D := D)).Faithful where
  map_injective input := input

def isoOfFunctor {first second : Diagram signature D}
    (compared : first.functor ≅ second.functor) : first ≅ second where
  hom := compared.hom
  inv := compared.inv
  hom_inv_id := compared.hom_inv_id
  inv_hom_id := compared.inv_hom_id

def interpretation : SemanticModels.Model signature D ⥤ Diagram signature D where
  obj model := ⟨model.diagram, inferInstance, inferInstance⟩
  map input := input
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (interpretation (signature := signature) (D := D)).Full where
  map_surjective input := ⟨input, rfl⟩

instance : (interpretation (signature := signature) (D := D)).Faithful where
  map_injective input := input

variable {E : Type z} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
variable (mapping : D ⥤ E) [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]

def postcompose : Diagram signature D ⥤ Diagram signature E where
  obj before :=
    ⟨before.functor ⋙ mapping, comp_preservesFiniteLimits before.functor mapping,
      CartesianClosedFunctorCoherence.closed_composition before.functor mapping⟩
  map input := Functor.whiskerRight input mapping
  map_id _ := Functor.whiskerRight_id' mapping
  map_comp before after := Functor.whiskerRight_comp before after mapping

omit [HasFiniteLimits D] [HasFiniteLimits E] in
@[simp] theorem postcompose_object (before : Diagram signature D) :
    ((postcompose mapping).obj before).functor = before.functor ⋙ mapping := rfl

omit [HasFiniteLimits D] [HasFiniteLimits E] in
@[simp] theorem postcompose_cell {before after : Diagram signature D} (input : before ⟶ after)
    (context : Object signature) :
    ((postcompose mapping).map input).app context = mapping.map (input.app context) := rfl

end Mettapedia.CategoryTheory.RelativeClosedSyntax.ClosedModels
