import Mettapedia.CategoryTheory.RelativeClosedSyntaxAssignmentTransport

/-!
# Categories of independently realized relative presentations

Each object consists of primitive meanings and their local declared-header
and equation realization. Its interpretation is obtained from the earned
forty-rule soundness theorem and the actual typed-arrow quotient.

Morphisms are ordinary natural transformations of these interpreted
diagrams. This category does not assert that arbitrary primitive maps extend
to such transformations, or that the generated presentation is a free modal
extension. The interpretation functor retains the whole supplied diagram.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.SemanticModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (signature : Signature (C := C) (symbols := symbols))
variable (D : Type w) [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

structure Model where
  meanings : Interpretation.Assignment C symbols D
  realization : Interpretation.Realization signature meanings

variable {signature D}

abbrev Model.diagram (model : Model signature D) : GeneratedCategory.Object signature ⥤ D :=
  Interpretation.functor model.meanings model.realization

instance : Category (Model signature D) where
  Hom first second := first.diagram ⟶ second.diagram
  id model := 𝟙 model.diagram
  comp before after := before ≫ after
  id_comp arrow := Category.id_comp (obj := GeneratedCategory.Object signature ⥤ D) arrow
  comp_id arrow := Category.comp_id (obj := GeneratedCategory.Object signature ⥤ D) arrow
  assoc before middle after := Category.assoc
    (obj := GeneratedCategory.Object signature ⥤ D) before middle after

@[ext] theorem Model.ext {first second : Model signature D}
    (same : first.meanings = second.meanings) : first = second := by
  cases first
  cases second
  cases same
  rfl

def diagrams : Model signature D ⥤ (GeneratedCategory.Object signature ⥤ D) where
  obj model := model.diagram
  map cell := cell
  map_id _ := rfl
  map_comp _ _ := rfl

instance diagrams_faithful : (diagrams (signature := signature) (D := D)).Faithful where
  map_injective := fun same => same

instance diagrams_full : (diagrams (signature := signature) (D := D)).Full where
  map_surjective := fun cell => ⟨cell, rfl⟩

def isoOfDiagram {first second : Model signature D} (comparison : first.diagram ≅ second.diagram) :
    first ≅ second where
  hom := comparison.hom
  inv := comparison.inv
  hom_inv_id := comparison.hom_inv_id
  inv_hom_id := comparison.inv_hom_id

@[simp] theorem isoOfDiagram_hom {first second : Model signature D}
    (comparison : first.diagram ≅ second.diagram) :
    (isoOfDiagram comparison).hom = comparison.hom := rfl

end Mettapedia.CategoryTheory.RelativeClosedSyntax.SemanticModels
