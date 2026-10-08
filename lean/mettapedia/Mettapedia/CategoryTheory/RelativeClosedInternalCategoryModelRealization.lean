import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryInterpretation
import Mettapedia.CategoryTheory.InternalCategoryEqualizerPresentation
import Mettapedia.CategoryTheory.InternalCategoryVertexIso

/-!
# Complete generated interpretation of an actual target category

Source and target universes are independent. An actual target category and
an independently supplied program-object isomorphism determine the evidence
operations. Transport and product-equalizer universal properties derive all
seven parser diagrams. No realization or global interpreter is model data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.ModelRealization

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation

universe k w z

variable {C : Type k} [Category.{k} C] (vertex : C)
variable {D : Type w} [Category.{z} D] [CartesianMonoidalCategory D] [HasFiniteLimits D]
variable (base : C ⥤ D) (original : InternalCategory D)
variable (comparison : base.obj vertex ≅ original.vertex)

abbrev targetCategory := InternalCategoryVertexIso.category original comparison

def operations : Meaning.Operations (base.obj vertex) where
  edge := original.edge
  source := (targetCategory vertex base original comparison).source
  target := (targetCategory vertex base original comparison).target
  unit := (targetCategory vertex base original comparison).unit
  composition := (InternalCategoryEqualizerPresentation.endpoints
    (targetCategory vertex base original comparison)).composition

theorem endpointLaws : Meaning.EndpointLaws vertex base (operations vertex base original comparison) where
  unitSource := (InternalCategoryEqualizerPresentation.endpoints
    (targetCategory vertex base original comparison)).unitSource
  unitTarget := (InternalCategoryEqualizerPresentation.endpoints
    (targetCategory vertex base original comparison)).unitTarget
  compositionSource := (InternalCategoryEqualizerPresentation.endpoints
    (targetCategory vertex base original comparison)).compositionSource
  compositionTarget := (InternalCategoryEqualizerPresentation.endpoints
    (targetCategory vertex base original comparison)).compositionTarget

theorem localLaws : ModelDiagrams.LocalLaws vertex base
    (operations vertex base original comparison) (endpointLaws vertex base original comparison) :=
  InternalCategoryEqualizerPresentation.laws (targetCategory vertex base original comparison)

theorem complete_compose_read {stage : D} (first second : stage ⟶ original.edge)
    (matching : first ≫ (operations vertex base original comparison).target =
      second ≫ (operations vertex base original comparison).source) :
    InternalCategoryPresentedDiagrams.compose
        (ModelDiagrams.endpoints vertex base (operations vertex base original comparison)
          (endpointLaws vertex base original comparison)) first second matching =
      original.compose first second (InternalCategoryVertexIso.matching original comparison first second matching) :=
  (InternalCategoryEqualizerPresentation.complete_compose_read
    (targetCategory vertex base original comparison) first second matching).trans
      (InternalCategoryVertexIso.complete_compose_read original comparison first second matching)

variable [MonoidalClosed D]

abbrev assignment := CategoryInterpretation.assignment vertex base (operations vertex base original comparison)

theorem realization : Interpretation.Realization (Presentation.signature vertex)
    (assignment vertex base original comparison) :=
  CategoryInterpretation.realization vertex base (operations vertex base original comparison)
    (endpointLaws vertex base original comparison) (localLaws vertex base original comparison)

def functor : Object (Presentation.signature vertex) ⥤ D :=
  CategoryInterpretation.functor vertex base (operations vertex base original comparison)
    (endpointLaws vertex base original comparison) (localLaws vertex base original comparison)

theorem complete_base_restriction :
    baseFunctor (Presentation.signature vertex) ⋙ functor vertex base original comparison = base :=
  Interpretation.functor_base (assignment vertex base original comparison)
    (realization vertex base original comparison)

theorem complete_old_object (supplied : C) :
    (functor vertex base original comparison).obj (baseObject (Presentation.signature vertex) supplied) =
      base.obj supplied :=
  Interpretation.functor_base_object (assignment vertex base original comparison)
    (realization vertex base original comparison) supplied

def compositionSource := (Presentation.inclusion vertex).object (Endpoints.composable vertex)
def edgeObject := (Presentation.inclusion vertex).object (Endpoints.edgeObject vertex)
def programObject := (Presentation.inclusion vertex).object (Endpoints.vertexObject vertex)

def compositionCode := (Presentation.inclusion vertex).rawArrow (Endpoints.composition vertex)
def sourceCode := (Presentation.inclusion vertex).rawArrow (Endpoints.source vertex)
def targetCode := (Presentation.inclusion vertex).rawArrow (Endpoints.target vertex)
def unitCode := (Presentation.inclusion vertex).rawArrow (Endpoints.unit vertex)

theorem complete_generated_composition :
    (⟨(functor vertex base original comparison).obj (compositionSource vertex),
      (functor vertex base original comparison).obj (edgeObject vertex),
      (functor vertex base original comparison).map (classOf (compositionCode vertex))⟩ : ArrowValue D) =
        ⟨(operations vertex base original comparison).toGraph.composable, original.edge,
          (operations vertex base original comparison).composition⟩ := by
  have complete := Interpretation.functor_complete_readout (assignment vertex base original comparison)
    (realization vertex base original comparison) (compositionCode vertex)
  have originalRead := (EquationExtension.evaluate_arrow_original (endpointSignature vertex)
    (Presentation.declaration vertex) (EquationReadout.assignment vertex base (operations vertex base original comparison))
      (Endpoints.composition vertex).code).trans
        (EquationReadout.composition_read vertex base (operations vertex base original comparison))
  exact Option.some.inj (complete.symm.trans originalRead)

theorem complete_generated_source :
    (⟨(functor vertex base original comparison).obj (edgeObject vertex),
      (functor vertex base original comparison).obj (programObject vertex),
      (functor vertex base original comparison).map (classOf (sourceCode vertex))⟩ : ArrowValue D) =
        ⟨original.edge, base.obj vertex, original.source ≫ comparison.inv⟩ := by
  have complete := Interpretation.functor_complete_readout (assignment vertex base original comparison)
    (realization vertex base original comparison) (sourceCode vertex)
  have originalRead := (EquationExtension.evaluate_arrow_original (endpointSignature vertex)
    (Presentation.declaration vertex) (EquationReadout.assignment vertex base (operations vertex base original comparison))
      (Endpoints.source vertex).code).trans
        (EquationReadout.source_read vertex base (operations vertex base original comparison))
  exact Option.some.inj (complete.symm.trans originalRead)

theorem complete_generated_target :
    (⟨(functor vertex base original comparison).obj (edgeObject vertex),
      (functor vertex base original comparison).obj (programObject vertex),
      (functor vertex base original comparison).map (classOf (targetCode vertex))⟩ : ArrowValue D) =
        ⟨original.edge, base.obj vertex, original.target ≫ comparison.inv⟩ := by
  have complete := Interpretation.functor_complete_readout (assignment vertex base original comparison)
    (realization vertex base original comparison) (targetCode vertex)
  have originalRead := (EquationExtension.evaluate_arrow_original (endpointSignature vertex)
    (Presentation.declaration vertex) (EquationReadout.assignment vertex base (operations vertex base original comparison))
      (Endpoints.target vertex).code).trans
        (EquationReadout.target_read vertex base (operations vertex base original comparison))
  exact Option.some.inj (complete.symm.trans originalRead)

theorem complete_generated_unit :
    (⟨(functor vertex base original comparison).obj (programObject vertex),
      (functor vertex base original comparison).obj (edgeObject vertex),
      (functor vertex base original comparison).map (classOf (unitCode vertex))⟩ : ArrowValue D) =
        ⟨base.obj vertex, original.edge, comparison.hom ≫ original.unit⟩ := by
  have complete := Interpretation.functor_complete_readout (assignment vertex base original comparison)
    (realization vertex base original comparison) (unitCode vertex)
  have originalRead := (EquationExtension.evaluate_arrow_original (endpointSignature vertex)
    (Presentation.declaration vertex) (EquationReadout.assignment vertex base (operations vertex base original comparison))
      (Endpoints.unit vertex).code).trans
        (EquationReadout.unit_read vertex base (operations vertex base original comparison))
  exact Option.some.inj (complete.symm.trans originalRead)

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.ModelRealization
