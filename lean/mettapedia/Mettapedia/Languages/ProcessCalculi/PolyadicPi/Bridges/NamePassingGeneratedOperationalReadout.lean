import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorNaturality
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalActive

/-!
# Whole return-indexed source evidence readouts

The actual category compiler maps the source evidence object to complete
return-indexed target evidence. Its two independently generated ports read
the complete function endpoints. This comparison uses the entire category
restriction, including the original category and native base extension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open NamePassingGeneratedConstructorComparison

universe k

def sourcePortValue (side : Bool) : ArrowValue Target.{k} :=
  ⟨compiler.obj NamePassingGeneratedOperationalPresentation.edges,
    compiler.obj NamePassingGeneratedOperationalPresentation.programs,
    compiler.map (if side then NamePassingGeneratedOperationalPresentation.edgeTarget else
      NamePassingGeneratedOperationalPresentation.edgeSource)⟩

private theorem native_source_restriction : sourcePortValue.{k} false =
    NamePassingGeneratedOperationalCategory.value
      (RelativeClosedInternalCategory.ModelRealization.sourceCode NamePassingGeneratedOperationalCategory.vertex) := by
  have whole := congrArg
    (fun mapping : Object (RelativeClosedInternalCategory.Presentation.signature
      NamePassingGeneratedOperationalCategory.vertex) ⥤ Target =>
      (⟨mapping.obj (RelativeClosedInternalCategory.ModelRealization.edgeObject
          NamePassingGeneratedOperationalCategory.vertex),
        mapping.obj (RelativeClosedInternalCategory.ModelRealization.programObject
          NamePassingGeneratedOperationalCategory.vertex),
        mapping.map (classOf (RelativeClosedInternalCategory.ModelRealization.sourceCode
          NamePassingGeneratedOperationalCategory.vertex))⟩ : ArrowValue Target))
    NamePassingGeneratedOperationalCategory.complete_category_restriction
  exact whole

private theorem native_target_restriction : sourcePortValue.{k} true =
    NamePassingGeneratedOperationalCategory.value
      (RelativeClosedInternalCategory.ModelRealization.targetCode NamePassingGeneratedOperationalCategory.vertex) := by
  have whole := congrArg
    (fun mapping : Object (RelativeClosedInternalCategory.Presentation.signature
      NamePassingGeneratedOperationalCategory.vertex) ⥤ Target =>
      (⟨mapping.obj (RelativeClosedInternalCategory.ModelRealization.edgeObject
          NamePassingGeneratedOperationalCategory.vertex),
        mapping.obj (RelativeClosedInternalCategory.ModelRealization.programObject
          NamePassingGeneratedOperationalCategory.vertex),
        mapping.map (classOf (RelativeClosedInternalCategory.ModelRealization.targetCode
          NamePassingGeneratedOperationalCategory.vertex))⟩ : ArrowValue Target))
    NamePassingGeneratedOperationalCategory.complete_category_restriction
  exact whole

private theorem cast_result {C : Type k} [Category.{k} C] {before after edge : C}
    (same : before = after) (port : edge ⟶ after) :
    (⟨edge,before,port ≫ eqToHom same.symm⟩ : ArrowValue C) = ⟨edge,after,port⟩ := by
  cases same
  simp only [eqToHom_refl, Category.comp_id]

theorem whole_port_readout (side : Bool) : sourcePortValue.{k} side =
    ⟨NamePassingGeneratedOperational.continuations,
      NamePassingGeneratedOperationalCategory.ordinary.termObject,
      NamePassingGeneratedOperational.functionEndpoint side⟩ := by
  cases side with
  | false =>
      rw [native_source_restriction, NamePassingGeneratedOperationalCategory.source_readout]
      change (⟨NamePassingGeneratedOperational.continuations,
        NamePassingGeneratedOperationalCategory.base.obj NamePassingGeneratedOperationalCategory.vertex,
        (ihom NamePassingGeneratedOperationalCategory.ordinary.names).map
          BindingClosedGeneratedOperationalModel.category.source ≫
            (ihom NamePassingGeneratedOperationalCategory.ordinary.names).map
              BindingClosedGeneratedOperationalModel.processComparison.inv ≫
                eqToHom NamePassingGeneratedOperationalCategory.program_object.symm⟩ : ArrowValue Target) = _
      rw [← Category.assoc, ← Functor.map_comp]
      exact cast_result NamePassingGeneratedOperationalCategory.program_object _
  | true =>
      rw [native_target_restriction, NamePassingGeneratedOperationalCategory.target_readout]
      change (⟨NamePassingGeneratedOperational.continuations,
        NamePassingGeneratedOperationalCategory.base.obj NamePassingGeneratedOperationalCategory.vertex,
        (ihom NamePassingGeneratedOperationalCategory.ordinary.names).map
          BindingClosedGeneratedOperationalModel.category.target ≫
            (ihom NamePassingGeneratedOperationalCategory.ordinary.names).map
              BindingClosedGeneratedOperationalModel.processComparison.inv ≫
                eqToHom NamePassingGeneratedOperationalCategory.program_object.symm⟩ : ArrowValue Target) = _
      rw [← Category.assoc, ← Functor.map_comp]
      exact cast_result NamePassingGeneratedOperationalCategory.program_object _

theorem complete_edge_object : compiler.obj NamePassingGeneratedOperationalPresentation.edges.{k} =
    NamePassingGeneratedOperational.continuations :=
  congrArg ArrowValue.source (whole_port_readout false)

theorem complete_program_object : compiler.obj NamePassingGeneratedOperationalPresentation.programs.{k} =
    NamePassingGeneratedOperationalCategory.ordinary.termObject :=
  congrArg ArrowValue.target (whole_port_readout false)

theorem complete_endpoint_heq (side : Bool) :
    HEq (compiler.map (if side then NamePassingGeneratedOperationalPresentation.edgeTarget.{k} else
      NamePassingGeneratedOperationalPresentation.edgeSource))
      (NamePassingGeneratedOperational.functionEndpoint side) :=
  ArrowValue.arrows_heq (whole_port_readout side)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalReadout
