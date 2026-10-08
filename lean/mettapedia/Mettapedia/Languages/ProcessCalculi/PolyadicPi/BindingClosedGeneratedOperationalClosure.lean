import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalEndpoints
import Mettapedia.OSLF.Syntax.BindingClosedGeneratedFunctor

/-!
# Independently declared parallel and private evidence closure

The old category guest's complete binding operations survive its actual
rule-declaration inclusion. The chosen product and function comparisons earn
that statement. They then transport the independently declared closure
generators to the final guest's actual edge and program objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalClosure

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open Mettapedia.OSLF.Binding
open BindingClosedPrimitiveOperations

universe k

section BindingTransport

variable {D E : Type k} [Category.{k} D] [Category.{k} E]
variable {middleNames targetNames : Symbols.{k}}
variable {middle : Mettapedia.CategoryTheory.RelativeClosedSyntax.Signature (C := D) (symbols := middleNames)}
variable {target : Mettapedia.CategoryTheory.RelativeClosedSyntax.Signature (C := E) (symbols := targetNames)}
variable (mapping : SignatureMap middle target)
variable (binding : ClosedPresentation.Operations AllArity.sig (Object middle))

abbrev mapped := ClosedPresentation.GeneratedFunctor.mapOperations mapping binding

theorem plain_transport (result : AllArity.sig.Srt) :
    plain (mapped mapping binding) result = mapping.functor.map (plain binding result) := by
  unfold plain
  rw [mapping.functor_curry]
  rfl

theorem unaryBody_transport :
    unaryBody (mapped mapping binding) = mapping.functor.map (unaryBody binding) := by
  unfold unaryBody
  rw [mapping.functor_pre, mapping.functor_rightUnitor_hom]
  rfl

theorem parallel_transport : (continuation (mapped mapping binding)).parallel =
    mapping.functor.map (continuation binding).parallel := by
  change lift (fst _ _ ≫ plain (mapped mapping binding) .pr)
      (lift (snd _ _ ≫ plain (mapped mapping binding) .pr) (toUnit _)) ≫
        (mapped mapping binding).operation AllArity.Op.par =
    mapping.functor.map (lift (fst _ _ ≫ plain binding .pr)
      (lift (snd _ _ ≫ plain binding .pr) (toUnit _)) ≫ binding.operation AllArity.Op.par)
  have operation : (mapped mapping binding).operation AllArity.Op.par =
      mapping.functor.map (binding.operation AllArity.Op.par) :=
    eq_of_heq (ClosedPresentation.GeneratedFunctor.mapOperations_operation_heq mapping binding AllArity.Op.par)
  rw [operation, mapping.functor.map_comp, mapping.functor_lift,
    mapping.functor_lift, mapping.functor.map_comp, mapping.functor.map_comp,
    mapping.functor_toUnit, plain_transport]
  rfl

theorem fresh_transport : (continuation (mapped mapping binding)).fresh =
    mapping.functor.map (continuation binding).fresh := by
  change lift (unaryBody (mapped mapping binding)) (toUnit _) ≫
    (mapped mapping binding).operation AllArity.Op.nu =
    mapping.functor.map (lift (unaryBody binding) (toUnit _) ≫ binding.operation AllArity.Op.nu)
  have operation : (mapped mapping binding).operation AllArity.Op.nu =
      mapping.functor.map (binding.operation AllArity.Op.nu) :=
    eq_of_heq (ClosedPresentation.GeneratedFunctor.mapOperations_operation_heq mapping binding AllArity.Op.nu)
  rw [operation, mapping.functor.map_comp, mapping.functor_lift,
    mapping.functor_toUnit, unaryBody_transport]
  rfl

end BindingTransport

abbrev oldBinding := BindingClosedGeneratedOperational.binding.{k}
abbrev oldOrdinary := BindingClosedGeneratedOperational.ordinary.{k}
abbrev inclusion := BindingClosedGeneratedOperationalModel.ruleInclusion.{k}
abbrev binding := BindingClosedGeneratedOperationalModel.binding.{k}
abbrev ordinary := BindingClosedGeneratedOperationalModel.ordinary.{k}
abbrev category := BindingClosedGeneratedOperationalModel.category.{k}

theorem binding_transport : binding.{k} = mapped inclusion oldBinding := by
  let : PreservesFiniteLimits BindingClosedGeneratedOperational.constructors.{k} :=
    BindingClosedGeneratedOperational.constructors_finite
  let : MonoidalClosedFunctor BindingClosedGeneratedOperational.constructors.{k} :=
    BindingClosedGeneratedOperational.constructors_closed
  exact ClosedPresentation.GeneratedFunctor.operations_postcomposition inclusion
    BindingClosedGeneratedOperational.constructors

theorem complete_parallel_transport : ordinary.{k}.parallel =
    inclusion.functor.map oldOrdinary.parallel := by
  have complete := congrArg (fun operations : ClosedPresentation.Operations AllArity.sig
      BindingClosedGeneratedOperationalModel.Target.{k} =>
    (⟨(continuation operations).processes ⊗ (continuation operations).processes,
      (continuation operations).processes, (continuation operations).parallel⟩ :
        Interpretation.ArrowValue BindingClosedGeneratedOperationalModel.Target)) binding_transport
  exact (eq_of_heq (Interpretation.ArrowValue.arrows_heq complete)).trans
    (parallel_transport inclusion oldBinding)

theorem complete_private_transport : ordinary.{k}.fresh =
    inclusion.functor.map oldOrdinary.fresh := by
  have complete := congrArg (fun operations : ClosedPresentation.Operations AllArity.sig
      BindingClosedGeneratedOperationalModel.Target.{k} =>
    (⟨(continuation operations).names ⟶[BindingClosedGeneratedOperationalModel.Target] (continuation operations).processes,
      (continuation operations).processes, (continuation operations).fresh⟩ :
        Interpretation.ArrowValue BindingClosedGeneratedOperationalModel.Target)) binding_transport
  exact (eq_of_heq (Interpretation.ArrowValue.arrows_heq complete)).trans
    (fresh_transport inclusion oldBinding)

abbrev vertex := BindingClosedGeneratedOperationalEndpoints.vertex.{k}
abbrev categoryMap := BindingClosedGeneratedOperationalEndpoints.categoryMap.{k}
abbrev declarations := BindingClosedGeneratedOperationalEndpoints.declarations.{k}
abbrev arrowInclusion := BindingClosedGeneratedOperationalEndpoints.arrowInclusion.{k}
abbrev equationInclusion := BindingClosedGeneratedOperationalEndpoints.equationInclusion.{k}

def domainComparison (origin : ULift.{k} BindingClosedGeneratedOperational.Origin) :
    RelativeClosedInternalCategory.RulePresentation.ruleDomain vertex categoryMap declarations origin ≅
      inclusion.functor.obj (declarations origin).domain :=
  eqToIso (SignatureMap.object_compose arrowInclusion equationInclusion (declarations origin).domain)

def translatedEdgeComparison : inclusion.functor.obj BindingClosedGeneratedOperational.edges.{k} ≅ category.edge :=
  (eqToIso (SignatureMap.object_compose arrowInclusion equationInclusion
    BindingClosedGeneratedOperational.edges)).symm ≪≫ BindingClosedGeneratedOperationalEndpoints.edgeComparison

def translatedProgramComparison : inclusion.functor.obj BindingClosedGeneratedOperational.programs.{k} ≅ category.vertex :=
  (eqToIso (SignatureMap.object_compose arrowInclusion equationInclusion
    BindingClosedGeneratedOperational.programs)).symm ≪≫ BindingClosedGeneratedOperationalEndpoints.vertexComparison

theorem translated_program_comparison : translatedProgramComparison.{k} =
    BindingClosedGeneratedOperationalModel.processComparison := by
  apply Iso.ext
  simp only [translatedProgramComparison, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
    eqToHom_refl, Category.id_comp]
  rfl

private theorem composition_square {first last : BindingClosedGeneratedOperational.CategoryGuest.{k}}
    (arrow : first ⟶ last) :
    eqToHom (SignatureMap.object_compose arrowInclusion equationInclusion first) ≫ inclusion.functor.map arrow =
      equationInclusion.functor.map (arrowInclusion.functor.map arrow) ≫
        eqToHom (SignatureMap.object_compose arrowInclusion equationInclusion last) :=
  equationInclusion.functor_composition_readout arrowInclusion arrow

private theorem translated_endpoint {first last : BindingClosedGeneratedOperational.CategoryGuest.{k}}
    (arrow : first ⟶ last) :
    eqToHom (SignatureMap.object_compose arrowInclusion equationInclusion first).symm ≫
        equationInclusion.functor.map (arrowInclusion.functor.map arrow) =
      inclusion.functor.map arrow ≫
        eqToHom (SignatureMap.object_compose arrowInclusion equationInclusion last).symm := by
  have whole := congrArg (fun observed =>
    eqToHom (SignatureMap.object_compose arrowInclusion equationInclusion first).symm ≫ observed ≫
      eqToHom (SignatureMap.object_compose arrowInclusion equationInclusion last).symm)
        (composition_square arrow)
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id] using whole.symm

theorem translated_edge_source : translatedEdgeComparison.{k}.hom ≫ category.source =
    inclusion.functor.map BindingClosedGeneratedOperational.edgeSource ≫ translatedProgramComparison.hom := by
  rw [translatedEdgeComparison, translatedProgramComparison, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_hom, Iso.symm_hom, eqToIso.inv, eqToIso.inv, Category.assoc,
    BindingClosedGeneratedOperationalEndpoints.complete_source_square]
  have whole := congrArg (fun observed => observed ≫ BindingClosedGeneratedOperationalEndpoints.vertexComparison.hom)
    (translated_endpoint BindingClosedGeneratedOperational.edgeSource)
  simp only [Category.assoc] at whole
  exact whole

theorem translated_edge_target : translatedEdgeComparison.{k}.hom ≫ category.target =
    inclusion.functor.map BindingClosedGeneratedOperational.edgeTarget ≫ translatedProgramComparison.hom := by
  rw [translatedEdgeComparison, translatedProgramComparison, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_hom, Iso.symm_hom, eqToIso.inv, eqToIso.inv, Category.assoc,
    BindingClosedGeneratedOperationalEndpoints.complete_target_square]
  have whole := congrArg (fun observed => observed ≫ BindingClosedGeneratedOperationalEndpoints.vertexComparison.hom)
    (translated_endpoint BindingClosedGeneratedOperational.edgeTarget)
  simp only [Category.assoc] at whole
  exact whole

theorem source_through_translated_edge : translatedEdgeComparison.{k}.inv ≫
    inclusion.functor.map BindingClosedGeneratedOperational.edgeSource =
      category.source ≫ translatedProgramComparison.inv := by
  apply (cancel_mono translatedProgramComparison.hom).mp
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← translated_edge_source, Iso.inv_hom_id_assoc]

theorem target_through_translated_edge : translatedEdgeComparison.{k}.inv ≫
    inclusion.functor.map BindingClosedGeneratedOperational.edgeTarget =
      category.target ≫ translatedProgramComparison.inv := by
  apply (cancel_mono translatedProgramComparison.hom).mp
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← translated_edge_target, Iso.inv_hom_id_assoc]

theorem complete_before (origin : ULift.{k} BindingClosedGeneratedOperational.Origin) :
    (domainComparison origin).hom ≫ inclusion.functor.map (classOf (declarations origin).before) ≫
        translatedProgramComparison.hom =
      classOf (RelativeClosedInternalCategory.RulePresentation.before vertex categoryMap declarations origin) ≫
        BindingClosedGeneratedOperationalEndpoints.vertexComparison.hom := by
  rw [domainComparison, translatedProgramComparison, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv]
  rw [← Category.assoc, composition_square]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  rfl

theorem complete_after (origin : ULift.{k} BindingClosedGeneratedOperational.Origin) :
    (domainComparison origin).hom ≫ inclusion.functor.map (classOf (declarations origin).after) ≫
        translatedProgramComparison.hom =
      classOf (RelativeClosedInternalCategory.RulePresentation.after vertex categoryMap declarations origin) ≫
        BindingClosedGeneratedOperationalEndpoints.vertexComparison.hom := by
  rw [domainComparison, translatedProgramComparison, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv]
  rw [← Category.assoc, composition_square]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  rfl

def parallelOrigin : ULift.{k} BindingClosedGeneratedOperational.Origin := ⟨.parallel⟩
def privateOrigin : ULift.{k} BindingClosedGeneratedOperational.Origin := ⟨.restriction⟩

def parallelStageComparison :
    RelativeClosedInternalCategory.RulePresentation.ruleDomain vertex.{k} categoryMap declarations parallelOrigin ≅
      category.edge ⊗ ordinary.processes :=
  domainComparison parallelOrigin ≪≫ tensorIso translatedEdgeComparison (Iso.refl ordinary.processes)

def privateStageComparison :
    RelativeClosedInternalCategory.RulePresentation.ruleDomain vertex.{k} categoryMap declarations privateOrigin ≅
      (ordinary.names ⟶[BindingClosedGeneratedOperationalModel.Target] category.edge) :=
  domainComparison privateOrigin ≪≫ (ihom ordinary.names).mapIso translatedEdgeComparison

def parallel : category.{k}.edge ⊗ ordinary.processes ⟶ category.edge :=
  parallelStageComparison.inv ≫ BindingClosedGeneratedOperationalEndpoints.firing parallelOrigin

def restriction : (ordinary.{k}.names ⟶[BindingClosedGeneratedOperationalModel.Target] category.edge) ⟶ category.edge :=
  privateStageComparison.inv ≫ BindingClosedGeneratedOperationalEndpoints.firing privateOrigin

theorem parallel_source : parallel.{k} ≫ category.source =
    lift (fst category.edge ordinary.processes ≫ category.source ≫
      BindingClosedGeneratedOperationalModel.processComparison.inv) (snd category.edge ordinary.processes) ≫
        ordinary.parallel ≫ BindingClosedGeneratedOperationalModel.processComparison.hom := by
  rw [parallel, Category.assoc, BindingClosedGeneratedOperationalEndpoints.firing_source, ← complete_before]
  simp only [parallelStageComparison, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
  erw [BindingClosedGeneratedOperational.complete_parallel_source]
  rw [inclusion.functor.map_comp, inclusion.functor_lift, inclusion.functor.map_comp]
  rw [← complete_parallel_transport, ← translated_program_comparison]
  simp only [tensorIso_inv, Iso.refl_inv, Category.assoc]
  change (translatedEdgeComparison.inv ⊗ₘ 𝟙 ordinary.processes) ≫
      lift (fst (inclusion.functor.obj BindingClosedGeneratedOperational.edges) ordinary.processes ≫
        inclusion.functor.map BindingClosedGeneratedOperational.edgeSource)
        (snd (inclusion.functor.obj BindingClosedGeneratedOperational.edges) ordinary.processes) ≫
      ordinary.parallel ≫ translatedProgramComparison.hom = _
  rw [comp_lift_assoc]
  simp only [tensorHom_fst_assoc, tensorHom_snd, Category.comp_id]
  rw [source_through_translated_edge]

theorem parallel_target : parallel.{k} ≫ category.target =
    lift (fst category.edge ordinary.processes ≫ category.target ≫
      BindingClosedGeneratedOperationalModel.processComparison.inv) (snd category.edge ordinary.processes) ≫
        ordinary.parallel ≫ BindingClosedGeneratedOperationalModel.processComparison.hom := by
  rw [parallel, Category.assoc, BindingClosedGeneratedOperationalEndpoints.firing_target, ← complete_after]
  simp only [parallelStageComparison, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
  erw [BindingClosedGeneratedOperational.complete_parallel_target]
  rw [inclusion.functor.map_comp, inclusion.functor_lift, inclusion.functor.map_comp]
  rw [← complete_parallel_transport, ← translated_program_comparison]
  simp only [tensorIso_inv, Iso.refl_inv, Category.assoc]
  change (translatedEdgeComparison.inv ⊗ₘ 𝟙 ordinary.processes) ≫
      lift (fst (inclusion.functor.obj BindingClosedGeneratedOperational.edges) ordinary.processes ≫
        inclusion.functor.map BindingClosedGeneratedOperational.edgeTarget)
        (snd (inclusion.functor.obj BindingClosedGeneratedOperational.edges) ordinary.processes) ≫
      ordinary.parallel ≫ translatedProgramComparison.hom = _
  rw [comp_lift_assoc]
  simp only [tensorHom_fst_assoc, tensorHom_snd, Category.comp_id]
  rw [target_through_translated_edge]

theorem private_source : restriction.{k} ≫ category.source =
    (ihom ordinary.names).map (category.source ≫ BindingClosedGeneratedOperationalModel.processComparison.inv) ≫
      ordinary.fresh ≫ BindingClosedGeneratedOperationalModel.processComparison.hom := by
  rw [restriction, Category.assoc, BindingClosedGeneratedOperationalEndpoints.firing_source, ← complete_before]
  simp only [privateStageComparison, Iso.trans_inv, Functor.mapIso_inv, Category.assoc, Iso.inv_hom_id_assoc]
  erw [BindingClosedGeneratedOperational.complete_private_source]
  rw [inclusion.functor.map_comp, inclusion.functor_ihom]
  rw [← complete_private_transport, ← translated_program_comparison]
  simp only [Category.assoc]
  change (ihom ordinary.names).map translatedEdgeComparison.inv ≫
      (ihom ordinary.names).map (inclusion.functor.map BindingClosedGeneratedOperational.edgeSource) ≫
        ordinary.fresh ≫ translatedProgramComparison.hom = _
  rw [← Functor.map_comp_assoc, source_through_translated_edge]

theorem private_target : restriction.{k} ≫ category.target =
    (ihom ordinary.names).map (category.target ≫ BindingClosedGeneratedOperationalModel.processComparison.inv) ≫
      ordinary.fresh ≫ BindingClosedGeneratedOperationalModel.processComparison.hom := by
  rw [restriction, Category.assoc, BindingClosedGeneratedOperationalEndpoints.firing_target, ← complete_after]
  simp only [privateStageComparison, Iso.trans_inv, Functor.mapIso_inv, Category.assoc, Iso.inv_hom_id_assoc]
  erw [BindingClosedGeneratedOperational.complete_private_target]
  rw [inclusion.functor.map_comp, inclusion.functor_ihom]
  rw [← complete_private_transport, ← translated_program_comparison]
  simp only [Category.assoc]
  change (ihom ordinary.names).map translatedEdgeComparison.inv ≫
      (ihom ordinary.names).map (inclusion.functor.map BindingClosedGeneratedOperational.edgeTarget) ≫
        ordinary.fresh ≫ translatedProgramComparison.hom = _
  rw [← Functor.map_comp_assoc, target_through_translated_edge]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalClosure
