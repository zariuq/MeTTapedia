import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalSchemaSemantics
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalCategory
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryRuleInterpretation

/-!
# Whole native readings of independently declared reduction endpoints

The generated premise objects retain their entire ordinary context and
metavariable function family. Their object and arrow comparisons are earned
from the actual static interpretation. Independent raw beta and fetch
expressions evaluate to the complete continuation ports, rather than ports
defined by the operational evidence chosen later.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalNativeReadout

open _root_.CategoryTheory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding CategoricalBindingModel
open NamePassingCategoricalCompiler NamePassingContinuationOperations NamePassingBindingClosedOperations
open NamePassingBindingClosedOperationalPresentation
open NamePassingBindingClosedOperationalSchemaSemantics

abbrev model := Native.operations.model
abbrev originalMeanings := NamePassingBindingClosedOperationalCategory.nativeMeanings
abbrev originalRealization := NamePassingBindingClosedOperationalCategory.native_all_seven_diagrams
abbrev originalFunctor := Interpretation.functor originalMeanings originalRealization

def domain (origin : Origin) : Ambient :=
  model.ctx (context origin) ⊗ model.family (NamePassingBindingClosedOperationalPresentation.metas origin)

def genericBefore (origin : Origin) : domain origin ⟶ operations.termObject :=
  model.generic (NamePassingBindingClosedOperationalPresentation.metas origin) (beforeTerm origin)

def genericAfter (origin : Origin) : domain origin ⟶ operations.termObject :=
  model.generic (NamePassingBindingClosedOperationalPresentation.metas origin) (afterTerm origin)

theorem static_before_readout (origin : Origin) :
    (⟨NamePassingBindingClosedOperationalCategory.base.obj (staticStage origin),
      NamePassingBindingClosedOperationalCategory.base.obj vertex,
      NamePassingBindingClosedOperationalCategory.base.map (staticBefore origin)⟩ : ArrowValue Ambient) =
        ⟨domain origin,operations.termObject,genericBefore origin⟩ := by
  have reading := Native.operations.schema_complete_readout (beforeTerm origin)
  rw [← NamePassingBindingClosedSchemas.complete_restriction] at reading
  exact reading

theorem static_after_readout (origin : Origin) :
    (⟨NamePassingBindingClosedOperationalCategory.base.obj (staticStage origin),
      NamePassingBindingClosedOperationalCategory.base.obj vertex,
      NamePassingBindingClosedOperationalCategory.base.map (staticAfter origin)⟩ : ArrowValue Ambient) =
        ⟨domain origin,operations.termObject,genericAfter origin⟩ := by
  have reading := Native.operations.schema_complete_readout (afterTerm origin)
  rw [← NamePassingBindingClosedSchemas.complete_restriction] at reading
  exact reading

abbrev premise (origin : Origin) :=
  RelativeClosedInternalCategory.RuleInterpretation.premise
    vertex categoryMap declarations originalMeanings originalRealization origin

abbrev programs := RelativeClosedInternalCategory.RuleInterpretation.programs
  vertex categoryMap originalMeanings originalRealization

abbrev edges := RelativeClosedInternalCategory.RuleInterpretation.edges
  vertex categoryMap originalMeanings originalRealization

theorem premise_object (origin : Origin) : premise origin = domain origin :=
  congrArg ArrowValue.source (static_before_readout origin)

theorem program_object : programs = operations.termObject :=
  NamePassingBindingClosedOperationalCategory.program_object

theorem source_complete :
    (⟨edges,programs,originalFunctor.map
      (classOf (RelativeClosedInternalCategory.NativeCategory.source vertex categoryMap))⟩ : ArrowValue Ambient) =
    ⟨CategoricalOperationalContinuations.category.edge,programs,
      CategoricalOperationalContinuations.category.source ≫
        NamePassingBindingClosedOperationalCategory.programComparison.inv⟩ :=
  (NamePassingBindingClosedOperationalCategory.native_value_readout
    NamePassingBindingClosedOperationalCategory.sourceCode).trans
      NamePassingBindingClosedOperationalCategory.source_readout

theorem target_complete :
    (⟨edges,programs,originalFunctor.map
      (classOf (RelativeClosedInternalCategory.NativeCategory.target vertex categoryMap))⟩ : ArrowValue Ambient) =
    ⟨CategoricalOperationalContinuations.category.edge,programs,
      CategoricalOperationalContinuations.category.target ≫
        NamePassingBindingClosedOperationalCategory.programComparison.inv⟩ :=
  (NamePassingBindingClosedOperationalCategory.native_value_readout
    NamePassingBindingClosedOperationalCategory.targetCode).trans
      NamePassingBindingClosedOperationalCategory.target_readout

theorem edge_object : edges = CategoricalOperationalContinuations.category.edge :=
  congrArg ArrowValue.source source_complete

theorem before_complete (origin : Origin) :
    (⟨premise origin,programs,originalFunctor.map (classOf (before origin))⟩ : ArrowValue Ambient) =
      ⟨domain origin,operations.termObject,genericBefore origin⟩ := by
  have complete := functor_complete_readout originalMeanings originalRealization (before origin)
  have actual := originalMeanings.evaluate_base_arrow (staticBefore origin)
  exact (Option.some.inj (complete.symm.trans actual)).trans (static_before_readout origin)

theorem after_complete (origin : Origin) :
    (⟨premise origin,programs,originalFunctor.map (classOf (after origin))⟩ : ArrowValue Ambient) =
      ⟨domain origin,operations.termObject,genericAfter origin⟩ := by
  have complete := functor_complete_readout originalMeanings originalRealization (after origin)
  have actual := originalMeanings.evaluate_base_arrow (staticAfter origin)
  exact (Option.some.inj (complete.symm.trans actual)).trans (static_after_readout origin)

theorem source_arrow : originalFunctor.map
    (classOf (RelativeClosedInternalCategory.NativeCategory.source vertex categoryMap)) =
      eqToHom edge_object ≫ CategoricalOperationalContinuations.category.source ≫
        NamePassingBindingClosedOperationalCategory.programComparison.inv := by
  simpa only [eqToHom_refl,Category.comp_id] using
    (conj_eqToHom_iff_heq _ _ edge_object rfl).mpr (ArrowValue.arrows_heq source_complete)

theorem target_arrow : originalFunctor.map
    (classOf (RelativeClosedInternalCategory.NativeCategory.target vertex categoryMap)) =
      eqToHom edge_object ≫ CategoricalOperationalContinuations.category.target ≫
        NamePassingBindingClosedOperationalCategory.programComparison.inv := by
  simpa only [eqToHom_refl,Category.comp_id] using
    (conj_eqToHom_iff_heq _ _ edge_object rfl).mpr (ArrowValue.arrows_heq target_complete)

theorem before_arrow (origin : Origin) : originalFunctor.map (classOf (before origin)) =
    eqToHom (premise_object origin) ≫ genericBefore origin ≫
      NamePassingBindingClosedOperationalCategory.programComparison.inv :=
  (conj_eqToHom_iff_heq _ _ (premise_object origin) program_object).mpr
    (ArrowValue.arrows_heq (before_complete origin))

theorem after_arrow (origin : Origin) : originalFunctor.map (classOf (after origin)) =
    eqToHom (premise_object origin) ≫ genericAfter origin ≫
      NamePassingBindingClosedOperationalCategory.programComparison.inv :=
  (conj_eqToHom_iff_heq _ _ (premise_object origin) program_object).mpr
    (ArrowValue.arrows_heq (after_complete origin))

def betaBodyInput : domain .beta ⟶ operations.boundBodyObject :=
  snd (operations.names ⊗ 𝟙_ Ambient)
    ((ihom (operations.names ⊗ 𝟙_ Ambient)).obj operations.termObject ⊗ 𝟙_ Ambient) ≫
      fst _ _ ≫ boundValue operations

def betaArgumentInput : domain .beta ⟶ operations.names :=
  fst (operations.names ⊗ 𝟙_ Ambient)
    ((ihom (operations.names ⊗ 𝟙_ Ambient)).obj operations.termObject ⊗ 𝟙_ Ambient) ≫
      fst operations.names (𝟙_ Ambient)

def betaInput : domain .beta ⟶ NamePassingCategoricalOperational.betaDomain :=
  lift betaBodyInput betaArgumentInput

def fetchNameInput : domain .fetch ⟶ operations.names :=
  fst (operations.names ⊗ (operations.termObject ⊗ 𝟙_ Ambient)) (𝟙_ Ambient) ≫ fst _ _

def fetchValueInput : domain .fetch ⟶ operations.termObject :=
  fst (operations.names ⊗ (operations.termObject ⊗ 𝟙_ Ambient)) (𝟙_ Ambient) ≫
    snd operations.names (operations.termObject ⊗ 𝟙_ Ambient) ≫ fst _ _

def fetchInput : domain .fetch ⟶ NamePassingCategoricalOperational.fetchDomain :=
  lift fetchNameInput fetchValueInput

theorem beta_before : genericBefore .beta = betaInput ≫ NamePassingCategoricalOperational.betaSource := by
  unfold genericBefore Model.generic
  erw [beta_before_value]
  change lift (betaBodyInput ≫ operations.abstraction) betaArgumentInput ≫ operations.application = _
  simp only [betaInput,NamePassingCategoricalOperational.betaSource,
    comp_lift_assoc,lift_fst_assoc,lift_snd]

theorem beta_after : genericAfter .beta = betaInput ≫ NamePassingCategoricalOperational.betaTarget := by
  unfold genericAfter Model.generic
  erw [beta_after_value]
  change call betaBodyInput betaArgumentInput = _
  simp only [betaInput,NamePassingCategoricalOperational.betaTarget,call,
    comp_lift_assoc,lift_fst,lift_snd]

theorem fetch_before : genericBefore .fetch = fetchInput ≫ NamePassingCategoricalOperational.fetchSource := by
  unfold genericBefore Model.generic
  erw [fetch_before_value]
  change lift fetchNameInput (lift fetchValueInput (fetchNameInput ≫ operations.reference)) ≫
    operations.carrier = _
  simp only [fetchInput,NamePassingCategoricalOperational.fetchSource,
    comp_lift_assoc,comp_lift,lift_fst_assoc,lift_fst,lift_snd]

theorem fetch_after : genericAfter .fetch = fetchInput ≫ snd operations.names operations.termObject := by
  unfold genericAfter Model.generic
  erw [fetch_after_value]
  change fetchValueInput = _
  simp only [fetchInput,lift_snd]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalNativeReadout
