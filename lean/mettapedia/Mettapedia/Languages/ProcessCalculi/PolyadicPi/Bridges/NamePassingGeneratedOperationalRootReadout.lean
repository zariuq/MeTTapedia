import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalReadout
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalSchemaSemantics

/-!
# Authored beta and fetch premise images in the generated target

The actual compiler restriction evaluates both independent raw endpoints.
The beta premise retains its full one-reference function family; its padded
unit context is compared with the ordinary beta evidence input. Fetch keeps
the name and stored continuation separately. Both actual target firings have
these complete program endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalRootReadout

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding CategoricalBindingModel
open NamePassingGeneratedConstructorComparison
open NamePassingBindingClosedOperations
open NamePassingBindingClosedOperationalSchemaSemantics

universe k

abbrev model := targetOperations.{k}.model
abbrev ordinary := NamePassingGeneratedOperationalCategory.ordinary.{k}

def domain (fetch : Bool) : Target.{k} := model.ctx (NamePassingGeneratedOperationalPresentation.rootContext fetch) ⊗
  model.family (NamePassingGeneratedOperationalPresentation.rootMetas fetch)

def before (fetch : Bool) : domain.{k} fetch ⟶ ordinary.termObject :=
  model.generic (NamePassingGeneratedOperationalPresentation.rootMetas fetch)
    (NamePassingGeneratedOperationalPresentation.rootBefore fetch)

def after (fetch : Bool) : domain.{k} fetch ⟶ ordinary.termObject :=
  model.generic (NamePassingGeneratedOperationalPresentation.rootMetas fetch)
    (NamePassingGeneratedOperationalPresentation.rootAfter fetch)

theorem static_before_readout (fetch : Bool) :
    (⟨NamePassingGeneratedOperationalCategory.base.obj
      (NamePassingGeneratedOperationalPresentation.rootStage fetch),
      NamePassingGeneratedOperationalCategory.base.obj NamePassingGeneratedOperationalCategory.vertex,
      NamePassingGeneratedOperationalCategory.base.map
        (NamePassingGeneratedOperationalPresentation.staticInclusion.functor.map
          (classOf (ClosedPresentation.SchemaExpressions.expression
            NamePassingGeneratedOperationalPresentation.sourceBinding
              (NamePassingGeneratedOperationalPresentation.rootBefore fetch))))⟩ : ArrowValue Target.{k}) =
      ⟨domain fetch,ordinary.termObject,before fetch⟩ := by
  have whole := targetOperations.schema_complete_readout
    (NamePassingGeneratedOperationalPresentation.rootBefore fetch)
  dsimp only [targetOperations] at whole
  rw [← NamePassingGeneratedStatic.complete_restriction
    NamePassingGeneratedOperationalCategory.binding BindingClosedGeneratedOperationalModel.structural_schemas] at whole
  exact whole

theorem static_after_readout (fetch : Bool) :
    (⟨NamePassingGeneratedOperationalCategory.base.obj
      (NamePassingGeneratedOperationalPresentation.rootStage fetch),
      NamePassingGeneratedOperationalCategory.base.obj NamePassingGeneratedOperationalCategory.vertex,
      NamePassingGeneratedOperationalCategory.base.map
        (NamePassingGeneratedOperationalPresentation.staticInclusion.functor.map
          (classOf (ClosedPresentation.SchemaExpressions.expression
            NamePassingGeneratedOperationalPresentation.sourceBinding
              (NamePassingGeneratedOperationalPresentation.rootAfter fetch))))⟩ : ArrowValue Target.{k}) =
      ⟨domain fetch,ordinary.termObject,after fetch⟩ := by
  have whole := targetOperations.schema_complete_readout
    (NamePassingGeneratedOperationalPresentation.rootAfter fetch)
  dsimp only [targetOperations] at whole
  rw [← NamePassingGeneratedStatic.complete_restriction
    NamePassingGeneratedOperationalCategory.binding BindingClosedGeneratedOperationalModel.structural_schemas] at whole
  exact whole

theorem whole_before_readout (fetch : Bool) :
    (⟨compiler.obj (NamePassingGeneratedOperationalPresentation.rootDeclaration fetch).domain,
      compiler.obj NamePassingGeneratedOperationalPresentation.programs,
      compiler.map (classOf (NamePassingGeneratedOperationalPresentation.rootDeclaration fetch).before)⟩ :
        ArrowValue Target.{k}) = ⟨domain fetch,ordinary.termObject,before fetch⟩ := by
  have whole := functor_complete_readout NamePassingGeneratedOperationalCategory.nativeMeanings
    NamePassingGeneratedOperationalCategory.native_all_seven_diagrams
      (NamePassingGeneratedOperationalPresentation.rootDeclaration fetch).before
  have actual := NamePassingGeneratedOperationalCategory.nativeMeanings.evaluate_base_arrow
    (NamePassingGeneratedOperationalPresentation.staticInclusion.functor.map
      (classOf (ClosedPresentation.SchemaExpressions.expression
        NamePassingGeneratedOperationalPresentation.sourceBinding
          (NamePassingGeneratedOperationalPresentation.rootBefore fetch))))
  exact (Option.some.inj (whole.symm.trans actual)).trans (static_before_readout fetch)

theorem whole_after_readout (fetch : Bool) :
    (⟨compiler.obj (NamePassingGeneratedOperationalPresentation.rootDeclaration fetch).domain,
      compiler.obj NamePassingGeneratedOperationalPresentation.programs,
      compiler.map (classOf (NamePassingGeneratedOperationalPresentation.rootDeclaration fetch).after)⟩ :
        ArrowValue Target.{k}) = ⟨domain fetch,ordinary.termObject,after fetch⟩ := by
  have whole := functor_complete_readout NamePassingGeneratedOperationalCategory.nativeMeanings
    NamePassingGeneratedOperationalCategory.native_all_seven_diagrams
      (NamePassingGeneratedOperationalPresentation.rootDeclaration fetch).after
  have actual := NamePassingGeneratedOperationalCategory.nativeMeanings.evaluate_base_arrow
    (NamePassingGeneratedOperationalPresentation.staticInclusion.functor.map
      (classOf (ClosedPresentation.SchemaExpressions.expression
        NamePassingGeneratedOperationalPresentation.sourceBinding
          (NamePassingGeneratedOperationalPresentation.rootAfter fetch))))
  exact (Option.some.inj (whole.symm.trans actual)).trans (static_after_readout fetch)

def betaBody : domain.{k} false ⟶ ordinary.boundBodyObject :=
  snd (ordinary.names ⊗ 𝟙_ Target)
    (((ordinary.names ⊗ 𝟙_ Target) ⟶[Target] ordinary.termObject) ⊗ 𝟙_ Target) ≫
      fst _ _ ≫ boundValue ordinary

def betaArgument : domain.{k} false ⟶ ordinary.names :=
  fst (ordinary.names ⊗ 𝟙_ Target)
    (((ordinary.names ⊗ 𝟙_ Target) ⟶[Target] ordinary.termObject) ⊗ 𝟙_ Target) ≫ fst _ _

def betaInput : domain.{k} false ⟶ NamePassingGeneratedOperational.betaDomain :=
  lift betaBody betaArgument

def fetchName : domain.{k} true ⟶ ordinary.names :=
  fst (ordinary.names ⊗ (ordinary.termObject ⊗ 𝟙_ Target)) (𝟙_ Target) ≫ fst _ _

def fetchStored : domain.{k} true ⟶ ordinary.termObject :=
  fst (ordinary.names ⊗ (ordinary.termObject ⊗ 𝟙_ Target)) (𝟙_ Target) ≫
    snd ordinary.names (ordinary.termObject ⊗ 𝟙_ Target) ≫ fst _ _

def fetchInput : domain.{k} true ⟶ NamePassingGeneratedOperational.fetchDomain :=
  lift fetchName fetchStored

theorem beta_before : before.{k} false = betaInput ≫ NamePassingGeneratedOperational.betaSource := by
  unfold before Model.generic
  erw [beta_before_value]
  simp only [betaInput, NamePassingGeneratedOperational.betaSource, comp_lift_assoc, lift_fst_assoc,
    lift_snd, betaBody, Category.assoc]
  rfl

theorem beta_after : after.{k} false = betaInput ≫ NamePassingGeneratedOperational.betaTarget := by
  unfold after Model.generic
  erw [beta_after_value]
  change NamePassingContinuationOperations.call betaBody betaArgument = _
  simp only [betaInput, NamePassingGeneratedOperational.betaTarget,
    NamePassingContinuationOperations.call, comp_lift_assoc, lift_fst, lift_snd]

theorem fetch_before : before.{k} true = fetchInput ≫ NamePassingGeneratedOperational.fetchSource := by
  unfold before Model.generic
  erw [fetch_before_value]
  change lift fetchName (lift fetchStored (fetchName ≫ ordinary.reference)) ≫ ordinary.carrier = _
  simp only [fetchInput, NamePassingGeneratedOperational.fetchSource, comp_lift_assoc, comp_lift,
    lift_fst, lift_snd, lift_fst_assoc]

theorem fetch_after : after.{k} true = fetchInput ≫ snd ordinary.names ordinary.termObject := by
  unfold after Model.generic
  erw [fetch_after_value]
  change fetchStored = _
  simp only [fetchInput, lift_snd]

def firing : (fetch : Bool) → domain.{k} fetch ⟶ NamePassingGeneratedOperational.continuations
  | false => betaInput ≫ NamePassingGeneratedOperational.beta
  | true => fetchInput ≫ NamePassingGeneratedOperational.fetch

theorem firing_before (fetch : Bool) : firing.{k} fetch ≫
    NamePassingGeneratedOperational.functionEndpoint false = before fetch := by
  simp only [NamePassingGeneratedOperational.functionEndpoint, NamePassingGeneratedOperational.endpoint,
    Bool.false_eq_true, ↓reduceIte]
  cases fetch with
  | false => rw [firing, Category.assoc, NamePassingGeneratedOperational.beta_source, ← beta_before]
  | true => rw [firing, Category.assoc, NamePassingGeneratedOperational.fetch_source, ← fetch_before]

theorem firing_after (fetch : Bool) : firing.{k} fetch ≫
    NamePassingGeneratedOperational.functionEndpoint true = after fetch := by
  simp only [NamePassingGeneratedOperational.functionEndpoint, NamePassingGeneratedOperational.endpoint, ↓reduceIte]
  cases fetch with
  | false => rw [firing, Category.assoc, NamePassingGeneratedOperational.beta_target, ← beta_after]
  | true => rw [firing, Category.assoc, NamePassingGeneratedOperational.fetch_target, ← fetch_after]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalRootReadout
