import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalPresentation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalCategory
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedConstructorReadout
import Mettapedia.OSLF.Syntax.BindingClosedGeneratedModelNormalization

/-!
# Complete source constructor comparisons along the generated compiler

The actual source binding data is recovered from its constructor inclusion.
Its native constructor arrows agree with independently authored expressions.
The compiler's complete static restriction then earns their five whole CPS
readings. The domain comparisons include padded unit contexts and complete
function objects, using the actual normalization isomorphisms. Strict native
choice preservation is not assumed for an arbitrary closed functor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory FunctorNormalization Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus

universe k

abbrev Source := NamePassingGeneratedOperationalPresentation.CategoryGuest.{k}
abbrev Target := NamePassingGeneratedOperationalCategory.Target.{k}

abbrev constructors : Object (ClosedPresentation.signature.{k} NamePassing.Presentation.signature) ⥤ Source.{k} :=
  NamePassingGeneratedOperationalPresentation.constructors.{k}
instance constructors_finite : PreservesFiniteLimits constructors.{k} :=
  NamePassingGeneratedOperationalPresentation.constructors_finite
instance constructors_closed : MonoidalClosedFunctor constructors.{k} :=
  NamePassingGeneratedOperationalPresentation.constructors_closed

def sourceOperations := ClosedPresentation.GeneratedModel.operations
  (binding := NamePassing.Presentation.signature) constructors.{k}
def sourceNative := normalizedFunctor
  (signature := ClosedPresentation.signature.{k} NamePassing.Presentation.signature) constructors.{k}
def compiler : Source.{k} ⥤ Target.{k} := NamePassingGeneratedOperationalCategory.nativeInterpretation.{k}.functor
def targetOperations := NamePassingGeneratedStatic.operations
  NamePassingGeneratedOperationalCategory.binding.{k}

theorem complete_constructor_restriction : constructors.{k} ⋙ compiler = targetOperations.interpretation.functor := by
  change (NamePassingGeneratedOperationalCategory.staticInclusion.functor ⋙
    (Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Presentation.baseMap
      NamePassingGeneratedOperationalCategory.vertex).functor) ⋙
      NamePassingGeneratedOperationalCategory.nativeInterpretation.functor = _
  rw [Functor.assoc, NamePassingGeneratedOperationalCategory.complete_static_restriction]
  exact NamePassingGeneratedStatic.complete_restriction
    NamePassingGeneratedOperationalCategory.binding BindingClosedGeneratedOperationalModel.structural_schemas

def sourceValue (operator : NamePassing.Presentation.Operator .tm) : ArrowValue Source.{k} :=
  ⟨sourceNative.obj (NamePassingBindingClosedConstructorExpressions.domain operator),
    sourceNative.obj NamePassingBindingClosedConstructorExpressions.terms,
    sourceNative.map (classOf (NamePassingBindingClosedConstructorExpressions.expression operator))⟩

theorem whole_source_constructor (operator : NamePassing.Presentation.Operator .tm) :
    sourceValue.{k} operator =
      ⟨NamePassingBindingClosedConstructorReadout.domain sourceOperations operator,
        NamePassingBindingPrimitiveOperations.terms sourceOperations,
        NamePassingBindingClosedConstructorReadout.arrow sourceOperations operator⟩ := by
  have whole := NamePassingBindingClosedConstructorReadout.complete_readout sourceOperations operator
  change (⟨(ClosedPresentation.GeneratedModel.operations
      (binding := NamePassing.Presentation.signature) constructors).interpretation.functor.obj _,
    (ClosedPresentation.GeneratedModel.operations
      (binding := NamePassing.Presentation.signature) constructors).interpretation.functor.obj _,
    (ClosedPresentation.GeneratedModel.operations
      (binding := NamePassing.Presentation.signature) constructors).interpretation.functor.map _⟩ : ArrowValue Source) = _ at whole
  rw [ClosedPresentation.GeneratedModel.interpretation_eq_normalized
    (binding := NamePassing.Presentation.signature)] at whole
  exact whole

def targetValue (operator : NamePassing.Presentation.Operator .tm) : ArrowValue Target.{k} :=
  ⟨NamePassingBindingClosedConstructorReadout.domain targetOperations operator,
    NamePassingBindingPrimitiveOperations.terms targetOperations,
    NamePassingBindingClosedConstructorReadout.arrow targetOperations operator⟩

theorem whole_target_constructor (operator : NamePassing.Presentation.Operator .tm) :
    (⟨compiler.obj (constructors.obj (NamePassingBindingClosedConstructorExpressions.domain operator)),
      compiler.obj (constructors.obj NamePassingBindingClosedConstructorExpressions.terms),
      compiler.map (constructors.map (classOf (NamePassingBindingClosedConstructorExpressions.expression operator)))⟩ :
        ArrowValue Target.{k}) = targetValue operator := by
  have whole := NamePassingBindingClosedConstructorReadout.complete_readout targetOperations operator
  rw [← complete_constructor_restriction] at whole
  exact whole

def domainComparison (operator : NamePassing.Presentation.Operator .tm) :
    compiler.obj (sourceValue.{k} operator).source ≅ (targetValue operator).source :=
  (compiler.mapIso (objectImage constructors (NamePassingBindingClosedConstructorExpressions.domain operator)).comparison).symm ≪≫
    eqToIso (congrArg ArrowValue.source (whole_target_constructor operator))

def programComparison (operator : NamePassing.Presentation.Operator .tm) :
    compiler.obj (sourceValue.{k} operator).target ≅ (targetValue operator).target :=
  (compiler.mapIso (objectImage constructors NamePassingBindingClosedConstructorExpressions.terms).comparison).symm ≪≫
    eqToIso (congrArg ArrowValue.target (whole_target_constructor operator))

private theorem mapped_normalized_square (operator : NamePassing.Presentation.Operator .tm) :
    compiler.map (objectImage constructors (NamePassingBindingClosedConstructorExpressions.domain operator)).comparison.hom ≫
      compiler.map (sourceValue.{k} operator).arrow ≫
        compiler.map (objectImage constructors NamePassingBindingClosedConstructorExpressions.terms).comparison.inv =
    compiler.map (constructors.map (classOf (NamePassingBindingClosedConstructorExpressions.expression operator))) := by
  have natural := (comparison constructors).hom.naturality
    (classOf (NamePassingBindingClosedConstructorExpressions.expression operator))
  have mapped := congrArg (compiler.map ·) natural
  rw [compiler.map_comp, compiler.map_comp] at mapped
  change compiler.map _ ≫ compiler.map (objectImage constructors
    NamePassingBindingClosedConstructorExpressions.terms).comparison.hom =
      compiler.map (objectImage constructors
        (NamePassingBindingClosedConstructorExpressions.domain operator)).comparison.hom ≫
          compiler.map (sourceValue operator).arrow at mapped
  rw [← Category.assoc, ← mapped, Category.assoc, ← compiler.map_comp,
    Iso.hom_inv_id, compiler.map_id, Category.comp_id]

private theorem transported_arrow {C : Type k} [Category.{k} C]
    {first last before after : C} (value : first ⟶ last) (reading : before ⟶ after)
    (same : (⟨first,last,value⟩ : ArrowValue C) = ⟨before,after,reading⟩) :
    eqToHom (congrArg ArrowValue.source same).symm ≫ value ≫
      eqToHom (congrArg ArrowValue.target same) = reading := by
  have sourceSame := congrArg ArrowValue.source same
  have targetSame := congrArg ArrowValue.target same
  dsimp at sourceSame targetSame
  subst before
  subst after
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using ArrowValue.arrow_injective same

theorem complete_compiled_constructor (operator : NamePassing.Presentation.Operator .tm) :
    (domainComparison.{k} operator).inv ≫ compiler.map (sourceValue operator).arrow ≫
      (programComparison operator).hom = (targetValue operator).arrow := by
  change (eqToHom (congrArg ArrowValue.source (whole_target_constructor operator)).symm ≫
    compiler.map (objectImage constructors (NamePassingBindingClosedConstructorExpressions.domain operator)).comparison.hom) ≫
      compiler.map (sourceValue operator).arrow ≫
        (compiler.map (objectImage constructors NamePassingBindingClosedConstructorExpressions.terms).comparison.inv ≫
          eqToHom (congrArg ArrowValue.target (whole_target_constructor operator))) = _
  have pasted := congrArg
    (fun arrow => eqToHom (congrArg ArrowValue.source (whole_target_constructor operator)).symm ≫
      arrow ≫ eqToHom (congrArg ArrowValue.target (whole_target_constructor operator)))
    (mapped_normalized_square operator)
  calc
    _ = eqToHom (congrArg ArrowValue.source (whole_target_constructor operator)).symm ≫
      compiler.map (constructors.map (classOf (NamePassingBindingClosedConstructorExpressions.expression operator))) ≫
        eqToHom (congrArg ArrowValue.target (whole_target_constructor operator)) := by
          simpa only [Category.assoc] using pasted
    _ = _ := transported_arrow _ _ (whole_target_constructor operator)

theorem reference_readout : (targetValue.{k} .reference).arrow =
    NamePassingGeneratedOperationalCategory.ordinary.reference :=
  NamePassingBindingPrimitiveOperations.generated_reference _

theorem abstraction_readout : (targetValue.{k} .abstraction).arrow =
    NamePassingGeneratedOperationalCategory.ordinary.abstraction :=
  NamePassingBindingPrimitiveOperations.generated_abstraction _

theorem application_readout : (targetValue.{k} .application).arrow =
    NamePassingGeneratedOperationalCategory.ordinary.application :=
  NamePassingBindingPrimitiveOperations.generated_application _

theorem definition_readout : (targetValue.{k} .definition).arrow =
    NamePassingGeneratedOperationalCategory.ordinary.definition :=
  NamePassingBindingPrimitiveOperations.generated_definition _

theorem carrier_readout : (targetValue.{k} .carrier).arrow =
    NamePassingGeneratedOperationalCategory.ordinary.carrier :=
  NamePassingBindingPrimitiveOperations.generated_carrier _

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorComparison
