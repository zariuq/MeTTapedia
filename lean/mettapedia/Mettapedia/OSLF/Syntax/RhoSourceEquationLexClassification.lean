import Mettapedia.OSLF.Syntax.CartesianModelLexTargetEquivalence
import Mettapedia.OSLF.Syntax.RhoEquationContextRepresentability
import Mettapedia.OSLF.Syntax.RhoFreePresheafEvents

/-!
# The finite-limit classifier over rho's actual source equations

The authored rho source has a proper equation quotient: parallel ACU and
name reflection both change the context theory. We instantiate the relative
finite-limit construction on that quotient category and compare its program
object with the existing equation-class state presheaf. This identifies the
state carrier used by the operational graph without claiming that the
finite-limit classifier alone contains the event graph or chosen closure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSourceEquationLexClassification

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents

/-- Contexts and substitutions in the complete Chapter 7 source equation
presentation, including the name-reflection equation. -/
noncomputable abbrev SourceContexts : Type :=
  ContextObject
    ((BindingEquationQuotientModel.algebra rhoSourceE).substitution.toClone)

private instance : HasFiniteProducts SourceContexts :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- The distinguished process/program context in the equation quotient. -/
noncomputable def program : SourceContexts :=
  ContextObject.ofList _ [Srt.pr]

/-- The complete source-equation context theory has the checked relative
finite-limit universal property in each small finitely complete target. -/
noncomputable def sourceLexEquivalence
    (D : Type) [SmallCategory D] [HasFiniteLimits D] :
    LeftExactTargetInterpretations SourceContexts D ≌
      CartesianTargetInterpretations SourceContexts D :=
  cartesianTargetLexEquivalence SourceContexts D

/-- The actual equation-class process presheaf is the pulled-back Yoneda
representation of the program object in the source equation context
category. The comparison acts on every open context and substitution. -/
noncomputable def sourceStatesAsProgramIso :
    (cloneContextToSyntactic sig).op ⋙
        termQPresheaf rhoSourceE Srt.pr ≅
      (termCloneToSemanticContextFunctor sig ⋙
          quotientContextFunctor rhoSourceE).op ⋙
        yoneda.obj program := by
  exact termQAsPulledYonedaIso rhoSourceE Srt.pr

/-- Yoneda's authored model of the equation quotient, now living in a
nontrivial presheaf target. -/
noncomputable def sourceYonedaModel :
    CartesianTargetInterpretations SourceContexts
      (SourceContextsᵒᵖ ⥤ Type) :=
  ⟨yoneda, by
    change PreservesFiniteProducts
      (yoneda : SourceContexts ⥤ SourceContextsᵒᵖ ⥤ Type)
    infer_instance⟩

/-- The pointwise extension of that authored model to finite
presentations. -/
noncomputable def sourceYonedaExtension :
    LeftExactTargetInterpretations SourceContexts
      (SourceContextsᵒᵖ ⥤ Type) :=
  extendPresheafAuthoredModel SourceContexts SourceContexts sourceYonedaModel

/-- Full functorial classification in the actual presheaf target, including
maps between interpretations and the equivalence coherence. -/
noncomputable def sourcePresheafLexEquivalence :
    LeftExactTargetInterpretations SourceContexts
        (SourceContextsᵒᵖ ⥤ Type) ≌
      CartesianTargetInterpretations SourceContexts
        (SourceContextsᵒᵖ ⥤ Type) :=
  cartesianPresheafLexEquivalence SourceContexts SourceContexts

/-- The explicit source-equation extension agrees with the inverse of the
full interpretation equivalence, not merely at its program object. -/
noncomputable def sourceYonedaInverseIso :
    sourceYonedaExtension ≅
      sourcePresheafLexEquivalence.inverse.obj sourceYonedaModel := by
  let E := sourcePresheafLexEquivalence
  let onContexts : E.functor.obj sourceYonedaExtension ≅
      sourceYonedaModel :=
    (CartesianTargetInterpretation SourceContexts
      (SourceContextsᵒᵖ ⥤ Type)).isoMk
        (extendPresheafAuthoredModelRestrictionIso
          SourceContexts SourceContexts sourceYonedaModel)
  exact (E.unitIso.app sourceYonedaExtension) ≪≫
    E.inverse.mapIso onContexts

/-- The generated interpretation of the program presentation is the same
representable presheaf that models authored equation-class programs. -/
noncomputable def generatedProgramIso :
    sourceYonedaExtension.1.obj
        ((authoredContext SourceContexts).obj program) ≅
      yoneda.obj program :=
  (extendPresheafAuthoredModelRestrictionIso
    SourceContexts SourceContexts sourceYonedaModel).app program

/-- Comparing the semantic program object with the operational state
presheaf after both are pulled back to intrinsic clone contexts. -/
noncomputable def generatedProgramAsOperationalStatesIso :
    (cloneContextToSyntactic sig).op ⋙
        termQPresheaf rhoSourceE Srt.pr ≅
      (termCloneToSemanticContextFunctor sig ⋙
          quotientContextFunctor rhoSourceE).op ⋙
        sourceYonedaExtension.1.obj
          ((authoredContext SourceContexts).obj program) :=
  sourceStatesAsProgramIso ≪≫
    Functor.isoWhiskerLeft
      (termCloneToSemanticContextFunctor sig ⋙
        quotientContextFunctor rhoSourceE).op
      generatedProgramIso.symm

end Mettapedia.OSLF.Binding.RhoSourceEquationLexClassification
