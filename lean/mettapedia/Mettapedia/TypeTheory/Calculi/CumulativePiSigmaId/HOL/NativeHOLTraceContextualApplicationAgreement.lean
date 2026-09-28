import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceMixedTermSemantics
import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceContextualBridge

/-!
# Hosted HOL application through native dependent application

The HOL object interpretation and the native contextual interpretation use
the same trace product at constant codomains. Thus a native application of
hosted object terms is independently justified by the mixed dependent-term
application constructor and has exactly the source HOL trace value.

This is a comparison on the shared simple-type fragment, not uniqueness of
all denotations or an interpretation of genuinely varying dependent fibres.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceContextualApplicationAgreement

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (Extension)
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceTermInterpretation
open ZFSetUniformListTraceContextualBridge

universe u

private theorem castSection_symm_cast {Gamma : Type (u + 1)}
    {first second : ZFSetContextualInterpretation.SetFamily Gamma}
    (equal : first = second)
    (value : ZFSetContextualInterpretation.Section first) :
    NativeTraceDisplayedSubstitution.castSection equal.symm
      (NativeTraceDisplayedSubstitution.castSection equal value) = value := by
  cases equal
  rfl

/-- The mixed judgment conservatively contains every denotation from the
native lambda/application fragment, on the identical family and section. -/
theorem lambda_fragment_is_mixed (a : ZFSet.{u}) {n : Nat}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    {term : NativeTraceLambdaSemantics.Tm n}
    {family : ZFSetContextualInterpretation.SetFamily context.Environment}
    {value : ZFSetContextualInterpretation.Section family}
    (meaning : NativeTraceLambdaSemantics.Denotes context term family value) :
    NativeHOLTraceMixedTermSemantics.Denotes a context term.erase family value := by
  induction meaning with
  | var context index =>
      exact NativeHOLTraceMixedTermSemantics.Denotes.variable context index
  | lam bodyMeaning bodyInduction =>
      exact NativeHOLTraceMixedTermSemantics.Denotes.abstraction bodyInduction
  | app functionMeaning argumentMeaning functionInduction argumentInduction =>
      exact NativeHOLTraceMixedTermSemantics.Denotes.application
        functionInduction argumentInduction

/-- An application of two displayed HOL objects is also a native dependent
application. The latter is built with `Denotes.application`, while the former
supplies only the independently represented leaves. -/
theorem object_application_is_native {a : ZFSet.{u}} {n : Nat}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    {A B : HOL.Ty BaseSort} {function argument : Tower.Tm n}
    {functionValue : context.Environment → Value a (.arr A B)}
    {argumentValue : context.Environment → Value a A}
    (functionMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      function functionValue)
    (argumentMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      argument argumentValue) :
    NativeHOLTraceMixedTermSemantics.Denotes a context (.app function argument)
      (NativeHOLTraceDisplayedTerms.typeFamily a context B)
      (fun environment => app (functionValue environment) (argumentValue environment)) := by
  have functionObject := NativeHOLTraceMixedTermSemantics.Denotes.object functionMeaning
  have argumentObject := NativeHOLTraceMixedTermSemantics.Denotes.object argumentMeaning
  have functionNative := functionObject.cast_family
    (arrow_family_eq_piFamily a A B)
  have applicationNative := NativeHOLTraceMixedTermSemantics.Denotes.application
    (domain := NativeHOLTraceDisplayedTerms.typeFamily a context A)
    (codomain := fun _ : Extension
      (NativeHOLTraceDisplayedTerms.typeFamily a context A) => typeCode a B)
    functionNative argumentObject
  apply applicationNative.change_value
  funext environment
  change ZFSetTraceContextual.app
    (NativeTraceDisplayedSubstitution.castSection
      (arrow_family_eq_piFamily a A B) functionValue)
    argumentValue environment = _
  simp only [NativeTraceDisplayedSubstitution.castSection]
  rw [toContext_section a A B functionValue]
  exact app_agreement a A B environment (functionValue environment)
    (argumentValue environment)

/-- HOL abstraction is likewise the native dependent abstraction at a
constant domain and codomain, after the proved family-code identification. -/
theorem object_abstraction_is_native {a : ZFSet.{u}} {n : Nat}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    {A B : HOL.Ty BaseSort} {body : Tower.Tm (n + 1)}
    {bodyValue : (context.snoc
      (NativeHOLTraceDisplayedTerms.typeFamily a context A)).Environment → Value a B}
    (bodyMeaning : NativeHOLTraceDisplayedTerms.Denotes a
      (context.snoc (NativeHOLTraceDisplayedTerms.typeFamily a context A))
      body bodyValue) :
    NativeHOLTraceMixedTermSemantics.Denotes a context (.lam body)
      (NativeHOLTraceDisplayedTerms.typeFamily a context (.arr A B))
      (fun environment => lam (fun x => bodyValue ⟨environment, x⟩)) := by
  have bodyObject := NativeHOLTraceMixedTermSemantics.Denotes.object bodyMeaning
  have nativeLambda := NativeHOLTraceMixedTermSemantics.Denotes.abstraction bodyObject
  let equal := arrow_family_eq_piFamily (Γ := context.Environment) a A B
  let source : context.Environment → Value a (.arr A B) :=
    fun environment => lam (fun x => bodyValue ⟨environment, x⟩)
  have forward : NativeTraceDisplayedSubstitution.castSection equal source =
      ZFSetTraceContextual.lam bodyValue := by
    funext environment
    calc
      NativeTraceDisplayedSubstitution.castSection equal source environment =
          toContext a A B environment (source environment) :=
        congrFun (toContext_section a A B source) environment
      _ = ZFSetTraceContextual.lam bodyValue environment :=
        lam_agreement a A B
          (fun environment x => bodyValue ⟨environment, x⟩) environment
  have casted := nativeLambda.cast_family equal.symm
  apply casted.change_value
  change NativeTraceDisplayedSubstitution.castSection equal.symm
    (ZFSetTraceContextual.lam bodyValue) = source
  rw [← forward]
  exact castSection_symm_cast equal source

/-- A constant-bearing HOL body and an independently denoted argument retain
native beta semantics when assembled as an actual lambda/application redex.
The resulting section is also the source HOL beta value. -/
theorem object_beta_is_native {a : ZFSet.{u}} {n : Nat}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    {A B : HOL.Ty BaseSort} {body : Tower.Tm (n + 1)}
    {argument : Tower.Tm n}
    {bodyValue : (context.snoc
      (NativeHOLTraceDisplayedTerms.typeFamily a context A)).Environment → Value a B}
    {argumentValue : context.Environment → Value a A}
    (bodyMeaning : NativeHOLTraceDisplayedTerms.Denotes a
      (context.snoc (NativeHOLTraceDisplayedTerms.typeFamily a context A))
      body bodyValue)
    (argumentMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      argument argumentValue) :
    NativeHOLTraceMixedTermSemantics.Denotes a context
      (.app (.lam body) argument)
      (NativeHOLTraceDisplayedTerms.typeFamily a context B)
      (fun environment => app
        (lam (fun x => bodyValue ⟨environment, x⟩))
        (argumentValue environment)) := by
  have bodyNative := NativeHOLTraceMixedTermSemantics.Denotes.object bodyMeaning
  have argumentNative := NativeHOLTraceMixedTermSemantics.Denotes.object argumentMeaning
  have applied := NativeHOLTraceMixedTermSemantics.Denotes.application
    (NativeHOLTraceMixedTermSemantics.Denotes.abstraction bodyNative)
    argumentNative
  apply applied.change_value
  funext environment
  calc
    ZFSetTraceContextual.app (ZFSetTraceContextual.lam bodyValue)
        argumentValue environment =
        bodyValue ⟨environment, argumentValue environment⟩ :=
      congrFun (ZFSetTraceContextual.app_lam bodyValue argumentValue) environment
    _ = app (lam (fun x => bodyValue ⟨environment, x⟩))
        (argumentValue environment) :=
      (app_lam (fun x : Value a A => bodyValue ⟨environment, x⟩)
        (argumentValue environment)).symm

/-- A represented HOL function and a represented HOL argument, independently
substituted into a mixed native context, meet at the native dependent
application constructor. This retains the exact compiled subterms and the
source trace value. -/
theorem represented_application_is_native {a : ZFSet.{u}}
    {gamma : HOL.Ctx BaseSort} {A B : HOL.Ty BaseSort}
    (sourceFunction : HOL.Term Symbol gamma (.arr A B))
    (sourceArgument : HOL.Term Symbol gamma A)
    {functionCode argumentCode : Tower.Tm gamma.length}
    (functionRepresented : HOLNaturalDeductionNativeTranslation.represent
      sourceFunction = some functionCode)
    (argumentRepresented : HOLNaturalDeductionNativeTranslation.represent
      sourceArgument = some argumentCode)
    {n : Nat} (context : NativeTraceLambdaSemantics.Context.{u} n)
    (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment →
      NativeHOLUniformListTraceRepresentation.Valuation a gamma)
    (components : ∀ {objectType : HOL.Ty BaseSort}
      (index : HOL.Var gamma objectType),
      NativeHOLTraceDisplayedTerms.Denotes a context
        (objects (FormationSensitiveHOLInterface.variableIndex index))
        (fun environment => valuation environment index)) :
    NativeHOLTraceMixedTermSemantics.Denotes a context
      (.app (Presentation.subst objects functionCode)
        (Presentation.subst objects argumentCode))
      (NativeHOLTraceDisplayedTerms.typeFamily a context B)
      (fun environment => interpret (.app sourceFunction sourceArgument)
        (valuation environment)) := by
  exact object_application_is_native
    (NativeHOLTraceDisplayedTerms.representation_square sourceFunction
      functionRepresented context objects valuation components)
    (NativeHOLTraceDisplayedTerms.representation_square sourceArgument
      argumentRepresented context objects valuation components)

/-- A represented source beta redex is assembled from native dependent
abstraction and application, including after an arbitrary displayed
substitution of its free source variables. The body and argument are
represented and interpreted independently; neither is required to be a
variable, a normal form, or a closed term. -/
theorem represented_beta_is_native {a : ZFSet.{u}}
    {gamma : HOL.Ctx BaseSort} {A B : HOL.Ty BaseSort}
    (sourceBody : HOL.Term Symbol (A :: gamma) B)
    (sourceArgument : HOL.Term Symbol gamma A)
    {bodyCode : Tower.Tm (gamma.length + 1)}
    {argumentCode : Tower.Tm gamma.length}
    (bodyRepresented : HOLNaturalDeductionNativeTranslation.represent
      sourceBody = some bodyCode)
    (argumentRepresented : HOLNaturalDeductionNativeTranslation.represent
      sourceArgument = some argumentCode)
    {n : Nat} (context : NativeTraceLambdaSemantics.Context.{u} n)
    (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment →
      NativeHOLUniformListTraceRepresentation.Valuation a gamma)
    (components : ∀ {objectType : HOL.Ty BaseSort}
      (index : HOL.Var gamma objectType),
      NativeHOLTraceDisplayedTerms.Denotes a context
        (objects (FormationSensitiveHOLInterface.variableIndex index))
        (fun environment => valuation environment index)) :
    NativeHOLTraceMixedTermSemantics.Denotes a context
      (.app (.lam (Presentation.subst (liftSub objects) bodyCode))
        (Presentation.subst objects argumentCode))
      (NativeHOLTraceDisplayedTerms.typeFamily a context B)
      (fun environment => interpret
        (HOL.Term.app (HOL.Term.lam sourceBody) sourceArgument)
        (valuation environment)) := by
  let extended := context.snoc (NativeHOLTraceDisplayedTerms.typeFamily a context A)
  let extendedValuation : extended.Environment →
      NativeHOLUniformListTraceRepresentation.Valuation a (A :: gamma) :=
    fun point => extend (valuation point.1) point.2
  have extendedComponents : ∀ {objectType : HOL.Ty BaseSort}
      (index : HOL.Var (A :: gamma) objectType),
      NativeHOLTraceDisplayedTerms.Denotes a extended
        (liftSub objects (FormationSensitiveHOLInterface.variableIndex index))
        (fun environment => extendedValuation environment index) := by
    intro objectType index
    cases index with
    | vz =>
        exact NativeHOLTraceDisplayedTerms.Denotes.variable 0
          (NativeTraceLambdaSemantics.Denotes.var extended 0)
    | vs prior =>
        exact (components prior).weaken
          (NativeHOLTraceDisplayedTerms.typeFamily a context A)
  have bodyMeaning := NativeHOLTraceDisplayedTerms.representation_square
    sourceBody bodyRepresented extended (liftSub objects)
      extendedValuation extendedComponents
  have argumentMeaning := NativeHOLTraceDisplayedTerms.representation_square
    sourceArgument argumentRepresented context objects valuation components
  change NativeHOLTraceDisplayedTerms.Denotes a extended
    (Presentation.subst (liftSub objects) bodyCode)
    (fun point => interpret sourceBody (extend (valuation point.1) point.2))
    at bodyMeaning
  have native : NativeHOLTraceMixedTermSemantics.Denotes a context
      (.app (.lam (Presentation.subst (liftSub objects) bodyCode))
        (Presentation.subst objects argumentCode))
      (NativeHOLTraceDisplayedTerms.typeFamily a context B)
      (fun environment => app
        (lam (fun x => interpret sourceBody (extend (valuation environment) x)))
        (interpret sourceArgument (valuation environment))) :=
    object_beta_is_native (a := a) (context := context) (A := A) (B := B)
      (body := Presentation.subst (liftSub objects) bodyCode)
      (argument := Presentation.subst objects argumentCode)
      (bodyValue := fun point => interpret sourceBody
        (extend (valuation point.1) point.2))
      (argumentValue := fun environment => interpret sourceArgument
        (valuation environment))
      bodyMeaning argumentMeaning
  simpa only [interpret_app_lam] using native

namespace Controls

/-- The actual `length nil` HOL term is interpreted by native dependent
application rather than treated only as a monolithic object leaf. -/
theorem length_nil_native (a : ZFSet.{u}) :
    NativeHOLTraceMixedTermSemantics.Denotes a NativeTraceLambdaSemantics.Context.nil
      (.app (.const (FormationSensitiveHOLUniformList.symbolName Symbol.length))
        (.const (FormationSensitiveHOLUniformList.symbolName Symbol.nil)))
      (NativeHOLTraceDisplayedTerms.typeFamily a NativeTraceLambdaSemantics.Context.nil
        count)
      (fun _ => app (constant a Symbol.length) (constant a Symbol.nil)) :=
  object_application_is_native
    (NativeHOLTraceDisplayedTerms.Denotes.constant
      (a := a) (context := NativeTraceLambdaSemantics.Context.nil) Symbol.length)
    (NativeHOLTraceDisplayedTerms.Denotes.constant
      (a := a) (context := NativeTraceLambdaSemantics.Context.nil) Symbol.nil)

end Controls

#print axioms object_application_is_native
#print axioms object_abstraction_is_native
#print axioms object_beta_is_native
#print axioms represented_application_is_native
#print axioms represented_beta_is_native
#print axioms lambda_fragment_is_mixed
#print axioms Controls.length_nil_native

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceContextualApplicationAgreement
