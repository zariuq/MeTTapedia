import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceMixedTermSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceBetaInstantiation

/-!
# Componentwise substitution into the existing mixed trace judgment

The substitution contract concerns individual variables, not preservation of
whole terms. HOL object derivations substitute into the existing mixed
judgment: arbitrary mixed replacements need not retain a source HOL type
index. Constant HOL products and their operations agree with the contextual
trace products by literal family equality and value equality.

The beta result retains the supplied body and argument at their shared domain.
It does not assert preservation for arbitrary raw denotation derivations.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceMixedSubstitution

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section Extension)
open NativeTraceLambdaSemantics (Context)
open NativeTraceContextMorphisms NativeTraceDisplayedSubstitution
open NativeHOLTraceDisplayedTerms (typeFamily)
open NativeHOLTraceMixedTermSemantics (Denotes)
open ZFSetUniformListTraceTypeInterpretation (Value typeCode)

universe u

theorem castSection_value {Gamma : Type (u + 1)} {first second : SetFamily Gamma}
    (equal : first = second) (value : Section first) (point : Gamma) :
    (castSection equal value point).1 = (value point).1 := by
  cases equal
  rfl

theorem castSection_inverse {Gamma : Type (u + 1)} {first second : SetFamily Gamma}
    (equal : first = second) (value : Section first) :
    castSection equal.symm (castSection equal value) = value := by
  cases equal
  rfl

theorem hol_product_family (a : ZFSet.{u}) {n : Nat} (context : Context.{u} n)
    (domain codomain : HOL.Ty BaseSort) :
    ZFSetTraceContextual.piFamily (typeFamily a context domain)
      (typeFamily a (context.snoc (typeFamily a context domain)) codomain) =
      typeFamily a context (.arr domain codomain) := by
  funext environment
  apply ZFSetTraceProducts.tracePiSet_congr
  intro value member
  exact ZFSetContextualInterpretation.totalFamily_at _ _ ⟨value, member⟩

theorem hol_application_agreement {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {domain codomain : HOL.Ty BaseSort}
    (function : context.Environment → Value a (.arr domain codomain))
    (argument : context.Environment → Value a domain) :
    ZFSetTraceContextual.app
        (castSection (hol_product_family a context domain codomain).symm function) argument =
      fun environment => ZFSetUniformListTraceTypeInterpretation.app
        (function environment) (argument environment) := by
  funext environment
  apply Subtype.ext
  exact (ZFSetTraceContextual.piDecode_value _ _ environment _ _).trans
    (congrArg (fun function => ZFSetTraceProducts.traceApp function (argument environment).1)
      (castSection_value _ function environment))

theorem hol_abstraction_agreement {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {domain codomain : HOL.Ty BaseSort}
    (body : (context.snoc (typeFamily a context domain)).Environment → Value a codomain) :
    castSection (hol_product_family a context domain codomain)
        (ZFSetTraceContextual.lam body) =
      fun environment => ZFSetUniformListTraceTypeInterpretation.lam
        (fun argument => body ⟨environment, argument⟩) := by
  funext environment
  apply (ZFSetTraceProducts.tracePiEquiv (typeCode a domain) (fun _ => typeCode a codomain)).injective
  funext argument
  change ZFSetUniformListTraceTypeInterpretation.app _ argument =
    ZFSetUniformListTraceTypeInterpretation.app _ argument
  rw [ZFSetUniformListTraceTypeInterpretation.app_lam]
  have agreement := hol_application_agreement
    (castSection (hol_product_family a context domain codomain)
      (ZFSetTraceContextual.lam body)) (fun _ => argument)
  rw [castSection_inverse] at agreement
  exact (congrFun agreement environment).symm.trans
    (congrFun (ZFSetTraceContextual.app_lam body (fun _ => argument)) environment)

/-- Only primitive variable components are required. -/
abbrev Components (a : ZFSet.{u}) {n m : Nat}
    (source : Context.{u} n) (target : Context.{u} m)
    (morphism : Morphism source target) (sigma : Sub Tower.Head n m) : Prop :=
  ∀ index, Denotes a target (sigma index)
    (morphism.reindexFamily (source.family index))
    (morphism.reindexSection (source.projection index))

theorem components_lift {a : ZFSet.{u}} {n m : Nat}
    {source : Context.{u} n} {target : Context.{u} m}
    {morphism : Morphism source target} {sigma : Sub Tower.Head n m}
    (components : Components a source target morphism sigma)
    (family : SetFamily source.Environment) :
    Components a (source.snoc family) (target.snoc (morphism.reindexFamily family))
      (morphism.lift family) (liftSub sigma) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · exact Denotes.variable _ 0
  · exact (components prior).weaken (morphism.reindexFamily family)

theorem variable_component {a : ZFSet.{u}} {n m : Nat}
    {source : Context.{u} n} {target : Context.{u} m}
    {morphism : Morphism source target} {sigma : Sub Tower.Head n m}
    (components : Components a source target morphism sigma)
    {index : Fin n} {family : SetFamily source.Environment} {value : Section family}
    (meaning : NativeTraceLambdaSemantics.Denotes source (.var index) family value) :
    Denotes a target (sigma index) (morphism.reindexFamily family)
      (morphism.reindexSection value) := by
  cases meaning
  exact components index

/-- The output stays in the existing mixed judgment, not a newly introduced
semantic carrier or an unjustified object-only closure assertion. -/
theorem object_substitute {a : ZFSet.{u}} {n : Nat} {source : Context.{u} n}
    {type : HOL.Ty BaseSort} {term : Tower.Tm n}
    {value : source.Environment → Value a type}
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a source term value)
    {m : Nat} {target : Context.{u} m} {morphism : Morphism source target}
    {sigma : Sub Tower.Head n m} (components : Components a source target morphism sigma) :
    Denotes a target (subst sigma term) (typeFamily a target type)
      (fun environment => value (morphism.environment environment)) := by
  induction meaning generalizing m with
  | «variable» index variableMeaning => exact variable_component components variableMeaning
  | constant symbol => exact .object (.constant symbol)
  | implication => exact .object .implication
  | universal type =>
      simpa only [subst, FormationSensitiveHOLInterface.typeAt_subst] using
        (Denotes.object (NativeHOLTraceDisplayedTerms.Denotes.universal
          (a := a) (context := target) type))
  | equality type =>
      simpa only [subst, FormationSensitiveHOLInterface.typeAt_subst] using
        (Denotes.object (NativeHOLTraceDisplayedTerms.Denotes.equality
          (a := a) (context := target) type))
  | @application n context domain codomain function argument functionValue argumentValue
      functionMeaning argumentMeaning functionInduction argumentInduction =>
      have functionMoved := (functionInduction components).cast_family
        (hol_product_family a target domain codomain).symm
      exact (Denotes.application functionMoved (argumentInduction components)).change_value
        (hol_application_agreement _ _)
  | @abstraction n context domain codomain body bodyValue bodyMeaning inductionHypothesis =>
      have moved := inductionHypothesis (components_lift components (typeFamily a context domain))
      exact ((Denotes.abstraction moved).cast_family
        (hol_product_family a target domain codomain)).change_value
          (hol_abstraction_agreement _)

theorem substitute {a : ZFSet.{u}} {n : Nat} {source : Context.{u} n}
    {term : Tower.Tm n} {family : SetFamily source.Environment} {value : Section family}
    (meaning : Denotes a source term family value)
    {m : Nat} {target : Context.{u} m} {morphism : Morphism source target}
    {sigma : Sub Tower.Head n m} (components : Components a source target morphism sigma) :
    Denotes a target (subst sigma term) (morphism.reindexFamily family)
      (morphism.reindexSection value) := by
  induction meaning generalizing m with
  | «variable» context index => exact components index
  | object objectMeaning => exact object_substitute objectMeaning components
  | abstraction bodyMeaning inductionHypothesis =>
      exact .abstraction (inductionHypothesis (components_lift components _))
  | @application n context domain codomain function argument functionValue argumentValue
      functionMeaning argumentMeaning functionInduction argumentInduction =>
      have functionMoved := functionInduction components
      have functionForApplication :
          Denotes a target (subst sigma function)
            (ZFSetTraceContextual.piFamily (morphism.reindexFamily domain)
              (codomain ∘ (morphism.lift domain).environment))
            (morphism.reindexSection functionValue) :=
        functionMoved.cast_family (by rfl)
      exact .application functionForApplication (argumentInduction components)

theorem components_identity (a : ZFSet.{u}) {n : Nat} (context : Context.{u} n) :
    Components a context context (Morphism.identity context) ids :=
  fun index => .variable context index

theorem components_comp {a : ZFSet.{u}} {n m k : Nat}
    {source : Context.{u} n} {middle : Context.{u} m} {target : Context.{u} k}
    {first : Morphism source middle} {second : Morphism middle target}
    {sigma : Sub Tower.Head n m} {tau : Sub Tower.Head m k}
    (firstComponents : Components a source middle first sigma)
    (secondComponents : Components a middle target second tau) :
    Components a source target (first.comp second) (subComp tau sigma) :=
  fun index => substitute (firstComponents index) secondComponents

theorem argument_components {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {domain : SetFamily context.Environment} {argument : Tower.Tm n}
    {argumentValue : Section domain} (meaning : Denotes a context argument domain argumentValue) :
    Components a (context.snoc domain) context
      (NativeTraceBetaInstantiation.argumentMorphism context argumentValue) (subst0 argument) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · exact meaning
  · exact .variable context prior

theorem instantiate {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {domain : SetFamily context.Environment} {codomain : SetFamily (Extension domain)}
    {body : Tower.Tm (n + 1)} {argument : Tower.Tm n}
    {bodyValue : Section codomain} {argumentValue : Section domain}
    (bodyMeaning : Denotes a (context.snoc domain) body codomain bodyValue)
    (argumentMeaning : Denotes a context argument domain argumentValue) :
    Denotes a context (inst0 argument body)
      (fun point => codomain ⟨point, argumentValue point⟩)
      (fun point => bodyValue ⟨point, argumentValue point⟩) :=
  substitute bodyMeaning (argument_components argumentMeaning)

theorem beta_square {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {domain : SetFamily context.Environment} {codomain : SetFamily (Extension domain)}
    {body : Tower.Tm (n + 1)} {argument : Tower.Tm n}
    {bodyValue : Section codomain} {argumentValue : Section domain}
    (bodyMeaning : Denotes a (context.snoc domain) body codomain bodyValue)
    (argumentMeaning : Denotes a context argument domain argumentValue)
    (headEquality : Tower.Head → Tower.Head → Prop) (root : RootComputation Tower.Head) :
    Step headEquality (.app (.lam body) argument) (inst0 argument body) root ∧
      Denotes a context (.app (.lam body) argument)
        (fun point => codomain ⟨point, argumentValue point⟩)
        (fun point => bodyValue ⟨point, argumentValue point⟩) ∧
      Denotes a context (inst0 argument body)
        (fun point => codomain ⟨point, argumentValue point⟩)
        (fun point => bodyValue ⟨point, argumentValue point⟩) := by
  exact ⟨.betaPi body argument,
    (Denotes.application (.abstraction bodyMeaning) argumentMeaning).change_value
      (ZFSetTraceContextual.app_lam bodyValue argumentValue),
    instantiate bodyMeaning argumentMeaning⟩

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceMixedSubstitution
