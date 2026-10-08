import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualYoneda
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TypedContextualControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TypedQuotientModelControls

/-!
# Native dependent sections at actual typed substitutions

The telescope binds a type X and a function f : Pi x:X.X. Its native
function certificate satisfies eta while retaining a distinction between
the original raw codes. Beta computation and changes of dependent type
annotations are also interpreted as equations of native sections.

A separate telescope (X:U), (x:X), (y:X) admits a nonprojection substitution
selecting y for x. Decoding the native section recovers that actual selected
class. The tower's set model, under its explicit cofinal-inaccessibles
hypothesis, distinguishes the resulting x and y sections. The native
construction itself does not require that set-model hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.TypedNativePresheafControls

open _root_.CategoryTheory Opposite
open TypedEquality TypedEquality.Normalization
open TypedContextual TypedContextual.NativePresheaf
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation (interpretHead)

universe u

abbrev levels := TypedContextualControls.levels
abbrev qualification := TypedQuotientControls.qualification

/-- The profile's independently proved conservativity admits an actual
formed telescope in the stronger typed context category. -/
def admitContext (source : FormationSensitiveContextual.Context Tower.rules) :
    TypedContextual.Context Tower.rules :=
  ⟨source.arity, source.raw, FormationSensitiveTypedQuotient.contextFormed qualification source.formed⟩

def admitType {source : FormationSensitiveContextual.Context Tower.rules}
    (type : FormationSensitiveContextual.TypeOver source) : TypeOver (admitContext source) :=
  ⟨type.code, type.level, type.universeWitness,
    FormationSensitiveTypedQuotient.typeTyped qualification type⟩

def admitTerm {source : FormationSensitiveContextual.Context Tower.rules}
    {type : FormationSensitiveContextual.TypeOver source}
    (term : FormationSensitiveContextual.Term source type) :
    Term (admitContext source) (admitType type) :=
  ⟨term.code, FormationSensitiveTypedQuotient.termTyped qualification term⟩

def admitArrow {source target : FormationSensitiveContextual.Context Tower.rules}
    (morphism : source ⟶ target) : admitContext source ⟶ admitContext target :=
  ⟨morphism.substitution, FormationSensitiveTypedQuotient.homTyped qualification morphism⟩

abbrev functionContext := admitContext TypedQuotientControls.functionContext.erase
noncomputable abbrev functionType := admitType TypedQuotientControls.displayedFunctionType.erase
noncomputable abbrev functionValue := admitTerm TypedQuotientControls.functionValue.erase
noncomputable abbrev etaValue := admitTerm TypedQuotientControls.etaValue.erase

theorem function_domain_is_variable :
    functionType.code = .pi (.var (1 : Fin 2)) (.var (2 : Fin 3)) := rfl

/-- This is an equation of whole natural sections, including all admitted
future substitutions into the genuinely variable domain X. -/
theorem function_eta_native :
    nativeSection levels functionValue = nativeSection levels etaValue :=
  (section_eq_iff levels functionValue etaValue).mpr TypedQuotientControls.eta_typed

theorem eta_codes_remain_distinct : functionValue.code ≠ etaValue.code := by
  intro same
  cases same

theorem eta_not_raw_conversion :
    ¬ Conv Tower.rules.headEq functionValue.code etaValue.code Tower.rules.computation :=
  TypedQuotientControls.eta_not_raw_converted

/-- A native natural certificate cannot uniformly recover the original
quoted implementation when its actual typed equations include eta. -/
theorem no_uniform_native_original_code :
    ¬ ∃ decode : (family levels (QType.mk levels functionType)).sections →
        Tower.Tm functionContext.arity,
      ∀ term : Term functionContext functionType,
        decode (nativeSection levels term) = term.code := by
  rintro ⟨decode, recovers⟩
  have same := congrArg decode function_eta_native
  rw [recovers functionValue, recovers etaValue] at same
  exact eta_codes_remain_distinct same

theorem eta_native_at_supplied_substitution {source : Context Tower.rules}
    (morphism : source ⟶ functionContext) :
    nativeSection levels (functionValue.reindex morphism) =
      nativeSection levels (etaValue.reindex morphism) := by
  exact (section_reindex levels functionValue morphism).trans
    ((congrArg (CwfYoneda.substituteSection (QuotientCwf.cwf levels)
      (QuotientCwf.project morphism)) function_eta_native).trans
      (section_reindex levels etaValue morphism).symm)

abbrev memberContext := admitContext ConversionQuotientControls.sourceContext
abbrev memberType := admitType ConversionQuotientControls.typeX
abbrev memberValue := admitTerm ConversionQuotientControls.valueX
abbrev betaValue := admitTerm ConversionQuotientControls.betaValue

theorem member_domain_is_variable : memberType.code = .var (1 : Fin 2) := rfl

theorem beta_native : nativeSection levels betaValue = nativeSection levels memberValue := by
  apply (section_eq_iff levels betaValue memberValue).mpr
  exact (FormationSensitiveTypedQuotient.conversionTermEq qualification
    ConversionQuotientControls.betaValue ConversionQuotientControls.valueX (.refl _)
    ConversionQuotientControls.betaConversion).2

abbrev extendedContext := admitContext ConversionQuotientControls.extendedSource
abbrev selector := admitArrow ConversionQuotientControls.replacement
abbrev oldProjection := admitArrow
  (FormationSensitiveContextual.projectionHom ConversionQuotientControls.sourceContext
    ConversionQuotientControls.typeX)

theorem selector_indices : selector.substitution (0 : Fin 2) = .var (0 : Fin 3) ∧
    selector.substitution (1 : Fin 2) = .var (2 : Fin 3) := ⟨rfl, rfl⟩

theorem selector_is_not_projection : selector ≠ oldProjection := by
  intro same
  have component := congrArg (fun morphism : extendedContext ⟶ memberContext =>
    morphism.substitution (0 : Fin 2)) same
  change Tm.var (0 : Fin 3) = Tm.var (1 : Fin 3) at component
  cases component

/-- Both substitutions retain the same actually bound type X. -/
theorem selector_annotation :
    memberType.reindex selector = memberType.reindex oldProjection := rfl

theorem selector_reads_newest :
    (CwfYoneda.decodeTerm (QuotientCwf.cwf levels) (QType.mk levels memberType)
      (QuotientCwf.project selector)
      ((nativeSection levels memberValue).val
        ⟨op (CwfYoneda.context (QuotientCwf.cwf levels) (context extendedContext)),
          QuotientCwf.project selector⟩)).val =
        QTerm.mk levels (⟨.var (0 : Fin 3), .var (0 : Fin 3)⟩ :
          Term extendedContext (memberType.reindex selector)) :=
  section_readout levels memberValue selector

theorem projection_reads_older :
    (CwfYoneda.decodeTerm (QuotientCwf.cwf levels) (QType.mk levels memberType)
      (QuotientCwf.project oldProjection)
      ((nativeSection levels memberValue).val
        ⟨op (CwfYoneda.context (QuotientCwf.cwf levels) (context extendedContext)),
          QuotientCwf.project oldProjection⟩)).val =
        QTerm.mk levels (⟨.var (1 : Fin 3), .var (1 : Fin 3)⟩ :
          Term extendedContext (memberType.reindex oldProjection)) :=
  section_readout levels memberValue oldProjection

/-- Full typed equality cannot identify the two independently supplied
members: the earned tower model reads them as distinct actual values. -/
theorem selected_members_not_equal (h : CofinalInaccessibles.{u}) :
    ¬ Equal Tower.rules extendedContext.raw
      (memberValue.reindex selector).code (memberValue.reindex oldProjection).code
      (memberType.reindex selector).code := by
  intro same
  let left := ConversionQuotientControls.valueX.reindex ConversionQuotientControls.replacement
  let right := ConversionQuotientControls.valueX.reindex
    (FormationSensitiveContextual.projectionHom ConversionQuotientControls.sourceContext
      ConversionQuotientControls.typeX)
  have annotations : TypeEq Tower.rules ConversionQuotientControls.extendedSource.raw
      (ConversionQuotientControls.typeX.reindex ConversionQuotientControls.replacement).code
      (ConversionQuotientControls.typeX.reindex
        (FormationSensitiveContextual.projectionHom ConversionQuotientControls.sourceContext
          ConversionQuotientControls.typeX)).code :=
    ⟨.sort Tower.zero, .sort _, .refl (.var 2)⟩
  have values := TypedQuotientValues.representativeTermValue_equal qualification towerLiftingFacts
    (standardTowerModel h) ConversionQuotientControls.extendedFormed rfl left right annotations same
  have readsLeft := ConversionQuotient.termValue_annotation towerLiftingFacts (standardTowerModel h)
    qualification.forms qualification.roots qualification.heads qualification.church
    ConversionQuotientControls.extendedFormed rfl left
    (code := TypedEquality.Annotated.CTm.var (0 : Fin 3))
    (typeCode := TypedEquality.Annotated.CTm.var (2 : Fin 3)) (.var 0) rfl rfl
  have readsRight := ConversionQuotient.termValue_annotation towerLiftingFacts (standardTowerModel h)
    qualification.forms qualification.roots qualification.heads qualification.church
    ConversionQuotientControls.extendedFormed rfl right
    (code := TypedEquality.Annotated.CTm.var (1 : Fin 3))
    (typeCode := TypedEquality.Annotated.CTm.var (2 : Fin 3)) (.var 1) rfl rfl
  rw [readsLeft, readsRight] at values
  have point := congrFun values (ConversionQuotientControls.thirdEnvironment h)
  change ({∅} : ZFSet.{u}) = ∅ at point
  have emptyIn : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [point] at emptyIn
  exact ZFSet.notMem_empty _ emptyIn

/-- A native client that substitutes y for x has a different answer even
though its supplied type variable X and final type annotation are retained. -/
theorem selector_native_sections_differ (h : CofinalInaccessibles.{u}) :
    nativeSection levels (memberValue.reindex selector) ≠
      nativeSection levels (memberValue.reindex oldProjection) := by
  intro same
  exact selected_members_not_equal h
    ((section_eq_iff levels (memberValue.reindex selector)
      (memberValue.reindex oldProjection)).mp same)

/-! ## A dependent annotation which raw conversion does not identify -/

theorem eta_annotation_native :
    nativeSectionAt levels TypedContextualControls.convertedVariable
      ((QType.mk_eq_iff levels
        (TypedContextualControls.secondAnnotation.reindex
          (projectionHom TypedContextualControls.familyContext TypedContextualControls.firstAnnotation))
        (TypedContextualControls.firstAnnotation.reindex
          (projectionHom TypedContextualControls.familyContext TypedContextualControls.firstAnnotation))).mpr
        (reindex_typeEquality TypedContextualControls.annotations_equal
          (projectionHom TypedContextualControls.familyContext
            TypedContextualControls.firstAnnotation)).symm) =
      nativeSection levels TypedContextualControls.suppliedVariable :=
  section_convertType levels TypedContextualControls.suppliedVariable _ _

theorem eta_annotation_is_not_raw_hiding :
    TypedContextualControls.firstAnnotation.code ≠ TypedContextualControls.secondAnnotation.code ∧
      ¬ Conv Tower.rules.headEq TypedContextualControls.firstAnnotation.code
        TypedContextualControls.secondAnnotation.code Tower.rules.computation :=
  ⟨TypedContextualControls.annotations_different_codes,
    TypedContextualControls.annotations_not_raw_converted⟩

/-- The actual native pair across the changed annotation is the represented
source pairing, with the canonical type-substitution and comprehension
comparisons retained explicitly. -/
theorem eta_annotation_native_pair :
    DisplayedPresheafCwf.presheafPair
        (yoneda.map (show CwfYoneda.context (QuotientCwf.cwf levels)
            ((quotientProjection Tower.rules).obj TypedContextualControls.suppliedContext) ⟶
          CwfYoneda.context (QuotientCwf.cwf levels)
            ((quotientProjection Tower.rules).obj TypedContextualControls.familyContext) from
          QuotientCwf.project (projectionHom TypedContextualControls.familyContext
            TypedContextualControls.firstAnnotation)))
        (family levels (QType.mk levels TypedContextualControls.secondAnnotation))
        ((Functor.sectionsFunctor _).map
          (CwfYoneda.substitutionIso (QuotientCwf.cwf levels)
            (QType.mk levels TypedContextualControls.secondAnnotation)
            (QuotientCwf.project (projectionHom TypedContextualControls.familyContext
              TypedContextualControls.firstAnnotation))).hom
          (CwfYoneda.interpretTerm (QuotientCwf.cwf levels)
            TypedContextualControls.suppliedNativeVariable)) ≫
        (CwfYoneda.comprehensionIso (QuotientCwf.cwf levels)
          (QType.mk levels TypedContextualControls.secondAnnotation)).hom =
      yoneda.map (show CwfYoneda.context (QuotientCwf.cwf levels)
            ((quotientProjection Tower.rules).obj TypedContextualControls.suppliedContext) ⟶
          CwfYoneda.context (QuotientCwf.cwf levels)
            (QuotientCwf.ext ((quotientProjection Tower.rules).obj TypedContextualControls.familyContext)
              (QType.mk levels TypedContextualControls.secondAnnotation)) from
        TypedContextualControls.nativePair) :=
  CwfYoneda.pairing_preserved (QuotientCwf.cwf levels)
    (QType.mk levels TypedContextualControls.secondAnnotation)
    (QuotientCwf.project (projectionHom TypedContextualControls.familyContext
      TypedContextualControls.firstAnnotation)) TypedContextualControls.suppliedNativeVariable

end Examples.TypedNativePresheafControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
