import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionFibres
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Conservativity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ChurchSoundness

/-!
# Model values of formed conversion classes

The interpretation is in an independently supplied set model, at a supplied
formed annotated telescope erasing the source telescope. Annotations are
constructed from admitted source typings. Their values on satisfying
environments are independent of both the typing certificate and the chosen
annotation. Qualified raw conversion therefore descends to the existing
joint term/type conversion classes.

The qualifications are formation discrimination, head/root preservation,
Church--Rosser, annotated lifting, and the local primitive laws of a set
model. No conversion-soundness or whole-proof soundness field is assumed.
This is a semantic quotient interpretation, not an arbitrary-CwF interpreter
or a classifying universal property.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace ConversionQuotient

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization
open Presentation.FormationSensitiveContextual
open UniverseLevel (LevelOrder)

universe u

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}
variable {P : ChurchRules S.R} {heads : Head → ZFSet.{u}} {constants : DeclName → ZFSet.{u}}

/-- Only environments satisfying the independently authored telescope are
observed. Outside that telescope, annotation coherence need not hold. -/
abbrev Environment {n : Nat} (context : CCtx Head n) :=
  {environment : Env.{u} n // Sat heads constants context environment}

abbrev Value {n : Nat} (context : CCtx Head n) :=
  Environment (heads := heads) (constants := constants) context → ZFSet.{u}

noncomputable def annotationValue {n : Nat} {context : CCtx Head n}
    (term : CTm Head n) : Value (heads := heads) (constants := constants) context :=
  fun environment => ev heads constants term environment.val

variable (lifting : LiftingFacts P) (model : SetModel heads constants P)

include lifting model in
/-- Independently admitted annotations with the same subject and type
erasures have identical values at every satisfying environment. -/
theorem annotationValue_independent {n : Nat} {context : CCtx Head n}
    (formed : CCtxFormed P context) {first second firstType secondType : CTm Head n}
    (firstTyped : CTyped P context first firstType)
    (secondTyped : CTyped P context second secondType)
    (sameSubject : first.erase = second.erase)
    (sameType : firstType.erase = secondType.erase) :
    annotationValue (heads := heads) (constants := constants) (context := context) first =
      annotationValue (context := context) second := by
  have secondAtFirst := lifting.retype S.levels formed secondTyped
    (CTyped.isType S.levels firstTyped formed) sameType.symm
  have equal := lifting.coherent formed firstTyped secondAtFirst sameSubject
  funext environment
  exact CDerivable.sound_equality model equal environment.val environment.property

include lifting model in
/-- Independently admitted annotations of one source type need not have
the same selected formation universe; their semantic values still agree. -/
theorem typeAnnotationValue_independent {n : Nat} {context : CCtx Head n}
    (formed : CCtxFormed P context) {first second : CTm Head n}
    (firstFormed : CIsType P context first) (secondFormed : CIsType P context second)
    (sameCode : first.erase = second.erase) :
    annotationValue (heads := heads) (constants := constants) (context := context) first =
      annotationValue (context := context) second := by
  obtain ⟨_, _, equal⟩ := lifting.typeEq S.levels formed firstFormed secondFormed sameCode
  funext environment
  exact CDerivable.sound_equality model equal environment.val environment.property

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (headPreserving : HeadPreserving S.R) (church : ConversionCoherence.ChurchRosser S.R)
variable {source : Context S.R} {context : CCtx Head source.arity}
  (formed : CCtxFormed P context) (erases : context.erase = source.raw)

/-- An annotation of the actual source formation certificate. -/
structure TypeAnnotation (type : TypeOver source) where
  code : CTm Head source.arity
  erases : code.erase = type.code
  typed : CTyped P context code (.head type.level)

/-- A joint annotation retains both the subject and its displayed type. -/
structure TermAnnotation {type : TypeOver source} (term : Term source type) where
  code : CTm Head source.arity
  typeCode : CTm Head source.arity
  erases : code.erase = term.code
  typeErases : typeCode.erase = type.code
  typed : CTyped P context code typeCode

include facts roots headPreserving church lifting formed erases in
theorem type_annotation_exists (type : TypeOver source) :
    Nonempty (TypeAnnotation (P := P) (context := context) type) := by
  have sourceFormed : CtxFormed S.R source.raw := erases ▸ formed.erase
  have typing := FormationSensitive.Typing.toTyped facts roots headPreserving church
    type.formed sourceFormed
  obtain ⟨code, universeCode, codeErases, universeErases, admitted⟩ :=
    lifts S.levels lifting typing formed erases
  obtain rfl := CTm.erase_eq_head universeErases
  exact ⟨⟨code, codeErases, admitted⟩⟩

include facts roots headPreserving church lifting formed erases in
theorem term_annotation_exists {type : TypeOver source} (term : Term source type) :
    Nonempty (TermAnnotation (P := P) (context := context) term) := by
  have sourceFormed : CtxFormed S.R source.raw := erases ▸ formed.erase
  have typing := FormationSensitive.Typing.toTyped facts roots headPreserving church
    term.typed sourceFormed
  obtain ⟨code, typeCode, codeErases, typeErases, admitted⟩ :=
    lifts S.levels lifting typing formed erases
  exact ⟨⟨code, typeCode, codeErases, typeErases, admitted⟩⟩

noncomputable def typeAnnotation (type : TypeOver source) :
    TypeAnnotation (P := P) (context := context) type :=
  Classical.choice (type_annotation_exists lifting facts roots headPreserving church formed erases type)

noncomputable def termAnnotation {type : TypeOver source} (term : Term source type) :
    TermAnnotation (P := P) (context := context) term :=
  Classical.choice (term_annotation_exists lifting facts roots headPreserving church formed erases term)

noncomputable def typeValue (type : TypeOver source) :
    Value (heads := heads) (constants := constants) context :=
  annotationValue (typeAnnotation lifting facts roots headPreserving church formed erases type).code

noncomputable def termValue {type : TypeOver source} (term : Term source type) :
    Value (heads := heads) (constants := constants) context :=
  annotationValue (termAnnotation lifting facts roots headPreserving church formed erases term).code

include model in
/-- The constructed type value agrees with every independently admitted
annotation, not only the annotation selected by the construction. -/
theorem typeValue_annotation (type : TypeOver source) {code : CTm Head source.arity}
    (codeFormed : CIsType P context code) (codeErases : code.erase = type.code) :
    typeValue lifting facts roots headPreserving church formed erases
        (heads := heads) (constants := constants) type =
      annotationValue (context := context) code := by
  let chosen := typeAnnotation lifting facts roots headPreserving church formed erases type
  exact typeAnnotationValue_independent lifting model formed
    ⟨type.level, type.universeWitness, chosen.typed⟩ codeFormed
    (chosen.erases.trans codeErases.symm)

include model in
/-- The constructed term value agrees with every independently admitted
joint annotation of that term and its supplied type. -/
theorem termValue_annotation {type : TypeOver source} (term : Term source type)
    {code typeCode : CTm Head source.arity}
    (typed : CTyped P context code typeCode) (codeErases : code.erase = term.code)
    (typeErases : typeCode.erase = type.code) :
    termValue lifting facts roots headPreserving church formed erases
        (heads := heads) (constants := constants) term =
      annotationValue (context := context) code := by
  let chosen := termAnnotation lifting facts roots headPreserving church formed erases term
  exact annotationValue_independent lifting model formed chosen.typed typed
    (chosen.erases.trans codeErases.symm) (chosen.typeErases.trans typeErases.symm)

include model in
/-- Membership is proved from the interpreted typing certificate and then
the annotation-independence theorem identifies its displayed type. -/
theorem termValue_member {type : TypeOver source} (term : Term source type)
    (environment : Environment (heads := heads) (constants := constants) context) :
    termValue lifting facts roots headPreserving church formed erases term environment ∈
      typeValue lifting facts roots headPreserving church formed erases type environment := by
  let chosen := termAnnotation lifting facts roots headPreserving church formed erases term
  have membership := (CDerivable.sound model chosen.typed) environment.val environment.property
  have typeComparison := typeValue_annotation lifting model facts roots headPreserving church
    formed erases type (CTyped.isType S.levels chosen.typed formed) chosen.typeErases
  rw [typeComparison]
  exact membership

include model in
/-- Qualified raw conversion of independently formed types preserves their
actual model values. Different selected universes are permitted. -/
theorem typeValue_conversion (first second : TypeOver source)
    (conversion : Conv S.R.headEq first.code second.code S.R.computation) :
    typeValue lifting facts roots headPreserving church formed erases
        (heads := heads) (constants := constants) first =
      typeValue lifting facts roots headPreserving church formed erases second := by
  have sourceFormed : CtxFormed S.R source.raw := erases ▸ formed.erase
  have firstTyped := FormationSensitive.Typing.toTyped facts roots headPreserving church
    first.formed sourceFormed
  have secondTyped := FormationSensitive.Typing.toTyped facts roots headPreserving church
    second.formed sourceFormed
  obtain ⟨level, universeWitness, equal⟩ := Conv.toTypeEq facts roots headPreserving church
    sourceFormed conversion firstTyped first.universeWitness secondTyped second.universeWitness
  obtain ⟨firstCode, secondCode, universeCode, firstErases, secondErases, universeErases, equality⟩ :=
    lifts S.levels lifting equal formed erases
  obtain rfl := CTm.erase_eq_head universeErases
  have firstAdmitted := (CEqual.typed S.levels equality formed).1
  have secondAdmitted := (CEqual.typed S.levels equality formed).2
  rw [typeValue_annotation lifting model facts roots headPreserving church formed erases first
      ⟨level, universeWitness, firstAdmitted⟩ firstErases,
    typeValue_annotation lifting model facts roots headPreserving church formed erases second
      ⟨level, universeWitness, secondAdmitted⟩ secondErases]
  funext environment
  exact CDerivable.sound_equality model equality environment.val environment.property

include model in
/-- Joint type and subject conversion preserves the actual interpreted
subject, rather than comparing only its displayed type. -/
theorem termValue_conversion {first second : TypeOver source}
    (left : Term source first) (right : Term source second)
    (typesConverted : Conv S.R.headEq first.code second.code S.R.computation)
    (subjectsConverted : Conv S.R.headEq left.code right.code S.R.computation) :
    termValue lifting facts roots headPreserving church formed erases
        (heads := heads) (constants := constants) left =
      termValue lifting facts roots headPreserving church formed erases right := by
  have sourceFormed : CtxFormed S.R source.raw := erases ▸ formed.erase
  let convertedRight := right.convertType first typesConverted.symm
  have leftTyped := FormationSensitive.Typing.toTyped facts roots headPreserving church
    left.typed sourceFormed
  have rightTyped := FormationSensitive.Typing.toTyped facts roots headPreserving church
    convertedRight.typed sourceFormed
  have equal := Conv.toEqual facts roots headPreserving church sourceFormed
    subjectsConverted leftTyped rightTyped
  obtain ⟨leftCode, rightCode, typeCode, leftErases, rightErases, typeErases, equality⟩ :=
    lifts S.levels lifting equal formed erases
  have leftAdmitted := (CEqual.typed S.levels equality formed).1
  have rightAdmitted := (CEqual.typed S.levels equality formed).2
  have chosenLeft := termValue_annotation lifting model facts roots headPreserving church
    formed erases left leftAdmitted leftErases typeErases
  have rawTypeEqual := Conv.toTypeEq facts roots headPreserving church sourceFormed
    typesConverted
    (FormationSensitive.Typing.toTyped facts roots headPreserving church first.formed sourceFormed)
    first.universeWitness
    (FormationSensitive.Typing.toTyped facts roots headPreserving church second.formed sourceFormed)
    second.universeWitness
  obtain ⟨uLevel, uWitness, typeEqual⟩ := rawTypeEqual
  obtain ⟨firstAnn, secondAnn, uAnn, firstAnnErases, secondAnnErases, uAnnErases, annTypeEqual⟩ :=
    lifts S.levels lifting typeEqual formed erases
  obtain rfl := CTm.erase_eq_head uAnnErases
  have rightAtSecond : CTyped P context rightCode secondAnn := by
    have firstEq : CTypeEq P context typeCode firstAnn :=
      lifting.typeEq S.levels formed (CTyped.isType S.levels rightAdmitted formed)
        ⟨uLevel, uWitness, (CEqual.typed S.levels annTypeEqual formed).1⟩
        (typeErases.trans firstAnnErases.symm)
    have across : CTypeEq P context firstAnn secondAnn :=
      ⟨uLevel, uWitness, annTypeEqual⟩
    exact CTyped.convType rightAdmitted (firstEq.trans S.levels across)
  rw [chosenLeft,
    termValue_annotation lifting model facts roots headPreserving church formed erases
      right rightAtSecond rightErases secondAnnErases]
  funext environment
  exact CDerivable.sound_equality model equality environment.val environment.property

/-- A formed type class denotes an actual contextual set-valued function. -/
noncomputable def quotientTypeValue (type : QType source) :
    Value (heads := heads) (constants := constants) context :=
  Quotient.liftOn type
    (typeValue lifting facts roots headPreserving church formed erases)
    (typeValue_conversion lifting model facts roots headPreserving church formed erases)

/-- Joint conversion classes denote actual contextual values. -/
noncomputable def quotientTermValue (term : QTerm source) :
    Value (heads := heads) (constants := constants) context :=
  Quotient.liftOn term
    (fun pair : TotalTerm source => termValue lifting facts roots headPreserving church formed erases pair.2)
    (fun _ _ related => termValue_conversion lifting model facts roots headPreserving church
      formed erases _ _ related.1 related.2)

@[simp] theorem quotientTypeValue_mk (type : TypeOver source) :
    quotientTypeValue lifting model facts roots headPreserving church formed erases
        (heads := heads) (constants := constants) (QType.mk type) =
      typeValue lifting facts roots headPreserving church formed erases type := rfl

@[simp] theorem quotientTermValue_mk {type : TypeOver source} (term : Term source type) :
    quotientTermValue lifting model facts roots headPreserving church formed erases
        (heads := heads) (constants := constants) (QTerm.mk term) =
      termValue lifting facts roots headPreserving church formed erases term := rfl

/-- Every joint class retains the membership theorem for its own displayed
type class. No representatives are inspected by the semantic conclusion. -/
theorem quotientTermValue_member (term : QTerm source)
    (environment : Environment (heads := heads) (constants := constants) context) :
    quotientTermValue lifting model facts roots headPreserving church formed erases term environment ∈
      quotientTypeValue lifting model facts roots headPreserving church formed erases term.type environment := by
  induction term using Quotient.inductionOn with
  | h pair =>
      exact termValue_member lifting model facts roots headPreserving church
        formed erases pair.2 environment

end ConversionQuotient
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
