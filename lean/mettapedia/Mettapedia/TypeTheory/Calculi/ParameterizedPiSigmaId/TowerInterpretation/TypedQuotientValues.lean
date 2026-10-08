import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTypedQuotient
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ConversionQuotient

/-!
# Actual model values of typed equality classes

The independently supplied set model interprets the full typed equality,
including dependent function and pair eta. Anchored annotation lifting and
the existing model soundness theorem establish equality of the actual
values of independently formed representatives. These values therefore
descend to the typed quotients, retaining their displayed membership.

The raw-to-typed-to-model triangle is proved for every supplied conversion
class. The operational qualification, annotation lifting and local model
laws remain explicit. This is a qualified set-model interpretation, not an
arbitrary native CwF interpreter or a classifying universal property.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace TypedQuotientValues

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization
open Presentation.FormationSensitiveContextual
open UniverseLevel (LevelOrder)

universe u

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}
variable {P : ChurchRules S.R} {heads : Head → ZFSet.{u}} {constants : DeclName → ZFSet.{u}}
variable (q : FormationSensitiveTypedQuotient.Qualification S)
  (lifting : LiftingFacts P) (model : SetModel heads constants P)
variable {source : Context S.R} {context : CCtx Head source.arity}
  (formed : CCtxFormed P context) (erases : context.erase = source.raw)

include model in
/-- Actual type values agree under full typed equality, allowing independently
chosen formation universes and annotations. -/
theorem representativeTypeValue_equal (first second : TypeOver source)
    (equal : TypeEq S.R source.raw first.code second.code) :
    ConversionQuotient.typeValue lifting q.forms q.roots q.heads q.church formed erases
        (heads := heads) (constants := constants) first =
      ConversionQuotient.typeValue lifting q.forms q.roots q.heads q.church formed erases second := by
  obtain ⟨level, universeWitness, typedEqual⟩ := equal
  obtain ⟨firstCode, secondCode, universeCode, firstErases, secondErases, universeErases, equality⟩ :=
    lifts S.levels lifting typedEqual formed erases
  obtain rfl := CTm.erase_eq_head universeErases
  have firstAdmitted := (CEqual.typed S.levels equality formed).1
  have secondAdmitted := (CEqual.typed S.levels equality formed).2
  rw [ConversionQuotient.typeValue_annotation lifting model q.forms q.roots q.heads q.church
      formed erases first ⟨level, universeWitness, firstAdmitted⟩ firstErases,
    ConversionQuotient.typeValue_annotation lifting model q.forms q.roots q.heads q.church
      formed erases second ⟨level, universeWitness, secondAdmitted⟩ secondErases]
  funext environment
  exact CDerivable.sound_equality model equality environment.val environment.property

include model in
/-- The heterogeneous typed relation identifies actual subject values. The
right annotation is aligned by its earned typed type equality. -/
theorem representativeTermValue_equal {first second : TypeOver source}
    (left : Term source first) (right : Term source second)
    (typesEqual : TypeEq S.R source.raw first.code second.code)
    (valuesEqual : Equal S.R source.raw left.code right.code first.code) :
    ConversionQuotient.termValue lifting q.forms q.roots q.heads q.church formed erases
        (heads := heads) (constants := constants) left =
      ConversionQuotient.termValue lifting q.forms q.roots q.heads q.church formed erases right := by
  obtain ⟨leftCode, rightCode, typeCode, leftErases, rightErases, typeErases, equality⟩ :=
    lifts S.levels lifting valuesEqual formed erases
  have leftAdmitted := (CEqual.typed S.levels equality formed).1
  have rightAdmitted := (CEqual.typed S.levels equality formed).2
  have chosenLeft := ConversionQuotient.termValue_annotation lifting model
    q.forms q.roots q.heads q.church formed erases left leftAdmitted leftErases typeErases
  obtain ⟨level, universeWitness, typeEqual⟩ := typesEqual
  obtain ⟨firstAnn, secondAnn, universeAnn, firstAnnErases, secondAnnErases, universeAnnErases,
      annTypeEqual⟩ := lifts S.levels lifting typeEqual formed erases
  obtain rfl := CTm.erase_eq_head universeAnnErases
  have rightAtSecond : CTyped P context rightCode secondAnn := by
    have firstEq : CTypeEq P context typeCode firstAnn :=
      lifting.typeEq S.levels formed (CTyped.isType S.levels rightAdmitted formed)
        ⟨level, universeWitness, (CEqual.typed S.levels annTypeEqual formed).1⟩
        (typeErases.trans firstAnnErases.symm)
    have across : CTypeEq P context firstAnn secondAnn :=
      ⟨level, universeWitness, annTypeEqual⟩
    exact CTyped.convType rightAdmitted (firstEq.trans S.levels across)
  rw [chosenLeft,
    ConversionQuotient.termValue_annotation lifting model q.forms q.roots q.heads q.church
      formed erases right rightAtSecond rightErases secondAnnErases]
  funext environment
  exact CDerivable.sound_equality model equality environment.val environment.property

/-- A typed type class denotes its actual set-valued function on admitted
environments, independently of the selected representative. -/
noncomputable def typeValue (type : FormationSensitiveTypedQuotient.QType q source) :
    ConversionQuotient.Value (heads := heads) (constants := constants) context :=
  Quotient.liftOn type
    (ConversionQuotient.typeValue lifting q.forms q.roots q.heads q.church formed erases)
    (representativeTypeValue_equal q lifting model formed erases)

/-- Typed beta/eta total-term classes denote actual supplied values. -/
noncomputable def termValue (term : FormationSensitiveTypedQuotient.QTerm q source) :
    ConversionQuotient.Value (heads := heads) (constants := constants) context :=
  Quotient.liftOn term
    (fun pair : TotalTerm source =>
      ConversionQuotient.termValue lifting q.forms q.roots q.heads q.church formed erases pair.2)
    (fun _ _ related => representativeTermValue_equal q lifting model
      formed erases _ _ related.1 related.2)

@[simp] theorem typeValue_mk (type : TypeOver source) :
    typeValue q lifting model formed erases (FormationSensitiveTypedQuotient.QType.mk q type) =
      ConversionQuotient.typeValue lifting q.forms q.roots q.heads q.church formed erases
        (heads := heads) (constants := constants) type := rfl

@[simp] theorem termValue_mk {type : TypeOver source} (term : Term source type) :
    termValue q lifting model formed erases (FormationSensitiveTypedQuotient.QTerm.mk q term) =
      ConversionQuotient.termValue lifting q.forms q.roots q.heads q.church formed erases
        (heads := heads) (constants := constants) term := rfl

/-- Every typed total-term class retains membership in its own displayed
interpreted type, including classes identified by eta. -/
theorem termValue_member (term : FormationSensitiveTypedQuotient.QTerm q source)
    (environment : ConversionQuotient.Environment
      (heads := heads) (constants := constants) context) :
    termValue q lifting model formed erases term environment ∈
      typeValue q lifting model formed erases (FormationSensitiveTypedQuotient.QTerm.type q term)
        environment := by
  induction term using Quotient.inductionOn with
  | h pair =>
      exact ConversionQuotient.termValue_member lifting model q.forms q.roots q.heads q.church
        formed erases pair.2 environment

/-- The interpreted raw class agrees with its image in the typed type
quotient. This holds on every supplied class, not only normal forms. -/
theorem typeValue_ofRaw (type : FormationSensitiveContextual.QType source) :
    typeValue q lifting model formed erases (FormationSensitiveTypedQuotient.QType.ofRaw q type) =
      ConversionQuotient.quotientTypeValue lifting model q.forms q.roots q.heads q.church
        formed erases (heads := heads) (constants := constants) type := by
  induction type using Quotient.inductionOn with
  | h type => rfl

/-- The subject-value triangle commutes on every joint raw type/term class. -/
theorem termValue_ofRaw (term : FormationSensitiveContextual.QTerm source) :
    termValue q lifting model formed erases (FormationSensitiveTypedQuotient.QTerm.ofRaw q term) =
      ConversionQuotient.quotientTermValue lifting model q.forms q.roots q.heads q.church
        formed erases (heads := heads) (constants := constants) term := by
  induction term using Quotient.inductionOn with
  | h pair => rfl

end TypedQuotientValues
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
