import Mettapedia.OSLF.Framework.WMCalculusNativeObservation
import Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient

/-!
# Observational equality as a native quotient-diagonal predicate

Behavioral agreement on raw WM states is the inverse image of literal
equality on their observational quotient. This statement holds as an equality
of subfunctors in the existing language-dependent presheaf fibration, not
merely as a pointwise equivalence. It commutes with substitution into any
presheaf context and is stable under independent contextual computation of
both state terms.

The construction is an extensional equality predicate for the quotient.
It does not install an intensional identity former or dependent eliminator
in Prime's authored syntax.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeObservationalEquality

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.PresheafNativeType

private abbrev wmLanguage : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- State pairs over the same authored-language presheaf base as the other
native WM observations. -/
def statePairObj (State : Type) : languagePresheafObj wmLanguage :=
  (Functor.const (Opposite (ConstructorObj wmLanguage))).obj (State × State)

/-- Apply the observational quotient to both coordinates naturally at every
constructor stage. -/
def quotientPairMap {State Query V : Type} (R : WMReading State Query V) :
    statePairObj State ⟶ statePairObj (ObsState R) where
  app X := TypeCat.ofHom (fun pair => (classOf R pair.1, classOf R pair.2))
  naturality := by
    intro X Y f
    rfl

/-- Raw behavioral agreement, viewed as a native predicate on state pairs. -/
def behavioralEquality {State Query V : Type}
    (R : WMReading State Query V) : Subfunctor (statePairObj State) where
  obj X := { pair | R.Agree .state pair.1 pair.2 }
  map := by
    intro X Y f pair agree
    exact agree

/-- Literal state equality before quotienting is a strictly stronger
predicate in readings with hidden state distinctions. -/
def rawDiagonal (State : Type) : Subfunctor (statePairObj State) where
  obj X := { pair | pair.1 = pair.2 }
  map := by
    intro X Y f pair equal
    exact equal

/-- The quotient's ordinary diagonal equality predicate. -/
def quotientDiagonal {State Query V : Type}
    (R : WMReading State Query V) :
    Subfunctor (statePairObj (ObsState R)) :=
  rawDiagonal (ObsState R)

/-- Behavioral equality is exactly the pullback of the quotient diagonal,
as an equality of native predicates over every constructor stage. -/
theorem behavioralEquality_eq_quotientDiagonal_preimage
    {State Query V : Type} (R : WMReading State Query V) :
    behavioralEquality R =
      (quotientDiagonal R).preimage (quotientPairMap R) := by
  ext X pair
  exact (classOf_eq_iff_agree R pair.1 pair.2).symm

/-- The equality comparison is coherent under substitution into an
arbitrary presheaf context, rather than only for constant global states. -/
theorem behavioralEquality_reindex
    {State Query V : Type} (R : WMReading State Query V)
    {Γ : languagePresheafObj wmLanguage}
    (pair : Γ ⟶ statePairObj State) :
    (behavioralEquality R).preimage pair =
      (quotientDiagonal R).preimage (pair ≫ quotientPairMap R) := by
  rw [behavioralEquality_eq_quotientDiagonal_preimage]
  simp only [Subfunctor.preimage_comp]

/-- Behavioral equality and the quotient diagonal are native types over
different bases, connected by the actual quotient map. -/
def behavioralEqualityNativeType {State Query V : Type}
    (R : WMReading State Query V) :
    FullPresheafGrothendieckObj wmLanguage where
  base := Opposite.op (statePairObj State)
  fiber := behavioralEquality R

def quotientDiagonalNativeType {State Query V : Type}
    (R : WMReading State Query V) :
    FullPresheafGrothendieckObj wmLanguage where
  base := Opposite.op (statePairObj (ObsState R))
  fiber := quotientDiagonal R

/-- Native-type transport along the quotient pair map is exact on fibres.
The map is not an identity eliminator for raw states. -/
def behavioralEqualityToQuotientDiagonal {State Query V : Type}
    (R : WMReading State Query V) :
    FullPresheafGrothendieckHom wmLanguage
      (behavioralEqualityNativeType R)
      (quotientDiagonalNativeType R) where
  base := quotientPairMap R
  fiberLe := by
    exact le_of_eq (behavioralEquality_eq_quotientDiagonal_preimage R)

/-- Independent contextual computation on two state terms preserves their
observational equality in both directions. -/
theorem denotedPairSteps_agree_iff {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    {first first' second second' : WMTerm .state}
    (firstSteps : WMContextStepStar first first')
    (secondSteps : WMContextStepStar second second') :
    R.Agree .state (R.denote first) (R.denote second) ↔
      R.Agree .state (R.denote first') (R.denote second') := by
  have firstAgree := laws.agree_of_contextStepStar firstSteps
  have secondAgree := laws.agree_of_contextStepStar secondSteps
  constructor
  · intro together
    exact R.agree_trans .state (R.agree_symm .state firstAgree)
      (R.agree_trans .state together secondAgree)
  · intro together
    exact R.agree_trans .state firstAgree
      (R.agree_trans .state together
        (R.agree_symm .state secondAgree))

/-- Thus computation also preserves literal equality of quotient states.
This is a dependent equality readout, not equality of raw states. -/
theorem denotedPairSteps_quotientEq_iff {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    {first first' second second' : WMTerm .state}
    (firstSteps : WMContextStepStar first first')
    (secondSteps : WMContextStepStar second second') :
    classOf R (R.denote first) = classOf R (R.denote second) ↔
      classOf R (R.denote first') = classOf R (R.denote second') := by
  rw [classOf_eq_iff_agree, classOf_eq_iff_agree]
  exact denotedPairSteps_agree_iff R laws firstSteps secondSteps

/-- Agreement can be strictly weaker than the raw diagonal. -/
theorem behavioralEquality_ne_rawDiagonal_of_distinct_agree
    {State Query V : Type} (R : WMReading State Query V)
    (X : Opposite (ConstructorObj wmLanguage))
    {first second : State} (distinct : first ≠ second)
    (agree : R.Agree .state first second) :
    behavioralEquality R ≠ rawDiagonal State := by
  intro equal
  have member : (first, second) ∈ (behavioralEquality R).obj X := agree
  rw [equal] at member
  exact distinct member

end Mettapedia.OSLF.Framework.WMCalculusNativeObservationalEquality
