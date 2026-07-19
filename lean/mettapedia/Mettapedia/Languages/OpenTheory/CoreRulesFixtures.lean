import Mettapedia.Languages.OpenTheory.CoreRules

/-!
# Calibration fixtures for the first six OpenTheory rules

These fixtures exercise successful and rejected raw rules, exact symbol
provenance, alpha-set deletion, axiom-tag identity, and the verified wrapper.
-/

namespace Mettapedia.Languages.OpenTheory

namespace CoreRulesFixtures

open SequentExamples CoreTermExamples

def p : CanonicalTerm := boolVariable "p"
def q : CanonicalTerm := boolVariable "q"
def r : CanonicalTerm := boolVariable "r"
def x : CanonicalTerm := individualVariable "x"
def y : CanonicalTerm := individualVariable "y"

theorem p_isBool : p.IsBool := by
  rfl

theorem q_isBool : q.IsBool := by
  rfl

theorem r_isBool : r.IsBool := by
  rfl

theorem x_not_isBool : ¬ x.IsBool := by
  intro hbool
  simp [x, individualVariable, CanonicalTerm.IsBool, Examples.individual,
    Ty.bool, TypeOp.bool, Name.global] at hbool

/-- A total fixture constructor for two already checked, same-typed operands. -/
def equalityOfSameType (left right : CanonicalTerm)
    (htypes : left.ty = right.ty) : CanonicalTerm :=
  ⟨CanonicalTerm.equalityDB left.ty left.term right.term, Ty.bool, by
    have hsame : Ty.same left.ty right.ty = true :=
      (Ty.same_eq_true_iff left.ty right.ty).mpr htypes
    simp [CanonicalTerm.equalityDB, Ty.equality, Ty.function,
      TypeOp.function, Ty.destFunction?, left.checked, right.checked, hsame]⟩

theorem equalityOfSameType_semantics
    (left right : CanonicalTerm) (htypes : left.ty = right.ty) :
    CanonicalTerm.EqualityConstructionSemantics left right
      (equalityOfSameType left right htypes) := by
  exact ⟨htypes, rfl⟩

def boolSequentP : Sequent := ⟨{p}, p⟩

def boolSequentQ : Sequent := ⟨{q}, q⟩

theorem boolSequentP_isBool : boolSequentP.IsBool := by
  simp [boolSequentP, Sequent.IsBool, p_isBool]

theorem boolSequentQ_isBool : boolSequentQ.IsBool := by
  simp [boolSequentQ, Sequent.IsBool, q_isBool]

def axiomP : Theorem :=
  Theorem.axiomResult boolSequentP boolSequentP_isBool

def axiomQ : Theorem :=
  Theorem.axiomResult boolSequentQ boolSequentQ_isBool

def assumeP : Theorem := Theorem.emptyResult {p} p
def assumeQ : Theorem := Theorem.emptyResult {q} q
def assumeR : Theorem := Theorem.emptyResult {r} r

def definedBoolOperator : TypeOp :=
  .mk (Name.global "bool")
    (.defined (.var (Name.global "witness") Ty.bool) [])

def definedBoolTy : Ty := .op definedBoolOperator []

def definedBoolTerm : CanonicalTerm :=
  ⟨.free ⟨Name.global "d", definedBoolTy⟩, definedBoolTy, by simp⟩

theorem definedBoolTerm_not_isBool : ¬ definedBoolTerm.IsBool := by
  intro hbool
  simp [definedBoolTerm, definedBoolTy, definedBoolOperator,
    CanonicalTerm.IsBool, Ty.bool, TypeOp.bool, Name.global] at hbool

/-! ## AXIOM and ASSUME -/

example : checkAxiom boolSequentP = some axiomP := by
  apply (checkAxiom_eq_some_iff boolSequentP axiomP).mpr
  exact ⟨boolSequentP_isBool,
    (theorem_axiomResult_eq_iff_hasParts
      boolSequentP boolSequentP_isBool axiomP).mp rfl⟩

example : checkAxiom nonBooleanSequent = none := by
  rw [checkAxiom_eq_none_iff]
  rintro ⟨out, semantics⟩
  exact x_not_isBool semantics.1.1

def boolConclusionNonBooleanHyp : Sequent := ⟨{x}, p⟩

theorem boolConclusionNonBooleanHyp_not_isBool :
    ¬ boolConclusionNonBooleanHyp.IsBool := by
  intro hbool
  exact x_not_isBool (hbool.2 x (by
    simp [boolConclusionNonBooleanHyp]))

/-- AXIOM checks every hypothesis, not only the Boolean conclusion. -/
example : checkAxiom boolConclusionNonBooleanHyp = none := by
  rw [checkAxiom_eq_none_iff]
  rintro ⟨out, semantics⟩
  exact boolConclusionNonBooleanHyp_not_isBool semantics.1

example : checkAssume p = some assumeP := by
  apply (checkAssume_eq_some_iff p assumeP).mpr
  exact ⟨p_isBool,
    (theorem_emptyResult_eq_iff_hasParts {p} p assumeP).mp rfl⟩

example : checkAssume x = none := by
  rw [checkAssume_eq_none_iff]
  rintro ⟨out, semantics⟩
  exact x_not_isBool semantics.1

/-- A defined type operator printed `bool` fails both primitive Boolean gates. -/
example : checkAssume definedBoolTerm = none := by
  rw [checkAssume_eq_none_iff]
  rintro ⟨out, semantics⟩
  exact definedBoolTerm_not_isBool semantics.1

def definedBoolSequent : Sequent :=
  ⟨{definedBoolTerm}, definedBoolTerm⟩

example : checkAxiom definedBoolSequent = none := by
  rw [checkAxiom_eq_none_iff]
  rintro ⟨out, semantics⟩
  exact definedBoolTerm_not_isBool semantics.1.1

/-- AXIOM and ASSUME can have source-equal current sequents while retaining
different axiom provenance. -/
example : axiomP.SourceEq assumeP := by
  rfl

example : axiomP.axioms ≠ assumeP.axioms := by
  simp [axiomP, assumeP, Theorem.axiomResult, Theorem.emptyResult]

/-! ## REFL -/

def xx : CanonicalTerm := equalityOfSameType x x rfl
def reflX : Theorem := Theorem.emptyResult ∅ xx

example : checkRefl x = some reflX := by
  apply (checkRefl_eq_some_iff x reflX).mpr
  exact ⟨xx, equalityOfSameType_semantics x x rfl,
    (theorem_emptyResult_eq_iff_hasParts ∅ xx reflX).mp rfl⟩

/-! ## APP -/

def f : CanonicalTerm :=
  functionVariable "f" Examples.individual Ty.bool

def fx : CanonicalTerm :=
  ⟨.app f.term x.term, Ty.bool, by
    simp [f, x, functionVariable, individualVariable,
      Ty.destFunction?_function]⟩

def ff : CanonicalTerm := equalityOfSameType f f rfl
def fxfx : CanonicalTerm := equalityOfSameType fx fx rfl
def reflF : Theorem := Theorem.emptyResult ∅ ff
def reflFX : Theorem := Theorem.emptyResult ∅ fxfx

def appResult : Theorem :=
  Theorem.unionResult reflF reflX ∅ fxfx

theorem checkApp_success : checkApp reflF reflX = some appResult := by
  apply (checkApp_eq_some_iff reflF reflX appResult).mpr
  refine ⟨f, f, x, x, fx, fx, fxfx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · exact equalityOfSameType_semantics x x rfl
  · exact ⟨Examples.individual, Ty.bool,
      Ty.destFunction?_function Examples.individual Ty.bool, rfl, rfl⟩
  · exact ⟨Examples.individual, Ty.bool,
      Ty.destFunction?_function Examples.individual Ty.bool, rfl, rfl⟩
  · exact equalityOfSameType_semantics fx fx rfl
  · exact (theorem_unionResult_eq_iff_hasParts
      reflF reflX ∅ fxfx appResult).mp rfl

def rawReflF : Theorem := Theorem.emptyResult {x} ff

def rawAppResult : Theorem :=
  Theorem.unionResult rawReflF reflX {x} fxfx

/-- Raw APP retains a non-Boolean hypothesis even though its conclusion is an
equality. -/
example : checkApp rawReflF reflX = some rawAppResult := by
  apply (checkApp_eq_some_iff rawReflF reflX rawAppResult).mpr
  refine ⟨f, f, x, x, fx, fx, fxfx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact equalityOfSameType_semantics f f rfl
  · exact equalityOfSameType_semantics x x rfl
  · exact ⟨Examples.individual, Ty.bool,
      Ty.destFunction?_function Examples.individual Ty.bool, rfl, rfl⟩
  · exact ⟨Examples.individual, Ty.bool,
      Ty.destFunction?_function Examples.individual Ty.bool, rfl, rfl⟩
  · exact equalityOfSameType_semantics fx fx rfl
  · exact (theorem_unionResult_eq_iff_hasParts
      rawReflF reflX {x} fxfx rawAppResult).mp rfl

example : ¬ rawAppResult.sequent.IsBool := by
  intro hbool
  exact x_not_isBool (hbool.2 x (by simp [rawAppResult, rawReflF,
    Theorem.unionResult, Theorem.emptyResult]))

/-- The raw APP request with a non-Boolean premise cannot enter the verified
profile. -/
example : ¬ VerifiedInputs (.app rawReflF reflX) := by
  intro inputs
  cases inputs with
  | app leftBool rightBool =>
      exact x_not_isBool (leftBool.2 x (by
        simp [rawReflF, Theorem.emptyResult]))

def pp : CanonicalTerm := equalityOfSameType p p rfl
def reflP : Theorem := Theorem.emptyResult ∅ pp

/-- APP rejects an equality between non-functions. -/
example : checkApp reflX reflX = none := by
  rw [checkApp_eq_none_iff]
  rintro ⟨out, functionLeft, functionRight, argumentLeft, argumentRight,
    applicationLeft, applicationRight, equality, functionView, argumentView,
    leftApplication, rightApplication, construction, parts⟩
  have knownView :
      CanonicalTerm.EqualityViewSemantics reflX.sequent.concl x x :=
    equalityOfSameType_semantics x x rfl
  have hleft := functionView.unique knownView |>.1
  subst functionLeft
  rcases leftApplication with ⟨domain, codomain, hfunction, _⟩
  simp [x, individualVariable, Examples.individual,
    Ty.destFunction?] at hfunction

/-- APP rejects a function equality paired with the wrong argument domain. -/
example : checkApp reflF reflP = none := by
  rw [checkApp_eq_none_iff]
  rintro ⟨out, functionLeft, functionRight, argumentLeft, argumentRight,
    applicationLeft, applicationRight, equality, functionView, argumentView,
    leftApplication, rightApplication, construction, parts⟩
  have knownFunctionView :
      CanonicalTerm.EqualityViewSemantics reflF.sequent.concl f f :=
    equalityOfSameType_semantics f f rfl
  have knownArgumentView :
      CanonicalTerm.EqualityViewSemantics reflP.sequent.concl p p :=
    equalityOfSameType_semantics p p rfl
  have hfunctionLeft := functionView.unique knownFunctionView |>.1
  have hargumentLeft := argumentView.unique knownArgumentView |>.1
  subst functionLeft
  subst argumentLeft
  rcases leftApplication with
    ⟨domain, codomain, hfunction, hdomain, applicationShape⟩
  have hknown : f.ty.destFunction? =
      some (Examples.individual, Ty.bool) :=
    Ty.destFunction?_function Examples.individual Ty.bool
  have hpairs : (domain, codomain) = (Examples.individual, Ty.bool) :=
    Option.some.inj (hfunction.symm.trans hknown)
  cases hpairs
  simp [p, boolVariable, Examples.individual,
    Ty.bool, TypeOp.bool, Name.global] at hdomain

/-- APP rejects a theorem whose conclusion only prints like equality. -/
def impostorTheorem : Theorem :=
  Theorem.emptyResult ∅ impostorEquality

example : checkApp impostorTheorem reflP = none := by
  rw [checkApp_eq_none_iff]
  rintro ⟨out, functionLeft, functionRight, argumentLeft, argumentRight,
    applicationLeft, applicationRight, equality, functionView, argumentView,
    leftApplication, rightApplication, construction, parts⟩
  have accepted :=
    (CanonicalTerm.destEquality?_eq_some_iff _ _ _).mpr functionView
  have rejected : impostorTheorem.sequent.concl.destEquality? = none := by
    exact impostorEquality_destEquality_eq_none
  rw [rejected] at accepted
  contradiction

/-! ## DEDUCT_ANTISYM -/

def pq : CanonicalTerm := equalityOfSameType p q rfl

def deductLeft : Theorem := Theorem.emptyResult {q} p
def deductRight : Theorem := Theorem.emptyResult {p} q

def deductResult : Theorem :=
  Theorem.unionResult deductLeft deductRight
    ((deductLeft.sequent.hyp.erase deductRight.sequent.concl) ∪
      (deductRight.sequent.hyp.erase deductLeft.sequent.concl))
    pq

theorem checkDeductAntisym_bool_success :
    checkDeductAntisym deductLeft deductRight = some deductResult := by
  apply (checkDeductAntisym_eq_some_iff
    deductLeft deductRight deductResult).mpr
  exact ⟨pq, equalityOfSameType_semantics p q rfl,
    (theorem_unionResult_eq_iff_hasParts deductLeft deductRight
      ((deductLeft.sequent.hyp.erase deductRight.sequent.concl) ∪
        (deductRight.sequent.hyp.erase deductLeft.sequent.concl))
      pq deductResult).mp rfl⟩

/-- Both opposite hypotheses are discharged by canonical-set deletion. -/
example : deductResult.sequent.hyp = ∅ := by
  simp [deductResult, deductLeft, deductRight, Theorem.unionResult,
    Theorem.emptyResult, p, q]

def xy : CanonicalTerm := equalityOfSameType x y rfl
def deductIndividualLeft : Theorem := Theorem.emptyResult {y} x
def deductIndividualRight : Theorem := Theorem.emptyResult {x} y

def deductIndividualResult : Theorem :=
  Theorem.unionResult deductIndividualLeft deductIndividualRight
    ((deductIndividualLeft.sequent.hyp.erase
        deductIndividualRight.sequent.concl) ∪
      (deductIndividualRight.sequent.hyp.erase
        deductIndividualLeft.sequent.concl))
    xy

/-- Raw DEDUCT_ANTISYM accepts same-typed non-Boolean conclusions. -/
example :
    checkDeductAntisym deductIndividualLeft deductIndividualRight =
      some deductIndividualResult := by
  apply (checkDeductAntisym_eq_some_iff _ _ _).mpr
  exact ⟨xy, equalityOfSameType_semantics x y rfl,
    (theorem_unionResult_eq_iff_hasParts _ _ _ xy
      deductIndividualResult).mp rfl⟩

/-- DEDUCT_ANTISYM rejects conclusions of different types. -/
example : checkDeductAntisym deductIndividualLeft assumeP = none := by
  rw [checkDeductAntisym_eq_none_iff]
  rintro ⟨out, equality, construction, parts⟩
  apply x_not_isBool
  exact construction.1.trans p_isBool

def alphaDeductLeft : Theorem :=
  Theorem.emptyResult {canonicalIdentityY} canonicalIdentityX

def alphaDeductRight : Theorem :=
  Theorem.emptyResult {canonicalIdentityX} canonicalIdentityY

def alphaIdentityEquality : CanonicalTerm :=
  equalityOfSameType canonicalIdentityX canonicalIdentityY
    (congrArg CanonicalTerm.ty canonicalIdentityX_eq_canonicalIdentityY)

def alphaDeductResult : Theorem :=
  Theorem.unionResult alphaDeductLeft alphaDeductRight
    ((alphaDeductLeft.sequent.hyp.erase alphaDeductRight.sequent.concl) ∪
      (alphaDeductRight.sequent.hyp.erase alphaDeductLeft.sequent.concl))
    alphaIdentityEquality

/-- Binder-renamed source terms discharge as one canonical alpha class. -/
example :
    checkDeductAntisym alphaDeductLeft alphaDeductRight =
      some alphaDeductResult := by
  apply (checkDeductAntisym_eq_some_iff _ _ _).mpr
  exact ⟨alphaIdentityEquality,
    equalityOfSameType_semantics canonicalIdentityX canonicalIdentityY
      (congrArg CanonicalTerm.ty canonicalIdentityX_eq_canonicalIdentityY),
    (theorem_unionResult_eq_iff_hasParts _ _ _ alphaIdentityEquality
      alphaDeductResult).mp rfl⟩

example : alphaDeductResult.sequent.hyp = ∅ := by
  simp [alphaDeductResult, alphaDeductLeft, alphaDeductRight,
    Theorem.unionResult, Theorem.emptyResult,
    canonicalIdentityX_eq_canonicalIdentityY]

/-- Distinct AXIOM tags survive DEDUCT_ANTISYM even when hypotheses change. -/
def taggedDeductResult : Theorem :=
  Theorem.unionResult axiomP axiomQ
    ((axiomP.sequent.hyp.erase axiomQ.sequent.concl) ∪
      (axiomQ.sequent.hyp.erase axiomP.sequent.concl))
    pq

example :
    checkDeductAntisym axiomP axiomQ = some taggedDeductResult := by
  apply (checkDeductAntisym_eq_some_iff _ _ _).mpr
  exact ⟨pq, equalityOfSameType_semantics p q rfl,
    (theorem_unionResult_eq_iff_hasParts _ _ _ pq taggedDeductResult).mp rfl⟩

example : taggedDeductResult.axioms = {boolSequentP, boolSequentQ} := by
  simp [taggedDeductResult, axiomP, axiomQ, Theorem.unionResult,
    Theorem.axiomResult]

/-! ## EQ_MP -/

def equalityPQ : Theorem := Theorem.emptyResult ∅ pq

def eqMpResult : Theorem :=
  Theorem.unionResult equalityPQ assumeP {p} q

theorem checkEqMp_bool_success :
    checkEqMp equalityPQ assumeP = some eqMpResult := by
  apply (checkEqMp_eq_some_iff equalityPQ assumeP eqMpResult).mpr
  exact ⟨p, q, equalityOfSameType_semantics p q rfl, rfl,
    (theorem_unionResult_eq_iff_hasParts
      equalityPQ assumeP {p} q eqMpResult).mp rfl⟩

theorem eqMp_coreStep :
    CoreStep (.eqMp equalityPQ assumeP) eqMpResult :=
  (eqMpSemantics_iff_coreStep equalityPQ assumeP eqMpResult).mp
    ((checkEqMp_eq_some_iff equalityPQ assumeP eqMpResult).mp
      checkEqMp_bool_success)

/-- Successful checking returns a Type-valued certificate, not only a Boolean
acceptance result. -/
example :
    ∃ certificate : CertifiedCoreResult (.eqMp equalityPQ assumeP),
      checkCoreEvidence (.eqMp equalityPQ assumeP) = some certificate ∧
        certificate.1 = eqMpResult :=
  checkCoreEvidence_exists_of_step eqMp_coreStep

/-- EQ_MP rejects a premise that does not match the equality's left side. -/
example : checkEqMp equalityPQ assumeR = none := by
  rw [checkEqMp_eq_none_iff]
  rintro ⟨out, left, right, view, hmatch, parts⟩
  have knownView :
      CanonicalTerm.EqualityViewSemantics equalityPQ.sequent.concl p q :=
    equalityOfSameType_semantics p q rfl
  have hleft := view.unique knownView |>.1
  have himpossible := hleft.symm.trans hmatch
  simp [assumeR, Theorem.emptyResult, p, r, boolVariable,
    Name.global] at himpossible

/-- EQ_MP rejects a same-named defined equality head. -/
example : checkEqMp impostorTheorem assumeP = none := by
  rw [checkEqMp_eq_none_iff]
  rintro ⟨out, left, right, view, hmatch, parts⟩
  have accepted :=
    (CanonicalTerm.destEquality?_eq_some_iff _ _ _).mpr view
  have rejected : impostorTheorem.sequent.concl.destEquality? = none := by
    simpa [impostorTheorem, Theorem.emptyResult] using
      impostorEquality_destEquality_eq_none
  rw [rejected] at accepted
  contradiction

/-- EQ_MP also rejects a primitive equality head with the wrong annotation. -/
def wrongAnnotationTheorem : Theorem :=
  Theorem.emptyResult ∅ wrongAnnotationEquality

example : checkEqMp wrongAnnotationTheorem assumeP = none := by
  rw [checkEqMp_eq_none_iff]
  rintro ⟨out, left, right, view, hmatch, parts⟩
  have accepted :=
    (CanonicalTerm.destEquality?_eq_some_iff _ _ _).mpr view
  have rejected : wrongAnnotationTheorem.sequent.concl.destEquality? = none := by
    simpa [wrongAnnotationTheorem, Theorem.emptyResult] using
      wrongAnnotationEquality_destEquality_eq_none
  rw [rejected] at accepted
  contradiction

def alphaIdentityRefl : CanonicalTerm :=
  equalityOfSameType canonicalIdentityX canonicalIdentityX rfl

def alphaEqualityTheorem : Theorem :=
  Theorem.emptyResult ∅ alphaIdentityRefl

def alphaPremise : Theorem :=
  Theorem.emptyResult {canonicalIdentityY} canonicalIdentityY

def alphaEqMpResult : Theorem :=
  Theorem.unionResult alphaEqualityTheorem alphaPremise
    {canonicalIdentityY} canonicalIdentityX

/-- EQ_MP matches binder-renamed source terms through canonical alpha identity;
the raw result remains non-Boolean. -/
example : checkEqMp alphaEqualityTheorem alphaPremise = some alphaEqMpResult := by
  apply (checkEqMp_eq_some_iff _ _ _).mpr
  exact ⟨canonicalIdentityX, canonicalIdentityX,
    equalityOfSameType_semantics canonicalIdentityX canonicalIdentityX rfl,
    canonicalIdentityX_eq_canonicalIdentityY,
    (theorem_unionResult_eq_iff_hasParts _ _ _ _ alphaEqMpResult).mp rfl⟩

theorem canonicalIdentityX_not_isBool : ¬ canonicalIdentityX.IsBool := by
  intro hbool
  simp [canonicalIdentityX, CanonicalTerm.IsBool, Ty.function,
    TypeOp.function, Ty.bool, TypeOp.bool, Name.global] at hbool

example : ¬ alphaEqMpResult.sequent.IsBool := by
  intro hbool
  exact canonicalIdentityX_not_isBool hbool.1

theorem equalityPQ_isBool : equalityPQ.sequent.IsBool := by
  constructor
  · exact (equalityOfSameType_semantics p q rfl).resultIsBool
  · simp [equalityPQ, Theorem.emptyResult]

theorem assumeP_isBool : assumeP.sequent.IsBool := by
  constructor
  · exact p_isBool
  · intro hypothesis hmember
    simp [assumeP, Theorem.emptyResult] at hmember
    subst hypothesis
    exact p_isBool

theorem reflF_isBool : reflF.sequent.IsBool := by
  constructor
  · exact (equalityOfSameType_semantics f f rfl).resultIsBool
  · simp [reflF, Theorem.emptyResult]

theorem reflX_isBool : reflX.sequent.IsBool := by
  constructor
  · exact (equalityOfSameType_semantics x x rfl).resultIsBool
  · simp [reflX, Theorem.emptyResult]

theorem app_coreStep : CoreStep (.app reflF reflX) appResult :=
  (appSemantics_iff_coreStep reflF reflX appResult).mp
    ((checkApp_eq_some_iff reflF reflX appResult).mp checkApp_success)

def verifiedAppRequest : VerifiedRequest :=
  ⟨.app reflF reflX, VerifiedInputs.app reflF_isBool reflX_isBool⟩

/-- Verified APP erases to the exact raw APP result. -/
example :
    (checkVerified verifiedAppRequest).map VerifiedTheorem.raw =
      some appResult := by
  apply (checkVerified_raw_eq_some_iff verifiedAppRequest appResult).mpr
  exact app_coreStep

theorem deductLeft_isBool : deductLeft.sequent.IsBool := by
  constructor
  · exact p_isBool
  · intro hypothesis hmember
    simp [deductLeft, Theorem.emptyResult] at hmember
    subst hypothesis
    exact q_isBool

theorem deductRight_isBool : deductRight.sequent.IsBool := by
  constructor
  · exact q_isBool
  · intro hypothesis hmember
    simp [deductRight, Theorem.emptyResult] at hmember
    subst hypothesis
    exact p_isBool

theorem deductAntisym_coreStep :
    CoreStep (.deductAntisym deductLeft deductRight) deductResult :=
  (deductAntisymSemantics_iff_coreStep
      deductLeft deductRight deductResult).mp
    ((checkDeductAntisym_eq_some_iff
      deductLeft deductRight deductResult).mp
      checkDeductAntisym_bool_success)

def verifiedDeductAntisymRequest : VerifiedRequest :=
  ⟨.deductAntisym deductLeft deductRight,
    VerifiedInputs.deductAntisym deductLeft_isBool deductRight_isBool⟩

/-- Verified DEDUCT_ANTISYM erases to the exact raw result. -/
example :
    (checkVerified verifiedDeductAntisymRequest).map VerifiedTheorem.raw =
      some deductResult := by
  apply (checkVerified_raw_eq_some_iff
    verifiedDeductAntisymRequest deductResult).mpr
  exact deductAntisym_coreStep

def verifiedEqMpRequest : VerifiedRequest :=
  ⟨.eqMp equalityPQ assumeP,
    VerifiedInputs.eqMp equalityPQ_isBool assumeP_isBool⟩

/-- The verified wrapper erases to the same raw EQ_MP derivation. -/
example :
    (checkVerified verifiedEqMpRequest).map VerifiedTheorem.raw =
      some eqMpResult := by
  apply (checkVerified_raw_eq_some_iff verifiedEqMpRequest eqMpResult).mpr
  exact eqMp_coreStep

end CoreRulesFixtures

end Mettapedia.Languages.OpenTheory
