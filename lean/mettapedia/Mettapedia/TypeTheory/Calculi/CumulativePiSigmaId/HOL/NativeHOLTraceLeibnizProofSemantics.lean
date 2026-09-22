import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceMixedTermSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizDerived

/-!
# Trace semantics of the native Leibniz proof combinators

The native equality compiler does not postulate symmetry, transitivity, or
congruence.  Its emitted terms apply a Leibniz proof to an explicit predicate.
This file gives those exact terms their dependent trace denotation.

The key family equation is literal: the separated proof code for equality is
the trace product over every predicate and the corresponding implication.
Consequently a proof may be consumed by an arbitrary dependent trace family;
no bijection-only transport or proof erasure is used.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceLeibnizProofSemantics

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section Extension)
open ZFSetUniformListTraceTypeInterpretation
open NativeTraceLambdaSemantics
open NativeHOLTraceMixedTermSemantics

universe u

/-- A native term denotes some section of the canonical proof family of the
given trace-valued proposition.  The section is retained, not erased. -/
def ProofDenotes (a : ZFSet.{u}) {n : Nat} (context : Context.{u} n)
    (term : Tower.Tm n)
    (proposition : context.Environment → Prop) : Prop :=
  ∃ value : Section (ZFSetTraceProofDecoding.truthFamily proposition),
    NativeHOLTraceMixedTermSemantics.Denotes a context term
      (ZFSetTraceProofDecoding.truthFamily proposition) value

/-- Every canonical proof fibre is separated and hence has at most one
section.  This is used only after a term has independently acquired the
correct family. -/
theorem proofSection_unique {Gamma : Type (u + 1)}
    {proposition : Gamma → Prop}
    (first second : Section (ZFSetTraceProofDecoding.truthFamily proposition)) :
    first = second := by
  funext environment
  apply Subtype.ext
  have hfirst := ZFSetTraceProofDecoding.mem_truthCode
    (proposition environment)
    (first environment).1
  have hsecond := ZFSetTraceProofDecoding.mem_truthCode
    (proposition environment)
    (second environment).1
  exact hfirst.mp (first environment).2 |>.1 |>.trans
    (hsecond.mp (second environment).2 |>.1).symm

theorem ProofDenotes.change_value {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {proposition : context.Environment → Prop}
    (meaning : ProofDenotes a context term proposition)
    (value : Section (ZFSetTraceProofDecoding.truthFamily proposition)) :
    ProofDenotes a context term proposition := by
  obtain ⟨oldValue, oldMeaning⟩ := meaning
  exact ⟨value, oldMeaning.change_value (proofSection_unique oldValue value)⟩

theorem ProofDenotes.cast_proposition {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {first second : context.Environment → Prop}
    (meaning : ProofDenotes a context term first) (equal : first = second) :
    ProofDenotes a context term second := by
  cases equal
  exact meaning

theorem ProofDenotes.weaken {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {proposition : context.Environment → Prop}
    (meaning : ProofDenotes a context term proposition)
    (extension : SetFamily context.Environment) :
    ProofDenotes a (context.snoc extension) (Presentation.rename wk term)
      (fun point => proposition point.1) := by
  obtain ⟨value, termMeaning⟩ := meaning
  exact ⟨fun point => value point.1, termMeaning.weaken extension⟩

theorem proofVariableZero {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} (proposition : context.Environment → Prop) :
    ProofDenotes a
      (context.snoc (ZFSetTraceProofDecoding.truthFamily proposition)) (.var 0)
      (fun point => proposition point.1) := by
  let extended := context.snoc (ZFSetTraceProofDecoding.truthFamily proposition)
  exact ⟨fun point => point.2,
    NativeHOLTraceMixedTermSemantics.Denotes.variable (a := a) extended 0⟩

/-- Native lambda abstraction is implication introduction after the literal
trace decoder identifies implication with a dependent proof product. -/
theorem implicationIntro {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {body : Tower.Tm (n + 1)}
    (premise conclusion : context.Environment → Prop)
    (bodyMeaning : ProofDenotes a
      (context.snoc (ZFSetTraceProofDecoding.truthFamily premise)) body
      (fun point => conclusion point.1)) :
    ProofDenotes a context (.lam body)
      (fun environment => premise environment → conclusion environment) := by
  obtain ⟨value, termMeaning⟩ := bodyMeaning
  have abstracted := NativeHOLTraceMixedTermSemantics.Denotes.abstraction termMeaning
  have decoder := ZFSetTraceProofDecoding.implication_decoder premise conclusion
  exact ⟨_, abstracted.cast_family decoder.symm⟩

/-- Native application is implication elimination at the decoded trace
family. -/
theorem implicationElim {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {function argument : Tower.Tm n}
    {premise conclusion : context.Environment → Prop}
    (functionMeaning : ProofDenotes a context function
      (fun environment => premise environment → conclusion environment))
    (argumentMeaning : ProofDenotes a context argument premise) :
    ProofDenotes a context (.app function argument) conclusion := by
  obtain ⟨functionValue, functionTerm⟩ := functionMeaning
  obtain ⟨argumentValue, argumentTerm⟩ := argumentMeaning
  have decoder := ZFSetTraceProofDecoding.implication_decoder premise conclusion
  have decodedFunction := functionTerm.cast_family decoder
  exact ⟨_, NativeHOLTraceMixedTermSemantics.Denotes.application
    decodedFunction argumentTerm⟩

/-- Native abstraction over an object trace family is universal
introduction. -/
theorem universalIntro {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {body : Tower.Tm (n + 1)}
    (domain : SetFamily context.Environment)
    (proposition : Extension domain → Prop)
    (bodyMeaning : ProofDenotes a (context.snoc domain) body proposition) :
    ProofDenotes a context (.lam body)
      (fun environment => ∀ argument : Elements (domain environment),
        proposition ⟨environment, argument⟩) := by
  obtain ⟨value, termMeaning⟩ := bodyMeaning
  have abstracted := NativeHOLTraceMixedTermSemantics.Denotes.abstraction termMeaning
  have decoder := ZFSetTraceProofDecoding.forall_decoder domain proposition
  exact ⟨_, abstracted.cast_family decoder.symm⟩

/-- Applying a universally quantified proof to an independently denoted
object is universal elimination. -/
theorem universalElim {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {function argument : Tower.Tm n}
    {domain : SetFamily context.Environment}
    {proposition : Extension domain → Prop} {argumentValue : Section domain}
    (functionMeaning : ProofDenotes a context function
      (fun environment => ∀ value : Elements (domain environment),
        proposition ⟨environment, value⟩))
    (argumentMeaning : NativeHOLTraceMixedTermSemantics.Denotes a context
      argument domain argumentValue) :
    ProofDenotes a context (.app function argument)
      (fun environment => proposition ⟨environment, argumentValue environment⟩) := by
  obtain ⟨functionValue, functionTerm⟩ := functionMeaning
  have decoder := ZFSetTraceProofDecoding.forall_decoder domain proposition
  have decodedFunction := functionTerm.cast_family decoder
  exact ⟨_, NativeHOLTraceMixedTermSemantics.Denotes.application
    decodedFunction argumentMeaning⟩

/-- A fully denoted HOL object term is also a mixed native term. -/
theorem object {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {type : HOL.Ty BaseSort} {term : Tower.Tm n}
    {value : context.Environment → Value a type}
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a context term value) :
    NativeHOLTraceMixedTermSemantics.Denotes a context term
      (NativeHOLTraceDisplayedTerms.typeFamily a context type) value :=
  .object meaning

def equalityProposition {a : ZFSet.{u}} {Gamma : Type (u + 1)}
    {type : HOL.Ty BaseSort} (left right : Gamma → Value a type) : Gamma → Prop :=
  fun environment => left environment = right environment

def appliedProposition {a : ZFSet.{u}} {Gamma : Type (u + 1)}
    {type : HOL.Ty BaseSort}
    (predicate : Gamma → Value a (.arr type .prop))
    (argument : Gamma → Value a type) : Gamma → Prop :=
  fun environment => ZFSetHOLTypeInterpretation.holds
    (app (predicate environment) (argument environment))

noncomputable def leibnizFamily (a : ZFSet.{u}) {n : Nat}
    (context : Context.{u} n) (type : HOL.Ty BaseSort)
    (left right : context.Environment → Value a type) :
    SetFamily context.Environment :=
  let predicates := NativeHOLTraceDisplayedTerms.typeFamily a context (.arr type .prop)
  let premise : Extension predicates → Value a .prop :=
    fun point => app point.2 (left point.1)
  let conclusion : Extension predicates → Value a .prop :=
    fun point => app point.2 (right point.1)
  ZFSetTraceContextual.piFamily predicates
    (ZFSetTraceContextual.piFamily
      (ZFSetTraceProofDecoding.truthFamily
        (fun point => ZFSetHOLTypeInterpretation.holds (premise point)))
      (ZFSetTraceProofDecoding.truthFamily
        (fun proofPoint => ZFSetHOLTypeInterpretation.holds
          (conclusion proofPoint.1))))

/-- Full predicate quantification separates trace values. -/
theorem leibniz_extensional {a : ZFSet.{u}} {type : HOL.Ty BaseSort}
    (left right : Value a type) :
    left = right ↔ ∀ predicate : Value a (.arr type .prop),
      ZFSetHOLTypeInterpretation.holds (app predicate left) →
        ZFSetHOLTypeInterpretation.holds (app predicate right) := by
  constructor
  · intro equal predicate assumption
    simpa [equal] using assumption
  · intro transported
    let predicate : Value a (.arr type .prop) :=
      ZFSetUniformListTraceTypeInterpretation.lam
        (fun candidate => ZFSetHOLTypeInterpretation.truth (candidate = left))
    have selected := transported predicate
    have reflexive : ZFSetHOLTypeInterpretation.holds (app predicate left) := by
      simp [predicate]
    have result := selected reflexive
    have right_eq_left : right = left := by
      have applied : app predicate right =
          ZFSetHOLTypeInterpretation.truth (right = left) := by
        simp [predicate]
      rw [applied] at result
      exact ZFSetHOLTypeInterpretation.holds_truth _ |>.mp result
    exact right_eq_left.symm

/-- The proof family for equality is literally the iterated trace product
implemented by the native Leibniz operator. -/
theorem equality_decoder (a : ZFSet.{u}) {n : Nat} (context : Context.{u} n)
    (type : HOL.Ty BaseSort)
    (left right : context.Environment → Value a type) :
    ZFSetTraceProofDecoding.truthFamily (equalityProposition left right) =
      leibnizFamily a context type left right := by
  unfold equalityProposition leibnizFamily
  let predicates := NativeHOLTraceDisplayedTerms.typeFamily a context (.arr type .prop)
  let premise : Extension predicates → Value a .prop :=
    fun point => app point.2 (left point.1)
  let conclusion : Extension predicates → Value a .prop :=
    fun point => app point.2 (right point.1)
  have extensional : (fun environment => left environment = right environment) =
      fun environment =>
        ∀ predicate : Elements (predicates environment),
          ZFSetHOLTypeInterpretation.holds
              (premise ⟨environment, predicate⟩) →
            ZFSetHOLTypeInterpretation.holds
              (conclusion ⟨environment, predicate⟩) := by
    funext environment
    exact propext (by
      simpa only [premise, conclusion] using
        leibniz_extensional (left environment) (right environment))
  rw [extensional]
  change ZFSetTraceProofDecoding.truthFamily (fun environment =>
      ∀ predicate : Elements (predicates environment),
        ZFSetHOLTypeInterpretation.holds
            (premise ⟨environment, predicate⟩) →
          ZFSetHOLTypeInterpretation.holds
            (conclusion ⟨environment, predicate⟩)) =
    ZFSetTraceContextual.piFamily predicates
      (ZFSetTraceContextual.piFamily
        (ZFSetTraceProofDecoding.truthFamily
          (fun point => ZFSetHOLTypeInterpretation.holds (premise point)))
        (ZFSetTraceProofDecoding.truthFamily
          (fun proofPoint => ZFSetHOLTypeInterpretation.holds
            (conclusion proofPoint.1))))
  exact (ZFSetTraceProofDecoding.forall_decoder predicates
    (fun point => ZFSetHOLTypeInterpretation.holds (premise point) →
      ZFSetHOLTypeInterpretation.holds (conclusion point))).trans
    (congrArg (ZFSetTraceContextual.piFamily predicates)
      (ZFSetTraceProofDecoding.implication_decoder
        (fun point => ZFSetHOLTypeInterpretation.holds (premise point))
        (fun point => ZFSetHOLTypeInterpretation.holds (conclusion point))))

/-- The exact two-lambda term emitted for equality reflexivity denotes the
canonical equality proof family. -/
theorem reflTerm_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {type : HOL.Ty BaseSort}
    (left : context.Environment → Value a type) :
    ProofDenotes a context FormationSensitiveHOLLeibnizDerived.reflTerm
      (equalityProposition left left) := by
  let predicates := NativeHOLTraceDisplayedTerms.typeFamily a context (.arr type .prop)
  let premise : Extension predicates → Value a .prop :=
    fun point => app point.2 (left point.1)
  have variableMeaning : NativeHOLTraceMixedTermSemantics.Denotes a
      ((context.snoc predicates).snoc
        (ZFSetTraceProofDecoding.truthFamily
          (fun point => ZFSetHOLTypeInterpretation.holds (premise point)))) (.var 0)
      (ZFSetTraceProofDecoding.truthFamily (fun point =>
        ZFSetHOLTypeInterpretation.holds (premise point.1)))
      (fun point => point.2) :=
    .variable _ 0
  have inner := NativeHOLTraceMixedTermSemantics.Denotes.abstraction variableMeaning
  have outer := NativeHOLTraceMixedTermSemantics.Denotes.abstraction inner
  have decoded := equality_decoder a context type left left
  change NativeHOLTraceMixedTermSemantics.Denotes a context
    FormationSensitiveHOLLeibnizDerived.reflTerm
    (leibnizFamily a context type left left) _ at outer
  have casted := outer.cast_family decoded.symm
  exact ⟨_, by
    simpa only [FormationSensitiveHOLLeibnizDerived.reflTerm] using casted⟩

/-- Reflexivity also proves an equality whose endpoints have already been
shown equal by the surrounding object semantics. -/
theorem reflTerm_denotes_of_equal {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {type : HOL.Ty BaseSort}
    {left right : context.Environment → Value a type}
    (equal : left = right) :
    ProofDenotes a context FormationSensitiveHOLLeibnizDerived.reflTerm
      (equalityProposition left right) := by
  cases equal
  exact reflTerm_denotes left

/-- Leibniz elimination for the actual native application tree.  The chosen
predicate is an independently denoted object term, and the result is the
same proof witness transported to the predicate at the right endpoint. -/
theorem eliminate {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {type : HOL.Ty BaseSort} {left right : context.Environment → Value a type}
    {comparison predicateTerm input : Tower.Tm n}
    {predicate : context.Environment → Value a (.arr type .prop)}
    (equalityMeaning : ProofDenotes a context comparison
      (equalityProposition left right))
    (predicateMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      predicateTerm predicate)
    (inputMeaning : ProofDenotes a context input
      (appliedProposition predicate left)) :
    ProofDenotes a context (.app (.app comparison predicateTerm) input)
      (appliedProposition predicate right) := by
  obtain ⟨equalityValue, equalityTerm⟩ := equalityMeaning
  obtain ⟨inputValue, inputTermMeaning⟩ := inputMeaning
  have decoded := equality_decoder a context type left right
  have equalityAsFunction := equalityTerm.cast_family decoded
  change NativeHOLTraceMixedTermSemantics.Denotes a context comparison
    (leibnizFamily a context type left right) _ at equalityAsFunction
  unfold leibnizFamily at equalityAsFunction
  have atPredicate := NativeHOLTraceMixedTermSemantics.Denotes.application
    equalityAsFunction (object predicateMeaning)
  change NativeHOLTraceMixedTermSemantics.Denotes a context
    (.app comparison predicateTerm)
    (ZFSetTraceContextual.piFamily
      (ZFSetTraceProofDecoding.truthFamily
        (appliedProposition predicate left))
      (ZFSetTraceProofDecoding.truthFamily
        (fun point => appliedProposition predicate right point.1))) _ at atPredicate
  have atInput := NativeHOLTraceMixedTermSemantics.Denotes.application
    atPredicate inputTermMeaning
  change NativeHOLTraceMixedTermSemantics.Denotes a context
    (.app (.app comparison predicateTerm) input)
    (ZFSetTraceProofDecoding.truthFamily
      (appliedProposition predicate right)) _ at atInput
  exact ⟨_, atInput⟩

/-- Specializing equality to a predicate produces the actual implication
proof emitted by proposition transport. -/
theorem specialize {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {type : HOL.Ty BaseSort} {left right : context.Environment → Value a type}
    {comparison predicateTerm : Tower.Tm n}
    {predicate : context.Environment → Value a (.arr type .prop)}
    (equalityMeaning : ProofDenotes a context comparison
      (equalityProposition left right))
    (predicateMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      predicateTerm predicate) :
    ProofDenotes a context (.app comparison predicateTerm)
      (fun environment => appliedProposition predicate left environment →
        appliedProposition predicate right environment) := by
  obtain ⟨equalityValue, equalityTerm⟩ := equalityMeaning
  have decoded := equality_decoder a context type left right
  have equalityAsFunction := equalityTerm.cast_family decoded
  change NativeHOLTraceMixedTermSemantics.Denotes a context comparison
    (leibnizFamily a context type left right) _ at equalityAsFunction
  unfold leibnizFamily at equalityAsFunction
  have atPredicate := NativeHOLTraceMixedTermSemantics.Denotes.application
    equalityAsFunction (object predicateMeaning)
  change NativeHOLTraceMixedTermSemantics.Denotes a context
    (.app comparison predicateTerm)
    (ZFSetTraceContextual.piFamily
      (ZFSetTraceProofDecoding.truthFamily
        (appliedProposition predicate left))
      (ZFSetTraceProofDecoding.truthFamily
        (fun point => appliedProposition predicate right point.1))) _ at atPredicate
  have implication := ZFSetTraceProofDecoding.implication_decoder
    (appliedProposition predicate left) (appliedProposition predicate right)
  have decodedTerm := atPredicate.cast_family implication.symm
  exact ⟨_, decodedTerm⟩

/-- The native implication spelling has its source trace truth value. -/
theorem rawImp_denotes {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {leftTerm rightTerm : Tower.Tm n}
    {left right : context.Environment → Value a .prop}
    (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left)
    (rightMeaning : NativeHOLTraceDisplayedTerms.Denotes a context rightTerm right) :
    NativeHOLTraceDisplayedTerms.Denotes a context (type := .prop)
      (FormationSensitiveHOLUniformList.rawImp leftTerm rightTerm)
      (fun environment => ZFSetHOLTypeInterpretation.truth
        (ZFSetHOLTypeInterpretation.holds (left environment) →
          ZFSetHOLTypeInterpretation.holds (right environment))) := by
  have applied := NativeHOLTraceDisplayedTerms.Denotes.application
    (NativeHOLTraceDisplayedTerms.Denotes.application
      (NativeHOLTraceDisplayedTerms.Denotes.implication (a := a)) leftMeaning)
    rightMeaning
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value applied
  funext environment
  exact NativeHOLUniformListTraceRepresentation.implicationValue_apply
    (left environment) (right environment)

/-- The native universal spelling has its source trace truth value. -/
theorem rawAll_denotes {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    (type : HOL.Ty BaseSort) {body : Tower.Tm (n + 1)}
    {bodyValue : (context.snoc
      (NativeHOLTraceDisplayedTerms.typeFamily a context type)).Environment →
        Value a .prop}
    (bodyMeaning : NativeHOLTraceDisplayedTerms.Denotes a
      (context.snoc (NativeHOLTraceDisplayedTerms.typeFamily a context type))
      body bodyValue) :
    NativeHOLTraceDisplayedTerms.Denotes a context (type := .prop)
      (FormationSensitiveHOLUniformList.rawAll type body)
      (fun environment => ZFSetHOLTypeInterpretation.truth
        (∀ argument : Value a type,
          ZFSetHOLTypeInterpretation.holds (bodyValue ⟨environment, argument⟩))) := by
  have predicate := NativeHOLTraceDisplayedTerms.Denotes.abstraction bodyMeaning
  have applied := NativeHOLTraceDisplayedTerms.Denotes.application
    (NativeHOLTraceDisplayedTerms.Denotes.universal (a := a) (context := context) type)
    predicate
  have lifted : (liftClosed (FormationSensitiveHOLUniformList.universal type) :
      Tower.Tm n) =
      .app (.const `HOLUniformList.universal)
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n type) := by
    simp only [FormationSensitiveHOLUniformList.universal, liftClosed,
      Presentation.rename, FormationSensitiveHOLInterface.typeAt_rename]
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value
    (by simpa only [FormationSensitiveHOLUniformList.rawAll, lifted] using applied)
  funext environment
  rw [NativeHOLUniformListTraceRepresentation.universalValue_apply]
  apply congrArg ZFSetHOLTypeInterpretation.truth
  apply propext
  simp only [ZFSetUniformListTraceTypeInterpretation.app_lam]

/-- The computed body of the native Leibniz operator denotes literal
equality, independently of the proof term that may inhabit it. -/
theorem rawLeibniz_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {type : HOL.Ty BaseSort}
    {leftTerm rightTerm : Tower.Tm n}
    {left right : context.Environment → Value a type}
    (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left)
    (rightMeaning : NativeHOLTraceDisplayedTerms.Denotes a context rightTerm right) :
    NativeHOLTraceDisplayedTerms.Denotes a context (type := .prop)
      (FormationSensitiveHOLLeibnizInterface.rawLeibniz type leftTerm rightTerm)
      (fun environment => ZFSetHOLTypeInterpretation.truth
        (left environment = right environment)) := by
  let predicates := NativeHOLTraceDisplayedTerms.typeFamily a context (.arr type .prop)
  let extended := context.snoc predicates
  have predicateVariable : NativeHOLTraceDisplayedTerms.Denotes a extended (.var 0)
      (fun point => point.2) :=
    .variable 0 (NativeTraceLambdaSemantics.Denotes.var extended 0)
  have leftApplication := NativeHOLTraceDisplayedTerms.Denotes.application
    predicateVariable (leftMeaning.weaken predicates)
  have rightApplication := NativeHOLTraceDisplayedTerms.Denotes.application
    predicateVariable (rightMeaning.weaken predicates)
  have implication := rawImp_denotes leftApplication rightApplication
  have quantified := rawAll_denotes (.arr type .prop) implication
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value
    (by simpa [FormationSensitiveHOLLeibnizInterface.rawLeibniz] using quantified)
  funext environment
  apply congrArg ZFSetHOLTypeInterpretation.truth
  apply propext
  constructor
  · intro transported
    apply (leibniz_extensional (left environment) (right environment)).mpr
    intro predicate assumption
    exact transported predicate.1 predicate.2 assumption
  · intro equal predicate member assumption
    exact (leibniz_extensional (left environment) (right environment)).mp equal
      ⟨predicate, member⟩ assumption

/-- The predicate used by native symmetry: a candidate is equal to the
original left endpoint. -/
theorem rightEqualityPredicate_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {type : HOL.Ty BaseSort}
    {leftTerm : Tower.Tm n} {left : context.Environment → Value a type}
    (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left) :
    NativeHOLTraceDisplayedTerms.Denotes a context (type := .arr type .prop)
      (.lam (FormationSensitiveHOLLeibnizInterface.rawLeibniz type
        (.var 0) (Presentation.rename wk leftTerm)))
      (fun environment => ZFSetUniformListTraceTypeInterpretation.lam
        (fun candidate => ZFSetHOLTypeInterpretation.truth
          (candidate = left environment))) := by
  let domain := NativeHOLTraceDisplayedTerms.typeFamily a context type
  let extended := context.snoc domain
  let bodyValue : extended.Environment → Value a .prop :=
    fun point => ZFSetHOLTypeInterpretation.truth (point.2 = left point.1)
  have candidate : NativeHOLTraceDisplayedTerms.Denotes a extended (.var 0)
      (fun point => point.2) :=
    .variable 0 (NativeTraceLambdaSemantics.Denotes.var extended 0)
  have comparison : NativeHOLTraceDisplayedTerms.Denotes a extended
      (type := .prop)
      (FormationSensitiveHOLLeibnizInterface.rawLeibniz type
        (.var 0) (Presentation.rename wk leftTerm)) bodyValue :=
    rawLeibniz_denotes candidate (leftMeaning.weaken domain)
  have abstracted := NativeHOLTraceDisplayedTerms.Denotes.abstraction comparison
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value abstracted
  rfl

/-- The predicate used by native transitivity: the original left endpoint is
equal to a candidate. -/
theorem leftEqualityPredicate_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {type : HOL.Ty BaseSort}
    {leftTerm : Tower.Tm n} {left : context.Environment → Value a type}
    (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left) :
    NativeHOLTraceDisplayedTerms.Denotes a context (type := .arr type .prop)
      (.lam (FormationSensitiveHOLLeibnizInterface.rawLeibniz type
        (Presentation.rename wk leftTerm) (.var 0)))
      (fun environment => ZFSetUniformListTraceTypeInterpretation.lam
        (fun candidate => ZFSetHOLTypeInterpretation.truth
          (left environment = candidate))) := by
  let domain := NativeHOLTraceDisplayedTerms.typeFamily a context type
  let extended := context.snoc domain
  let bodyValue : extended.Environment → Value a .prop :=
    fun point => ZFSetHOLTypeInterpretation.truth (left point.1 = point.2)
  have candidate : NativeHOLTraceDisplayedTerms.Denotes a extended (.var 0)
      (fun point => point.2) :=
    .variable 0 (NativeTraceLambdaSemantics.Denotes.var extended 0)
  have comparison : NativeHOLTraceDisplayedTerms.Denotes a extended
      (type := .prop)
      (FormationSensitiveHOLLeibnizInterface.rawLeibniz type
        (Presentation.rename wk leftTerm) (.var 0)) bodyValue :=
    rawLeibniz_denotes (leftMeaning.weaken domain) candidate
  have abstracted := NativeHOLTraceDisplayedTerms.Denotes.abstraction comparison
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value abstracted
  rfl

/-- The predicate used by argument congruence compares the fixed application
with application to the candidate argument. -/
theorem congruencePredicate_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {domain result : HOL.Ty BaseSort}
    {functionTerm argumentTerm : Tower.Tm n}
    {functionValue : context.Environment → Value a (.arr domain result)}
    {argumentValue : context.Environment → Value a domain}
    (functionMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      functionTerm functionValue)
    (argumentMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      argumentTerm argumentValue) :
    NativeHOLTraceDisplayedTerms.Denotes a context (type := .arr domain .prop)
      (.lam (FormationSensitiveHOLLeibnizInterface.rawLeibniz result
        (Presentation.rename wk (.app functionTerm argumentTerm))
        (.app (Presentation.rename wk functionTerm) (.var 0))))
      (fun environment => ZFSetUniformListTraceTypeInterpretation.lam
        (fun candidate => ZFSetHOLTypeInterpretation.truth
          (app (functionValue environment) (argumentValue environment) =
            app (functionValue environment) candidate))) := by
  let argumentFamily := NativeHOLTraceDisplayedTerms.typeFamily a context domain
  let extended := context.snoc argumentFamily
  let fixedApplication : context.Environment → Value a result :=
    fun environment => app (functionValue environment) (argumentValue environment)
  let bodyValue : extended.Environment → Value a .prop :=
    fun point => ZFSetHOLTypeInterpretation.truth
      (fixedApplication point.1 = app (functionValue point.1) point.2)
  have fixedMeaning := NativeHOLTraceDisplayedTerms.Denotes.application
    functionMeaning argumentMeaning
  have candidate : NativeHOLTraceDisplayedTerms.Denotes a extended (.var 0)
      (fun point => point.2) :=
    .variable 0 (NativeTraceLambdaSemantics.Denotes.var extended 0)
  have candidateApplication := NativeHOLTraceDisplayedTerms.Denotes.application
    (functionMeaning.weaken argumentFamily) candidate
  have comparison : NativeHOLTraceDisplayedTerms.Denotes a extended
      (type := .prop)
      (FormationSensitiveHOLLeibnizInterface.rawLeibniz result
        (Presentation.rename wk (.app functionTerm argumentTerm))
        (.app (Presentation.rename wk functionTerm) (.var 0))) bodyValue :=
    rawLeibniz_denotes (fixedMeaning.weaken argumentFamily) candidateApplication
  have abstracted := NativeHOLTraceDisplayedTerms.Denotes.abstraction comparison
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value abstracted
  rfl

/-- The predicate used by function congruence compares the fixed application
with application of the candidate function to the fixed argument. -/
theorem functionCongruencePredicate_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {domain result : HOL.Ty BaseSort}
    {functionTerm argumentTerm : Tower.Tm n}
    {functionValue : context.Environment → Value a (.arr domain result)}
    {argumentValue : context.Environment → Value a domain}
    (functionMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      functionTerm functionValue)
    (argumentMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      argumentTerm argumentValue) :
    NativeHOLTraceDisplayedTerms.Denotes a context
      (type := .arr (.arr domain result) .prop)
      (.lam (FormationSensitiveHOLLeibnizInterface.rawLeibniz result
        (Presentation.rename wk (.app functionTerm argumentTerm))
        (.app (.var 0) (Presentation.rename wk argumentTerm))))
      (fun environment => ZFSetUniformListTraceTypeInterpretation.lam
        (fun candidate => ZFSetHOLTypeInterpretation.truth
          (app (functionValue environment) (argumentValue environment) =
            app candidate (argumentValue environment)))) := by
  let functionFamily := NativeHOLTraceDisplayedTerms.typeFamily a context
    (.arr domain result)
  let extended := context.snoc functionFamily
  let fixedApplication : context.Environment → Value a result :=
    fun environment => app (functionValue environment) (argumentValue environment)
  let bodyValue : extended.Environment → Value a .prop :=
    fun point => ZFSetHOLTypeInterpretation.truth
      (fixedApplication point.1 = app point.2 (argumentValue point.1))
  have fixedMeaning := NativeHOLTraceDisplayedTerms.Denotes.application
    functionMeaning argumentMeaning
  have candidate : NativeHOLTraceDisplayedTerms.Denotes a extended (.var 0)
      (fun point => point.2) :=
    .variable 0 (NativeTraceLambdaSemantics.Denotes.var extended 0)
  have candidateApplication := NativeHOLTraceDisplayedTerms.Denotes.application
    candidate (argumentMeaning.weaken functionFamily)
  have comparison : NativeHOLTraceDisplayedTerms.Denotes a extended
      (type := .prop)
      (FormationSensitiveHOLLeibnizInterface.rawLeibniz result
        (Presentation.rename wk (.app functionTerm argumentTerm))
        (.app (.var 0) (Presentation.rename wk argumentTerm))) bodyValue :=
    rawLeibniz_denotes (fixedMeaning.weaken functionFamily) candidateApplication
  have abstracted := NativeHOLTraceDisplayedTerms.Denotes.abstraction comparison
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value abstracted
  rfl

/-- The exact native symmetry combinator preserves literal trace equality. -/
theorem symmetry_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {type : HOL.Ty BaseSort}
    {leftTerm comparison : Tower.Tm n}
    {left right : context.Environment → Value a type}
    (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left)
    (comparisonMeaning : ProofDenotes a context comparison
      (equalityProposition left right)) :
    ProofDenotes a context
      (FormationSensitiveHOLLeibnizDerived.symmetry type leftTerm comparison)
      (equalityProposition right left) := by
  let predicate : context.Environment → Value a (.arr type .prop) :=
    fun environment => ZFSetUniformListTraceTypeInterpretation.lam
      (fun candidate => ZFSetHOLTypeInterpretation.truth
        (candidate = left environment))
  have predicateMeaning := rightEqualityPredicate_denotes leftMeaning
  have reflexive := reflTerm_denotes (a := a) left
  have reflexiveAtPredicate : ProofDenotes a context
      FormationSensitiveHOLLeibnizDerived.reflTerm
      (appliedProposition predicate left) := by
    apply ProofDenotes.cast_proposition reflexive
    funext environment
    apply propext
    simp [appliedProposition, predicate, equalityProposition]
  have transported := eliminate comparisonMeaning predicateMeaning
    reflexiveAtPredicate
  apply ProofDenotes.cast_proposition
    (by simpa only [FormationSensitiveHOLLeibnizDerived.symmetry] using transported)
  funext environment
  apply propext
  simp [appliedProposition, equalityProposition]

/-- The exact native transitivity combinator preserves literal trace
equality. -/
theorem transitivity_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {type : HOL.Ty BaseSort}
    {leftTerm first second : Tower.Tm n}
    {left middle right : context.Environment → Value a type}
    (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left)
    (firstMeaning : ProofDenotes a context first
      (equalityProposition left middle))
    (secondMeaning : ProofDenotes a context second
      (equalityProposition middle right)) :
    ProofDenotes a context
      (FormationSensitiveHOLLeibnizDerived.transitivity type leftTerm first second)
      (equalityProposition left right) := by
  let predicate : context.Environment → Value a (.arr type .prop) :=
    fun environment => ZFSetUniformListTraceTypeInterpretation.lam
      (fun candidate => ZFSetHOLTypeInterpretation.truth
        (left environment = candidate))
  have predicateMeaning := leftEqualityPredicate_denotes leftMeaning
  have firstAtPredicate : ProofDenotes a context first
      (appliedProposition predicate middle) := by
    apply ProofDenotes.cast_proposition firstMeaning
    funext environment
    apply propext
    simp [appliedProposition, predicate, equalityProposition]
  have transported := eliminate secondMeaning predicateMeaning firstAtPredicate
  apply ProofDenotes.cast_proposition
    (by simpa only [FormationSensitiveHOLLeibnizDerived.transitivity] using transported)
  funext environment
  apply propext
  simp [appliedProposition, equalityProposition]

/-- The exact native argument-congruence combinator transports equality
through an independently denoted function. -/
theorem congruence_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {domain result : HOL.Ty BaseSort}
    {functionTerm argumentTerm comparison : Tower.Tm n}
    {functionValue : context.Environment → Value a (.arr domain result)}
    {left right : context.Environment → Value a domain}
    (functionMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      functionTerm functionValue)
    (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context argumentTerm left)
    (comparisonMeaning : ProofDenotes a context comparison
      (equalityProposition left right)) :
    ProofDenotes a context
      (FormationSensitiveHOLLeibnizDerived.congruence result
        functionTerm argumentTerm comparison)
      (equalityProposition
        (fun environment => app (functionValue environment) (left environment))
        (fun environment => app (functionValue environment) (right environment))) := by
  let leftImage : context.Environment → Value a result :=
    fun environment => app (functionValue environment) (left environment)
  let predicate : context.Environment → Value a (.arr domain .prop) :=
    fun environment => ZFSetUniformListTraceTypeInterpretation.lam
      (fun candidate => ZFSetHOLTypeInterpretation.truth
        (leftImage environment = app (functionValue environment) candidate))
  have predicateMeaning := congruencePredicate_denotes functionMeaning leftMeaning
  have reflexive := reflTerm_denotes (a := a) leftImage
  have reflexiveAtPredicate : ProofDenotes a context
      FormationSensitiveHOLLeibnizDerived.reflTerm
      (appliedProposition predicate left) := by
    apply ProofDenotes.cast_proposition reflexive
    funext environment
    apply propext
    simp [appliedProposition, predicate, equalityProposition, leftImage]
  have transported := eliminate comparisonMeaning predicateMeaning
    reflexiveAtPredicate
  apply ProofDenotes.cast_proposition
    (by simpa only [FormationSensitiveHOLLeibnizDerived.congruence] using transported)
  funext environment
  apply propext
  simp [appliedProposition, equalityProposition]

/-- The exact native function-congruence combinator transports equality
through application to an independently denoted argument. -/
theorem functionCongruence_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {domain result : HOL.Ty BaseSort}
    {functionTerm argumentTerm comparison : Tower.Tm n}
    {left right : context.Environment → Value a (.arr domain result)}
    {argumentValue : context.Environment → Value a domain}
    (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      functionTerm left)
    (argumentMeaning : NativeHOLTraceDisplayedTerms.Denotes a context
      argumentTerm argumentValue)
    (comparisonMeaning : ProofDenotes a context comparison
      (equalityProposition left right)) :
    ProofDenotes a context
      (FormationSensitiveHOLLeibnizDerived.functionCongruence result
        functionTerm argumentTerm comparison)
      (equalityProposition
        (fun environment => app (left environment) (argumentValue environment))
        (fun environment => app (right environment) (argumentValue environment))) := by
  let leftImage : context.Environment → Value a result :=
    fun environment => app (left environment) (argumentValue environment)
  let predicate : context.Environment → Value a (.arr (.arr domain result) .prop) :=
    fun environment => ZFSetUniformListTraceTypeInterpretation.lam
      (fun candidate => ZFSetHOLTypeInterpretation.truth
        (leftImage environment = app candidate (argumentValue environment)))
  have predicateMeaning := functionCongruencePredicate_denotes
    leftMeaning argumentMeaning
  have reflexive := reflTerm_denotes (a := a) leftImage
  have reflexiveAtPredicate : ProofDenotes a context
      FormationSensitiveHOLLeibnizDerived.reflTerm
      (appliedProposition predicate left) := by
    apply ProofDenotes.cast_proposition reflexive
    funext environment
    apply propext
    simp [appliedProposition, predicate, equalityProposition, leftImage]
  have transported := eliminate comparisonMeaning predicateMeaning
    reflexiveAtPredicate
  apply ProofDenotes.cast_proposition
    (by simpa only [FormationSensitiveHOLLeibnizDerived.functionCongruence]
      using transported)
  funext environment
  apply propext
  simp [appliedProposition, equalityProposition]

noncomputable def propositionIdentity (a : ZFSet.{u}) :
    Value a (.arr .prop .prop) :=
  ZFSetUniformListTraceTypeInterpretation.lam
    (fun proposition : Value a .prop => proposition)

@[simp] theorem app_propositionIdentity (a : ZFSet.{u})
    (proposition : Value a .prop) :
    app (propositionIdentity a) proposition = proposition := by
  simp [propositionIdentity]

/-- The identity predicate on propositions has the exact native one-lambda
representation used by proposition transport. -/
theorem propositionIdentityPredicate_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} :
    NativeHOLTraceDisplayedTerms.Denotes a context
      (type := .arr .prop .prop) ((.lam (.var 0)) : Tower.Tm n)
      (fun (_ : context.Environment) => propositionIdentity a) := by
  let domain := NativeHOLTraceDisplayedTerms.typeFamily a context .prop
  have variableMeaning : NativeHOLTraceDisplayedTerms.Denotes a (context.snoc domain)
      (type := .prop) (.var (0 : Fin (n + 1))) (fun point => point.2) :=
    .variable 0 (NativeTraceLambdaSemantics.Denotes.var _ 0)
  simpa only [propositionIdentity] using
    (NativeHOLTraceDisplayedTerms.Denotes.abstraction
      (domain := .prop) (codomain := .prop) variableMeaning)

/-- Specializing equality of propositions to the identity predicate yields
the exact native forward-implication proof. -/
theorem propForward_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {comparison : Tower.Tm n}
    {left right : context.Environment → Value a .prop}
    (comparisonMeaning : ProofDenotes a context comparison
      (equalityProposition left right)) :
    ProofDenotes a context
      (FormationSensitiveHOLLeibnizDerived.propForward comparison)
      (fun environment => ZFSetHOLTypeInterpretation.holds (left environment) →
        ZFSetHOLTypeInterpretation.holds (right environment)) := by
  let predicate : context.Environment → Value a (.arr .prop .prop) :=
    fun _ => propositionIdentity a
  have specialized := specialize comparisonMeaning
    (propositionIdentityPredicate_denotes (a := a) (context := context))
  apply ProofDenotes.cast_proposition
    (by simpa only [FormationSensitiveHOLLeibnizDerived.propForward]
      using specialized)
  funext environment
  apply propext
  simp [appliedProposition, propositionIdentity]

namespace Controls

theorem reflexivity_has_trace_proof (a : ZFSet.{u})
    (x : Value a element) :
    ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext
      FormationSensitiveHOLLeibnizDerived.reflTerm
      (equalityProposition (fun _ => x) (fun _ => x)) :=
  reflTerm_denotes (fun _ => x)

end Controls

#print axioms proofSection_unique
#print axioms implicationIntro
#print axioms implicationElim
#print axioms universalIntro
#print axioms universalElim
#print axioms equality_decoder
#print axioms reflTerm_denotes
#print axioms symmetry_denotes
#print axioms transitivity_denotes
#print axioms congruence_denotes
#print axioms functionCongruence_denotes
#print axioms propForward_denotes
#print axioms Controls.reflexivity_has_trace_proof

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceLeibnizProofSemantics
