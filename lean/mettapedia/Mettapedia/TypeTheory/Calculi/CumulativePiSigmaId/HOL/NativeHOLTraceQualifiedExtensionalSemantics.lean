import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceExtensionalCompilerSemantics

/-!
# Compositional trace semantics for qualified extensional proof terms

The constructive mixed-term semantics is closed under variables, represented
HOL objects, abstraction, and application.  The qualified extensional
compiler additionally emits two fully applied opaque proof constants.  A
root-only judgment is enough when either constant is the outermost node, but
not when its result is abstracted, applied, or consumed by a later proof rule.

`Denotes` is the least compositional extension of the mixed-term judgment by
those two qualified nodes.  The new constructors retain their actual premise
terms and the canonical Aczel-trace proof sections.  Partial applications of
the opaque constants acquire no meaning here.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceQualifiedExtensionalSemantics

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section Extension)
open ZFSetUniformListTraceTypeInterpretation
open NativeTraceLambdaSemantics NativeTraceContextMorphisms
open NativeTraceDisplayedSubstitution
open NativeHOLTraceLeibnizProofSemantics
open FormationSensitiveHOLExtensionalApplications

universe u

/-- The least mixed native-term semantics closed under the two fully applied,
qualified extensional proof constants. -/
inductive Denotes (a : ZFSet.{u}) : {n : Nat} → (context : Context.{u} n) →
    (term : Tower.Tm n) → (family : SetFamily context.Environment) →
      Section family → Prop where
  | mixed {n : Nat} {context : Context.{u} n} {term : Tower.Tm n}
      {family : SetFamily context.Environment} {value : Section family}
      (meaning : NativeHOLTraceMixedTermSemantics.Denotes a context term family value) :
      Denotes a context term family value
  | abstraction {n : Nat} {context : Context.{u} n}
      {domain : SetFamily context.Environment}
      {codomain : SetFamily (Extension domain)} {body : Tower.Tm (n + 1)}
      {bodyValue : Section codomain} :
      Denotes a (context.snoc domain) body codomain bodyValue →
      Denotes a context (.lam body) (ZFSetTraceContextual.piFamily domain codomain)
        (ZFSetTraceContextual.lam bodyValue)
  | application {n : Nat} {context : Context.{u} n}
      {domain : SetFamily context.Environment}
      {codomain : SetFamily (Extension domain)} {function argument : Tower.Tm n}
      {functionValue : Section (ZFSetTraceContextual.piFamily domain codomain)}
      {argumentValue : Section domain} :
      Denotes a context function (ZFSetTraceContextual.piFamily domain codomain)
          functionValue →
      Denotes a context argument domain argumentValue →
      Denotes a context (.app function argument)
        (fun environment => codomain ⟨environment, argumentValue environment⟩)
        (ZFSetTraceContextual.app functionValue argumentValue)
  | propositionExtensionality {n : Nat} {context : Context.{u} n}
      {leftTerm rightTerm forwardTerm backwardTerm : Tower.Tm n}
      {left right : context.Environment → Value a .prop}
      {forwardValue : Section (ZFSetTraceProofDecoding.truthFamily
        (fun environment => ZFSetHOLTypeInterpretation.holds (left environment) →
          ZFSetHOLTypeInterpretation.holds (right environment)))}
      {backwardValue : Section (ZFSetTraceProofDecoding.truthFamily
        (fun environment => ZFSetHOLTypeInterpretation.holds (right environment) →
          ZFSetHOLTypeInterpretation.holds (left environment)))}
      (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left)
      (rightMeaning : NativeHOLTraceDisplayedTerms.Denotes a context rightTerm right)
      (forwardMeaning : Denotes a context forwardTerm _ forwardValue)
      (backwardMeaning : Denotes a context backwardTerm _ backwardValue) :
      Denotes a context
        (propositionExtensionalityApp leftTerm rightTerm forwardTerm backwardTerm)
        (ZFSetTraceProofDecoding.truthFamily (equalityProposition left right))
        (NativeHOLTraceExtensionalRuleSemantics.propositionExtensionalitySection
          left right
          (fun environment =>
            (ZFSetTraceProofDecoding.mem_truthCode _ _).mp
              (forwardValue environment).2 |>.2)
          (fun environment =>
            (ZFSetTraceProofDecoding.mem_truthCode _ _).mp
              (backwardValue environment).2 |>.2))
  | functionExtensionality {n : Nat} {context : Context.{u} n}
      {domain codomain : HOL.Ty BaseSort}
      {domainTerm codomainTerm leftTerm rightTerm pointwiseTerm : Tower.Tm n}
      {left right : context.Environment → Value a (.arr domain codomain)}
      {pointwiseValue : Section (ZFSetTraceProofDecoding.truthFamily
        (fun environment => ∀ argument : Value a domain,
          app (left environment) argument = app (right environment) argument))}
      (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left)
      (rightMeaning : NativeHOLTraceDisplayedTerms.Denotes a context rightTerm right)
      (pointwiseMeaning : Denotes a context pointwiseTerm _ pointwiseValue) :
      Denotes a context
        (functionExtensionalityApp domainTerm codomainTerm leftTerm rightTerm pointwiseTerm)
        (ZFSetTraceProofDecoding.truthFamily (equalityProposition left right))
        (NativeHOLTraceExtensionalRuleSemantics.functionExtensionalitySection
          left right
          (fun environment argument =>
            (ZFSetTraceProofDecoding.mem_truthCode _ _).mp
              (pointwiseValue environment).2 |>.2 argument))

theorem Denotes.cast_family {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {first second : SetFamily context.Environment} {value : Section first}
    (meaning : Denotes a context term first value) (equal : first = second) :
    Denotes a context term second
      (castSection equal value) := by
  cases equal
  exact meaning

theorem Denotes.change_value {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {family : SetFamily context.Environment} {first second : Section family}
    (meaning : Denotes a context term family first) (equal : first = second) :
    Denotes a context term family second := by
  cases equal
  exact meaning

/-- Qualified denotation commutes with displayed renaming.  The extensional
sections are re-created at the new environment and then identified by proof
fibre separation. -/
theorem Denotes.rename {a : ZFSet.{u}} {n : Nat} {source : Context.{u} n}
    {term : Tower.Tm n} {family : SetFamily source.Environment}
    {value : Section family} (meaning : Denotes a source term family value)
    {m : Nat} {target : Context.{u} m} {rho : Ren n m}
    {morphism : Morphism source target}
    (displayed : NativeTraceDisplayedSubstitution.Renaming source target rho morphism) :
    Denotes a target (Presentation.rename rho term)
      (morphism.reindexFamily family) (morphism.reindexSection value) := by
  induction meaning generalizing m with
  | mixed meaning => exact .mixed (meaning.rename displayed)
  | @abstraction n context domain codomain body bodyValue bodyMeaning ih =>
      exact .abstraction (ih (displayed.lift domain))
  | @application n context domain codomain function argument functionValue argumentValue
      functionMeaning argumentMeaning functionInduction argumentInduction =>
      have functionMoved := functionInduction displayed
      have argumentMoved := argumentInduction displayed
      have functionForApplication :
          Denotes a target (Presentation.rename rho function)
            (ZFSetTraceContextual.piFamily (morphism.reindexFamily domain)
              (codomain ∘ (morphism.lift domain).environment))
            (morphism.reindexSection functionValue) :=
        functionMoved.cast_family (by rfl)
      exact .application functionForApplication argumentMoved
  | propositionExtensionality leftMeaning rightMeaning forwardMeaning backwardMeaning
      forwardInduction backwardInduction =>
      have leftMoved := leftMeaning.rename displayed
      have rightMoved := rightMeaning.rename displayed
      have forwardMoved := forwardInduction displayed
      have backwardMoved := backwardInduction displayed
      have rebuilt := Denotes.propositionExtensionality
        leftMoved rightMoved forwardMoved backwardMoved
      apply rebuilt.change_value
      exact NativeHOLTraceLeibnizProofSemantics.proofSection_unique _ _
  | @functionExtensionality n context domain codomain domainTerm codomainTerm
      leftTerm rightTerm pointwiseTerm left right pointwiseValue leftMeaning
      rightMeaning pointwiseMeaning pointwiseInduction =>
      have leftMoved := leftMeaning.rename displayed
      have rightMoved := rightMeaning.rename displayed
      have pointwiseMoved := pointwiseInduction displayed
      have rebuilt := Denotes.functionExtensionality
        (domainTerm := Presentation.rename rho domainTerm)
        (codomainTerm := Presentation.rename rho codomainTerm)
        leftMoved rightMoved pointwiseMoved
      apply rebuilt.change_value
      exact NativeHOLTraceLeibnizProofSemantics.proofSection_unique _ _

theorem Denotes.weaken {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {term : Tower.Tm n} {family : SetFamily context.Environment}
    {value : Section family} (meaning : Denotes a context term family value)
    (extension : SetFamily context.Environment) :
    Denotes a (context.snoc extension) (Presentation.rename wk term)
      (family ∘ Sigma.fst) (fun point => value point.1) :=
  meaning.rename
    (NativeTraceDisplayedSubstitution.Renaming.weaken context extension)

/-- A qualified proof retains a section of the exact canonical truth family. -/
def ProofDenotes (a : ZFSet.{u}) {n : Nat} (context : Context.{u} n)
    (term : Tower.Tm n) (proposition : context.Environment → Prop) : Prop :=
  ∃ value : Section (ZFSetTraceProofDecoding.truthFamily proposition),
    Denotes a context term (ZFSetTraceProofDecoding.truthFamily proposition) value

theorem ProofDenotes.ofMixed {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {proposition : context.Environment → Prop}
    (meaning : NativeHOLTraceLeibnizProofSemantics.ProofDenotes
      a context term proposition) :
    ProofDenotes a context term proposition := by
  obtain ⟨value, termMeaning⟩ := meaning
  exact ⟨value, .mixed termMeaning⟩

theorem ProofDenotes.change_value {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {proposition : context.Environment → Prop}
    (meaning : ProofDenotes a context term proposition)
    (value : Section (ZFSetTraceProofDecoding.truthFamily proposition)) :
    ProofDenotes a context term proposition := by
  obtain ⟨oldValue, oldMeaning⟩ := meaning
  exact ⟨value, oldMeaning.change_value
    (NativeHOLTraceLeibnizProofSemantics.proofSection_unique oldValue value)⟩

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

theorem proofDenotes_valid {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {proposition : context.Environment → Prop}
    (meaning : ProofDenotes a context term proposition) :
    ∀ environment, proposition environment := by
  obtain ⟨value, _⟩ := meaning
  intro environment
  exact (ZFSetTraceProofDecoding.mem_truthCode
    (proposition environment) (value environment).1).mp
      (value environment).2 |>.2

theorem proofVariableZero {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} (proposition : context.Environment → Prop) :
    ProofDenotes a
      (context.snoc (ZFSetTraceProofDecoding.truthFamily proposition)) (.var 0)
      (fun point => proposition point.1) :=
  ProofDenotes.ofMixed
    (NativeHOLTraceLeibnizProofSemantics.proofVariableZero proposition)

/-- Qualified implication introduction remains the ordinary trace lambda;
the premise may itself contain qualified extensional nodes. -/
theorem implicationIntro {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {body : Tower.Tm (n + 1)}
    (premise conclusion : context.Environment → Prop)
    (bodyMeaning : ProofDenotes a
      (context.snoc (ZFSetTraceProofDecoding.truthFamily premise)) body
      (fun point => conclusion point.1)) :
    ProofDenotes a context (.lam body)
      (fun environment => premise environment → conclusion environment) := by
  obtain ⟨value, termMeaning⟩ := bodyMeaning
  have abstracted := Denotes.abstraction termMeaning
  have decoder := ZFSetTraceProofDecoding.implication_decoder premise conclusion
  exact ⟨_, abstracted.cast_family decoder.symm⟩

/-- Qualified implication elimination consumes an arbitrary recursively
qualified premise. -/
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
  exact ⟨_, Denotes.application decodedFunction argumentTerm⟩

theorem universalIntro {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {body : Tower.Tm (n + 1)}
    (domain : SetFamily context.Environment)
    (proposition : Extension domain → Prop)
    (bodyMeaning : ProofDenotes a (context.snoc domain) body proposition) :
    ProofDenotes a context (.lam body)
      (fun environment => ∀ argument : Elements (domain environment),
        proposition ⟨environment, argument⟩) := by
  obtain ⟨value, termMeaning⟩ := bodyMeaning
  have abstracted := Denotes.abstraction termMeaning
  have decoder := ZFSetTraceProofDecoding.forall_decoder domain proposition
  exact ⟨_, abstracted.cast_family decoder.symm⟩

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
  exact ⟨_, Denotes.application decodedFunction (.mixed argumentMeaning)⟩

/-- A represented HOL object is available as a qualified mixed term. -/
theorem object {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {type : HOL.Ty BaseSort} {term : Tower.Tm n}
    {value : context.Environment → Value a type}
    (meaning : NativeHOLTraceDisplayedTerms.Denotes a context term value) :
    Denotes a context term
      (NativeHOLTraceDisplayedTerms.typeFamily a context type) value :=
  .mixed (.object meaning)

theorem reflTerm_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {type : HOL.Ty BaseSort}
    (left : context.Environment → Value a type) :
    ProofDenotes a context FormationSensitiveHOLLeibnizDerived.reflTerm
      (equalityProposition left left) :=
  ProofDenotes.ofMixed
    (NativeHOLTraceLeibnizProofSemantics.reflTerm_denotes left)

theorem reflTerm_denotes_of_equal {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {type : HOL.Ty BaseSort}
    {left right : context.Environment → Value a type}
    (equal : left = right) :
    ProofDenotes a context FormationSensitiveHOLLeibnizDerived.reflTerm
      (equalityProposition left right) := by
  cases equal
  exact reflTerm_denotes left

/-- Leibniz elimination remains compositional when the equality proof is a
qualified extensional result. -/
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
  have decoded := NativeHOLTraceLeibnizProofSemantics.equality_decoder
    a context type left right
  have equalityAsFunction := equalityTerm.cast_family decoded
  change Denotes a context comparison
    (NativeHOLTraceLeibnizProofSemantics.leibnizFamily a context type left right) _
    at equalityAsFunction
  unfold NativeHOLTraceLeibnizProofSemantics.leibnizFamily at equalityAsFunction
  have atPredicate := Denotes.application equalityAsFunction
    (object predicateMeaning)
  change Denotes a context (.app comparison predicateTerm)
    (ZFSetTraceContextual.piFamily
      (ZFSetTraceProofDecoding.truthFamily
        (appliedProposition predicate left))
      (ZFSetTraceProofDecoding.truthFamily
        (fun point => appliedProposition predicate right point.1))) _ at atPredicate
  have atInput := Denotes.application atPredicate inputTermMeaning
  exact ⟨_, atInput⟩

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
  have decoded := NativeHOLTraceLeibnizProofSemantics.equality_decoder
    a context type left right
  have equalityAsFunction := equalityTerm.cast_family decoded
  change Denotes a context comparison
    (NativeHOLTraceLeibnizProofSemantics.leibnizFamily a context type left right) _
    at equalityAsFunction
  unfold NativeHOLTraceLeibnizProofSemantics.leibnizFamily at equalityAsFunction
  have atPredicate := Denotes.application equalityAsFunction
    (object predicateMeaning)
  change Denotes a context (.app comparison predicateTerm)
    (ZFSetTraceContextual.piFamily
      (ZFSetTraceProofDecoding.truthFamily
        (appliedProposition predicate left))
      (ZFSetTraceProofDecoding.truthFamily
        (fun point => appliedProposition predicate right point.1))) _ at atPredicate
  have implication := ZFSetTraceProofDecoding.implication_decoder
    (appliedProposition predicate left) (appliedProposition predicate right)
  exact ⟨_, atPredicate.cast_family implication.symm⟩

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
  have predicateMeaning :=
    NativeHOLTraceLeibnizProofSemantics.rightEqualityPredicate_denotes leftMeaning
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
  have predicateMeaning :=
    NativeHOLTraceLeibnizProofSemantics.leftEqualityPredicate_denotes leftMeaning
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
  have predicateMeaning :=
    NativeHOLTraceLeibnizProofSemantics.congruencePredicate_denotes
      functionMeaning leftMeaning
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
  have predicateMeaning :=
    NativeHOLTraceLeibnizProofSemantics.functionCongruencePredicate_denotes
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
    fun _ => NativeHOLTraceLeibnizProofSemantics.propositionIdentity a
  have specialized := specialize comparisonMeaning
    (NativeHOLTraceLeibnizProofSemantics.propositionIdentityPredicate_denotes
      (a := a) (context := context))
  apply ProofDenotes.cast_proposition
    (by simpa only [FormationSensitiveHOLLeibnizDerived.propForward]
      using specialized)
  funext environment
  apply propext
  simp [appliedProposition,
    NativeHOLTraceLeibnizProofSemantics.propositionIdentity]

theorem propositionExtensionality_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n}
    {leftTerm rightTerm forwardTerm backwardTerm : Tower.Tm n}
    {left right : context.Environment → Value a .prop}
    (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left)
    (rightMeaning : NativeHOLTraceDisplayedTerms.Denotes a context rightTerm right)
    (forwardMeaning : ProofDenotes a context forwardTerm
      (fun environment => ZFSetHOLTypeInterpretation.holds (left environment) →
        ZFSetHOLTypeInterpretation.holds (right environment)))
    (backwardMeaning : ProofDenotes a context backwardTerm
      (fun environment => ZFSetHOLTypeInterpretation.holds (right environment) →
        ZFSetHOLTypeInterpretation.holds (left environment))) :
    ProofDenotes a context
      (propositionExtensionalityApp leftTerm rightTerm forwardTerm backwardTerm)
      (equalityProposition left right) := by
  obtain ⟨forwardValue, forwardTermMeaning⟩ := forwardMeaning
  obtain ⟨backwardValue, backwardTermMeaning⟩ := backwardMeaning
  exact ⟨_, .propositionExtensionality leftMeaning rightMeaning
    forwardTermMeaning backwardTermMeaning⟩

theorem functionExtensionality_denotes {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {domain codomain : HOL.Ty BaseSort}
    (domainTerm codomainTerm : Tower.Tm n)
    {leftTerm rightTerm pointwiseTerm : Tower.Tm n}
    {left right : context.Environment → Value a (.arr domain codomain)}
    (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left)
    (rightMeaning : NativeHOLTraceDisplayedTerms.Denotes a context rightTerm right)
    (pointwiseMeaning : ProofDenotes a context pointwiseTerm
      (fun environment => ∀ argument : Value a domain,
        app (left environment) argument = app (right environment) argument)) :
    ProofDenotes a context
      (functionExtensionalityApp domainTerm codomainTerm leftTerm rightTerm pointwiseTerm)
      (equalityProposition left right) := by
  obtain ⟨pointwiseValue, pointwiseTermMeaning⟩ := pointwiseMeaning
  exact ⟨_, .functionExtensionality
    (domainTerm := domainTerm) (codomainTerm := codomainTerm)
    leftMeaning rightMeaning pointwiseTermMeaning⟩

#print axioms Denotes.rename
#print axioms Denotes.weaken
#print axioms ProofDenotes.ofMixed
#print axioms ProofDenotes.weaken
#print axioms proofDenotes_valid
#print axioms implicationIntro
#print axioms implicationElim
#print axioms universalIntro
#print axioms universalElim
#print axioms eliminate
#print axioms specialize
#print axioms symmetry_denotes
#print axioms transitivity_denotes
#print axioms congruence_denotes
#print axioms functionCongruence_denotes
#print axioms propForward_denotes
#print axioms propositionExtensionality_denotes
#print axioms functionExtensionality_denotes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceQualifiedExtensionalSemantics
