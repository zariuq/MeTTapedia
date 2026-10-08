import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CheckingAlgorithm
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableConversion

/-!
# Executable dependent synthesis and checking

This procedure reconstructs `CheckingAlgorithm` derivations from terms. Its
inputs contain no typing derivation or supplied structural proof tree. Universe
successors and joins are primitive choices, independently qualified at the
selected rule package; its reduction strategy is shared with executable conversion.
The public checking boundary checks context and expected-type formation too.
Fuel failure means no certificate was found, and does not mean ill-typedness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace ExecutableChecking

variable {Head : Type}

structure HeadChoices (R : Rules Head) where
  typing : (head : Head) → Option {type : Head // R.headTyping head type}
  join : (first second : Head) → Option {result : Head // R.join first second result}

variable (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
variable [∀ head, Decidable (R.isUniverse head)] [DecidableRel R.cumulative]
variable (heads : HeadChoices R) (reducer : ExecutableReduction.Reducer R)

abbrev SynthResult {n : Nat} (context : Ctx Head n) (term : Tm Head n) :=
  (type : Tm Head n) × PLift (CheckingAlgorithm R .synth context term type)

abbrev CheckResult {n : Nat} (context : Ctx Head n) (term type : Tm Head n) :=
  PLift (CheckingAlgorithm R .check context term type)

/-- Recognition of a computed universe head, with the independently reconstructed
reduction from the supplied synthesized type. -/
def asUniverse {n : Nat} (fuel : Nat) (type : Tm Head n) :
    Option {head : Head // R.isUniverse head ∧ Reduces R type (.head head)} := do
  let normal ← reducer fuel type
  match normalShape : normal.val with
  | .head head =>
      if admitted : R.isUniverse head then
        some ⟨head, admitted, (normalShape ▸ normal.property)⟩
      else none
  | _ => none

def below : Nat → {n : Nat} → (context : Ctx Head n) → (first second : Tm Head n) →
    Option (PLift (BelowAlgorithm R context first second))
  | 0, _, _, _, _ => none
  | fuel+1, _, context, first, second =>
      match ExecutableConversion.types R reducer (fuel+1) context first second with
      | some same => some ⟨.conv same.down⟩
      | none => do
          let firstNormal ← reducer (fuel+1) first
          let secondNormal ← reducer (fuel+1) second
          match firstShape : firstNormal.val, secondShape : secondNormal.val with
          | .head u, .head v =>
              if cumulative : R.cumulative u v then
                return ⟨.universes (firstShape ▸ firstNormal.property) (secondShape ▸ secondNormal.property) cumulative⟩
              else none
          | .pi domain body, .pi domain' body' =>
              let domains ← ExecutableConversion.types R reducer fuel context domain domain'
              let bodies ← below fuel (.snoc context domain) body body'
              return ⟨.pi (firstShape ▸ firstNormal.property) (secondShape ▸ secondNormal.property) domains.down bodies.down⟩
          | .sigma domain body, .sigma domain' body' =>
              let domains ← below fuel context domain domain'
              let bodies ← below fuel (.snoc context domain) body body'
              return ⟨.sigma (firstShape ▸ firstNormal.property) (secondShape ▸ secondNormal.property) domains.down bodies.down⟩
          | _, _ => none

mutual

def synth : Nat → {n : Nat} → (context : Ctx Head n) → (term : Tm Head n) →
    Option (SynthResult R context term)
  | 0, _, _, _ => none
  | fuel+1, _, context, term => match term with
      | .var index => some ⟨Ctx.lookup context index, ⟨.var index⟩⟩
      | .const name => match known : R.constantType name with
          | some type => some ⟨liftClosed type, ⟨.const known⟩⟩
          | none => none
      | .head value => do
          let chosen ← heads.typing value
          return ⟨.head chosen.val, ⟨.head chosen.property⟩⟩
      | .pi domain body => do
          let domainType ← synth fuel context domain
          let domainLevel ← asUniverse R reducer (fuel+1) domainType.1
          let bodyType ← synth fuel (.snoc context domain) body
          let bodyLevel ← asUniverse R reducer (fuel+1) bodyType.1
          let joined ← heads.join domainLevel.val bodyLevel.val
          return ⟨.head joined.val, ⟨.pi domainType.2.down domainLevel.property.2
            domainLevel.property.1 bodyType.2.down bodyLevel.property.2
            bodyLevel.property.1 joined.property⟩⟩
      | .sigma domain body => do
          let domainType ← synth fuel context domain
          let domainLevel ← asUniverse R reducer (fuel+1) domainType.1
          let bodyType ← synth fuel (.snoc context domain) body
          let bodyLevel ← asUniverse R reducer (fuel+1) bodyType.1
          let joined ← heads.join domainLevel.val bodyLevel.val
          return ⟨.head joined.val, ⟨.sigma domainType.2.down domainLevel.property.2
            domainLevel.property.1 bodyType.2.down bodyLevel.property.2
            bodyLevel.property.1 joined.property⟩⟩
      | .id carrier left right => do
          let carrierType ← synth fuel context carrier
          let carrierLevel ← asUniverse R reducer (fuel+1) carrierType.1
          let first ← check fuel context left carrier
          let second ← check fuel context right carrier
          return ⟨.head carrierLevel.val, ⟨.id carrierType.2.down carrierLevel.property.2
            carrierLevel.property.1 first.down second.down⟩⟩
      | .refl subject => do
          let reflected ← synth fuel context subject
          return ⟨.id reflected.1 subject subject, ⟨.refl reflected.2.down⟩⟩
      | .app (.lam body) argument => do
          let argumentType ← synth fuel context argument
          let bodyType ← synth fuel (.snoc context argumentType.1) body
          return ⟨inst0 argument bodyType.1, ⟨.redex argumentType.2.down bodyType.2.down⟩⟩
      | .app function argument => do
          let functionType ← synth fuel context function
          let functionNormal ← reducer (fuel+1) functionType.1
          match functionNormalShape : functionNormal.val with
          | .pi domain body =>
              let argumentChecked ← check fuel context argument domain
              return ⟨inst0 argument body,
                ⟨.app functionType.2.down (functionNormalShape ▸ functionNormal.property) argumentChecked.down⟩⟩
          | _ => none
      | .fst pair => do
          let pairType ← synth fuel context pair
          let pairNormal ← reducer (fuel+1) pairType.1
          match pairNormalShape : pairNormal.val with
          | .sigma domain _ => return ⟨domain, ⟨.fst pairType.2.down (pairNormalShape ▸ pairNormal.property)⟩⟩
          | _ => none
      | .snd pair => do
          let pairType ← synth fuel context pair
          let pairNormal ← reducer (fuel+1) pairType.1
          match pairNormalShape : pairNormal.val with
          | .sigma _ body =>
              return ⟨inst0 (.fst pair) body, ⟨.snd pairType.2.down (pairNormalShape ▸ pairNormal.property)⟩⟩
          | _ => none
      | .lam _ | .pair _ _ => none

def check : Nat → {n : Nat} → (context : Ctx Head n) → (term type : Tm Head n) →
    Option (CheckResult R context term type)
  | 0, _, _, _, _ => none
  | fuel+1, _, context, term, type => match term with
      | .lam body => do
          let normal ← reducer (fuel+1) type
          match normalShape : normal.val with
          | .pi domain codomain =>
              let checked ← check fuel (.snoc context domain) body codomain
              return ⟨.lamCheck (normalShape ▸ normal.property) checked.down⟩
          | _ => none
      | .pair first second => do
          let normal ← reducer (fuel+1) type
          match normalShape : normal.val with
          | .sigma domain codomain =>
              let firstChecked ← check fuel context first domain
              let secondChecked ← check fuel context second (inst0 first codomain)
              return ⟨.pairCheck (normalShape ▸ normal.property) firstChecked.down secondChecked.down⟩
          | _ => none
      | .refl subject => do
          let normal ← reducer (fuel+1) type
          match normalShape : normal.val with
          | .id carrier left right =>
              let checked ← check fuel context subject carrier
              let first ← ExecutableConversion.compare R reducer fuel context subject left carrier
              let second ← ExecutableConversion.compare R reducer fuel context subject right carrier
              return ⟨.reflCheck (normalShape ▸ normal.property) checked.down first.down second.down⟩
          | _ => none
      | other => do
          let inferred ← synth fuel context other
          let usable ← below R reducer fuel context inferred.1 type
          return ⟨.switch inferred.2.down usable.down⟩

end

inductive ContextAlgorithm (R : Rules Head) : {n : Nat} → Ctx Head n → Prop where
  | nil : ContextAlgorithm R .nil
  | snoc {n : Nat} {context : Ctx Head n} {domain type : Tm Head n} {levelHead : Head} :
      ContextAlgorithm R context → CheckingAlgorithm R .synth context domain type →
      Reduces R type (.head levelHead) → R.isUniverse levelHead →
      ContextAlgorithm R (.snoc context domain)

def formContext (fuel : Nat) : {n : Nat} → (context : Ctx Head n) →
    Option (PLift (ContextAlgorithm R context))
  | _, .nil => some ⟨.nil⟩
  | _, .snoc context domain => do
      let previous ← formContext fuel context
      let inferred ← synth R heads reducer fuel context domain
      let level ← asUniverse R reducer fuel inferred.1
      return ⟨.snoc previous.down inferred.2.down level.property.2 level.property.1⟩

structure JudgmentCertificate {n : Nat} (context : Ctx Head n) (term type : Tm Head n) where
  contextChecked : ContextAlgorithm R context
  expectedUniverse : Head
  expectedType : Tm Head n
  expectedChecked : CheckingAlgorithm R .synth context type expectedType
  expectedReduction : Reduces R expectedType (.head expectedUniverse)
  expectedIsUniverse : R.isUniverse expectedUniverse
  termChecked : CheckingAlgorithm R .check context term type

def judgment {n : Nat} (fuel : Nat) (context : Ctx Head n) (term type : Tm Head n) :
    Option (JudgmentCertificate R context term type) := do
  let contextChecked ← formContext R heads reducer fuel context
  let expected ← synth R heads reducer fuel context type
  let level ← asUniverse R reducer fuel expected.1
  let termChecked ← check R heads reducer fuel context term type
  return ⟨contextChecked.down, level.val, expected.1, expected.2.down,
    level.property.2, level.property.1, termChecked.down⟩

def accepts {n : Nat} (fuel : Nat) (context : Ctx Head n) (term type : Tm Head n) : Bool :=
  (judgment R heads reducer fuel context term type).isSome

structure EqualityCertificate {n : Nat} (context : Ctx Head n)
    (first second type : Tm Head n) where
  firstChecked : JudgmentCertificate R context first type
  secondChecked : JudgmentCertificate R context second type
  compared : Algorithm R (.compare context first second type)

/-- Conversion is qualified by computed formation and typing of both
endpoints. A raw conversion search alone does not establish typed equality. -/
def equality {n : Nat} (fuel : Nat) (context : Ctx Head n)
    (first second type : Tm Head n) : Option (EqualityCertificate R context first second type) := do
  let firstChecked ← judgment R heads reducer fuel context first type
  let secondChecked ← judgment R heads reducer fuel context second type
  let compared ← ExecutableConversion.compare R reducer fuel context first second type
  return ⟨firstChecked, secondChecked, compared.down⟩

def acceptsEquality {n : Nat} (fuel : Nat) (context : Ctx Head n)
    (first second type : Tm Head n) : Bool :=
  (equality R heads reducer fuel context first second type).isSome

section Soundness

open UniverseLevel (LevelOrder)

variable {L : Type} [LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (headSteps : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
include facts roots headSteps algebra declared

omit [DecidableEq Head] in
theorem ContextAlgorithm.sound {n : Nat} {context : Ctx Head n}
    (checked : ContextAlgorithm S.R context) : CtxFormed S.R context := by
  induction checked with
  | nil => exact .nil
  | snoc _ domainChecked reduction levelHead previous =>
      have typed := CheckingAlgorithm.sound facts roots headSteps algebra declared
        domainChecked previous
      exact .snoc previous ⟨_, levelHead, Typed.convType typed
        (Reduces.typeEq facts roots headSteps previous reduction (Typed.isType typed previous))⟩

omit [DecidableEq Head] in
theorem JudgmentCertificate.sound {n : Nat} {context : Ctx Head n} {term type : Tm Head n}
    (certificate : JudgmentCertificate S.R context term type) : Typed S.R context term type := by
  have contextFormed := ContextAlgorithm.sound facts roots headSteps algebra declared
    certificate.contextChecked
  have expected := CheckingAlgorithm.sound facts roots headSteps algebra declared
    certificate.expectedChecked contextFormed
  have expectedFormed : IsType S.R context type :=
    ⟨certificate.expectedUniverse, certificate.expectedIsUniverse,
      Typed.convType expected (Reduces.typeEq facts roots headSteps contextFormed
        certificate.expectedReduction (Typed.isType expected contextFormed))⟩
  exact CheckingAlgorithm.sound facts roots headSteps algebra declared certificate.termChecked
    contextFormed expectedFormed

/-- Computed acceptance establishes typing, including context and expected-type
formation. No proof tree is an input to this test. -/
theorem accepts_sound [DecidableRel S.R.headEq]
    [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
    (choices : HeadChoices S.R) (evaluator : ExecutableReduction.Reducer S.R)
    {n fuel : Nat} {context : Ctx Head n} {term type : Tm Head n}
    (accepted : accepts S.R choices evaluator fuel context term type = true) :
    Typed S.R context term type := by
  unfold accepts at accepted
  cases computed : judgment S.R choices evaluator fuel context term type with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at accepted
  | some certificate =>
      exact JudgmentCertificate.sound facts roots headSteps algebra declared certificate

omit [DecidableEq Head] in
theorem EqualityCertificate.sound {n : Nat} {context : Ctx Head n}
    {first second type : Tm Head n}
    (certificate : EqualityCertificate S.R context first second type) :
    Equal S.R context first second type := by
  have formed := ContextAlgorithm.sound facts roots headSteps algebra declared
    certificate.firstChecked.contextChecked
  exact Algorithm.sound facts roots headSteps algebra certificate.compared formed
    (JudgmentCertificate.sound facts roots headSteps algebra declared certificate.firstChecked)
    (JudgmentCertificate.sound facts roots headSteps algebra declared certificate.secondChecked)

theorem acceptsEquality_sound [DecidableRel S.R.headEq]
    [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
    (choices : HeadChoices S.R) (evaluator : ExecutableReduction.Reducer S.R)
    {n fuel : Nat} {context : Ctx Head n} {first second type : Tm Head n}
    (accepted : acceptsEquality S.R choices evaluator fuel context first second type = true) :
    Equal S.R context first second type := by
  unfold acceptsEquality at accepted
  cases computed : equality S.R choices evaluator fuel context first second type with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at accepted
  | some certificate =>
      exact EqualityCertificate.sound facts roots headSteps algebra declared certificate

end Soundness

end ExecutableChecking
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
