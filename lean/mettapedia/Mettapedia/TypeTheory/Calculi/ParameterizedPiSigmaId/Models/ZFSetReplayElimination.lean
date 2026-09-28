import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySubstitution

/-!
# Elimination into the actual extracted result type

The existing resultFormation algorithm instantiates a product codomain or
a dependent-pair fibre. These proofs connect its exact output to replay
interpretation and the set-theoretic elimination laws.

The immediate semantic typing premises are explicit. This proves the
elimination cases, not soundness of all premises, conversion profiles or
independently chosen formation certificates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (sigmaSet)
open ZFSetTraceProducts (tracePiSet traceApp)
open Mettapedia.SetTheory

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
variable (universeSuccessor : Head → Head)
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

theorem application_resultFormation_interpretation
    (context : Ctx Head n) (contextCode : ContextCode Head ConversionCode n)
    (A function argument : Tm Head n) (B : Tm Head (n + 1))
    (functionCode argumentCode formation domainCode : Code Head ConversionCode n)
    (bodyCode : Code Head ConversionCode (n + 1)) (level domainLevel bodyLevel : Head)
    (bodyMeaning : Meaning.{u} (n + 1)) (arg : Meaning.{u} n)
    (atFunctionType : functionCode.resultFormation renameConversion substituteConversion universeSuccessor
      contextCode function (.pi A B) = some (level, formation))
    (atParts : formation.piFormation = some (domainLevel, bodyLevel, domainCode, bodyCode))
    (bodyChecked : check R conversionCheck (.snoc context A) B (.head bodyLevel) bodyCode = true)
    (atBody : assemble heads constants bodyCode B (.head bodyLevel) = some bodyMeaning)
    (atArgument : assemble heads constants argumentCode argument A = some arg) :
    ∃ resultType,
      (Code.appElim A B functionCode argumentCode).resultFormation
        renameConversion substituteConversion universeSuccessor contextCode (.app function argument)
        (inst0 argument B) = some (bodyLevel, bodyCode.instantiateFormation
          renameConversion substituteConversion B bodyLevel argument argumentCode) ∧
      assemble heads constants (bodyCode.instantiateFormation
          renameConversion substituteConversion B bodyLevel argument argumentCode)
        (inst0 argument B) (.head bodyLevel) = some resultType ∧
      ∀ env, resultType.value env = bodyMeaning.value (extend env (arg.value env)) := by
  obtain ⟨resultType, assembled, values⟩ :=
    assemble_instantiate renameConversion substituteConversion heads constants R conversionCheck
      bodyCode argumentCode bodyMeaning arg bodyChecked atBody atArgument
  refine ⟨resultType, ?_, assembled, values⟩
  simp [Code.resultFormation, atFunctionType, atParts]

/-- If the function and argument inhabit the exact extracted product and
domain, application inhabits the type computed by resultFormation. -/
theorem application_result_membership
    (context : Ctx Head n) (contextCode : ContextCode Head ConversionCode n)
    (A function argument : Tm Head n) (B : Tm Head (n + 1))
    (functionCode argumentCode formation domainCode : Code Head ConversionCode n)
    (bodyCode : Code Head ConversionCode (n + 1)) (level domainLevel bodyLevel : Head)
    (functionMeaning functionType domainMeaning arg result : Meaning.{u} n)
    (bodyMeaning : Meaning.{u} (n + 1))
    (atFunctionType : functionCode.resultFormation renameConversion substituteConversion universeSuccessor
      contextCode function (.pi A B) = some (level, formation))
    (atParts : formation.piFormation = some (domainLevel, bodyLevel, domainCode, bodyCode))
    (bodyChecked : check R conversionCheck (.snoc context A) B (.head bodyLevel) bodyCode = true)
    (atProduct : assemble heads constants formation (.pi A B) (.head level) = some functionType)
    (atDomain : assemble heads constants domainCode A (.head domainLevel) = some domainMeaning)
    (atBody : assemble heads constants bodyCode B (.head bodyLevel) = some bodyMeaning)
    (atFunction : assemble heads constants functionCode function (.pi A B) = some functionMeaning)
    (atArgument : assemble heads constants argumentCode argument A = some arg)
    (atResult : assemble heads constants (.appElim A B functionCode argumentCode)
      (.app function argument) (inst0 argument B) = some result)
    (env : Environment.{u} n)
    (functionTyped : functionMeaning.value env ∈ functionType.value env)
    (argumentTyped : arg.value env ∈ domainMeaning.value env) :
    ∃ resultType,
      (Code.appElim A B functionCode argumentCode).resultFormation
        renameConversion substituteConversion universeSuccessor contextCode (.app function argument)
        (inst0 argument B) = some (bodyLevel, bodyCode.instantiateFormation
          renameConversion substituteConversion B bodyLevel argument argumentCode) ∧
      assemble heads constants (bodyCode.instantiateFormation
          renameConversion substituteConversion B bodyLevel argument argumentCode)
        (inst0 argument B) (.head bodyLevel) = some resultType ∧
      result.value env ∈ resultType.value env := by
  obtain ⟨a, b, atA, atB, productValue, _⟩ :=
    assemble_piFormation heads constants formation atParts atProduct
  rw [atDomain] at atA
  rw [atBody] at atB
  cases Option.some.inj atA
  cases Option.some.inj atB
  obtain ⟨resultType, extracted, assembled, values⟩ :=
    application_resultFormation_interpretation heads constants renameConversion substituteConversion
      universeSuccessor R conversionCheck context contextCode A function argument B
      functionCode argumentCode formation domainCode bodyCode level domainLevel bodyLevel
      bodyMeaning arg atFunctionType atParts bodyChecked atBody atArgument
  refine ⟨resultType, extracted, assembled, ?_⟩
  rw [values]
  simp [assemble, atFunction, atArgument] at atResult
  subst result
  rw [productValue] at functionTyped
  exact ZFSetTraceProducts.traceApp_mem ⟨_, functionTyped⟩ ⟨_, argumentTyped⟩

omit [DecidableEq Head] in
/-- First projection uses the domain certificate extracted from the pair's
actual result formation. No independent domain interpretation is selected. -/
theorem first_result_membership
    (contextCode : ContextCode Head ConversionCode n)
    (A pair : Tm Head n) (B : Tm Head (n + 1))
    (pairCode formation domainCode : Code Head ConversionCode n)
    (bodyCode : Code Head ConversionCode (n + 1)) (level domainLevel bodyLevel : Head)
    (pairMeaning pairType domainMeaning result : Meaning.{u} n)
    (atPairType : pairCode.resultFormation renameConversion substituteConversion universeSuccessor
      contextCode pair (.sigma A B) = some (level, formation))
    (atParts : formation.sigmaFormation = some (domainLevel, bodyLevel, domainCode, bodyCode))
    (atSigma : assemble heads constants formation (.sigma A B) (.head level) = some pairType)
    (atDomain : assemble heads constants domainCode A (.head domainLevel) = some domainMeaning)
    (atPair : assemble heads constants pairCode pair (.sigma A B) = some pairMeaning)
    (atResult : assemble heads constants (.fstElim B pairCode) (.fst pair) A = some result)
    (env : Environment.{u} n) (pairTyped : pairMeaning.value env ∈ pairType.value env) :
    (Code.fstElim B pairCode).resultFormation renameConversion substituteConversion universeSuccessor
      contextCode (.fst pair) A = some (domainLevel, domainCode) ∧
      result.value env ∈ domainMeaning.value env := by
  refine ⟨by simp [Code.resultFormation, atPairType, atParts], ?_⟩
  obtain ⟨a, b, atA, _, sigmaValue⟩ :=
    assemble_sigmaFormation heads constants formation atParts atSigma
  rw [atDomain] at atA
  cases Option.some.inj atA
  rw [sigmaValue] at pairTyped
  obtain ⟨x, inside, y, _, equal⟩ := ZFSetDependentProducts.mem_sigmaSet.mp pairTyped
  simp [assemble, atPair] at atResult
  subst result
  change ZFSetOrderedPair.first (pairMeaning.value env) ∈ domainMeaning.value env
  rw [equal, ZFSetOrderedPair.first_pair]
  exact inside

/-- The second projection's extracted type substitutes the first projection,
using the very certificate built by resultFormation for that projection. -/
theorem second_resultFormation_interpretation
    (context : Ctx Head n) (contextCode : ContextCode Head ConversionCode n)
    (A pair : Tm Head n) (B : Tm Head (n + 1))
    (pairCode formation domainCode : Code Head ConversionCode n)
    (bodyCode : Code Head ConversionCode (n + 1)) (level domainLevel bodyLevel : Head)
    (bodyMeaning : Meaning.{u} (n + 1)) (pairMeaning : Meaning.{u} n)
    (atPairType : pairCode.resultFormation renameConversion substituteConversion universeSuccessor
      contextCode pair (.sigma A B) = some (level, formation))
    (atParts : formation.sigmaFormation = some (domainLevel, bodyLevel, domainCode, bodyCode))
    (bodyChecked : check R conversionCheck (.snoc context A) B (.head bodyLevel) bodyCode = true)
    (atBody : assemble heads constants bodyCode B (.head bodyLevel) = some bodyMeaning)
    (atPair : assemble heads constants pairCode pair (.sigma A B) = some pairMeaning) :
    ∃ resultType,
      (Code.sndElim A B pairCode).resultFormation
        renameConversion substituteConversion universeSuccessor contextCode (.snd pair)
        (inst0 (.fst pair) B) = some (bodyLevel, bodyCode.instantiateFormation
          renameConversion substituteConversion B bodyLevel (.fst pair) (.fstElim B pairCode)) ∧
      assemble heads constants (bodyCode.instantiateFormation
          renameConversion substituteConversion B bodyLevel (.fst pair) (.fstElim B pairCode))
        (inst0 (.fst pair) B) (.head bodyLevel) = some resultType ∧
      ∀ env, resultType.value env =
        bodyMeaning.value (extend env (ZFSetOrderedPair.first (pairMeaning.value env))) := by
  have atFirst : assemble heads constants (.fstElim B pairCode) (.fst pair) A =
      some (.plain (fun env => ZFSetOrderedPair.first (pairMeaning.value env))) := by
    simp [assemble, atPair]
  obtain ⟨resultType, assembled, values⟩ :=
    assemble_instantiate renameConversion substituteConversion heads constants R conversionCheck
      bodyCode (.fstElim B pairCode) bodyMeaning _ bodyChecked atBody atFirst
  refine ⟨resultType, ?_, assembled, values⟩
  simp [Code.resultFormation, atPairType, atParts]

/-- Second projection inhabits the fibre over the first projection, with the
type's assembly pinned to the actual generated formation certificate. -/
theorem second_result_membership
    (context : Ctx Head n) (contextCode : ContextCode Head ConversionCode n)
    (A pair : Tm Head n) (B : Tm Head (n + 1))
    (pairCode formation domainCode : Code Head ConversionCode n)
    (bodyCode : Code Head ConversionCode (n + 1)) (level domainLevel bodyLevel : Head)
    (pairMeaning pairType result : Meaning.{u} n) (bodyMeaning : Meaning.{u} (n + 1))
    (atPairType : pairCode.resultFormation renameConversion substituteConversion universeSuccessor
      contextCode pair (.sigma A B) = some (level, formation))
    (atParts : formation.sigmaFormation = some (domainLevel, bodyLevel, domainCode, bodyCode))
    (bodyChecked : check R conversionCheck (.snoc context A) B (.head bodyLevel) bodyCode = true)
    (atSigma : assemble heads constants formation (.sigma A B) (.head level) = some pairType)
    (atBody : assemble heads constants bodyCode B (.head bodyLevel) = some bodyMeaning)
    (atPair : assemble heads constants pairCode pair (.sigma A B) = some pairMeaning)
    (atResult : assemble heads constants (.sndElim A B pairCode) (.snd pair)
      (inst0 (.fst pair) B) = some result)
    (env : Environment.{u} n) (pairTyped : pairMeaning.value env ∈ pairType.value env) :
    ∃ resultType,
      (Code.sndElim A B pairCode).resultFormation
        renameConversion substituteConversion universeSuccessor contextCode (.snd pair)
        (inst0 (.fst pair) B) = some (bodyLevel, bodyCode.instantiateFormation
          renameConversion substituteConversion B bodyLevel (.fst pair) (.fstElim B pairCode)) ∧
      assemble heads constants (bodyCode.instantiateFormation
          renameConversion substituteConversion B bodyLevel (.fst pair) (.fstElim B pairCode))
        (inst0 (.fst pair) B) (.head bodyLevel) = some resultType ∧
      result.value env ∈ resultType.value env := by
  obtain ⟨a, b, _, atB, sigmaValue⟩ :=
    assemble_sigmaFormation heads constants formation atParts atSigma
  rw [atBody] at atB
  cases Option.some.inj atB
  obtain ⟨resultType, extracted, assembled, values⟩ :=
    second_resultFormation_interpretation heads constants renameConversion substituteConversion
      universeSuccessor R conversionCheck context contextCode A pair B pairCode formation
      domainCode bodyCode level domainLevel bodyLevel bodyMeaning pairMeaning
      atPairType atParts bodyChecked atBody atPair
  refine ⟨resultType, extracted, assembled, ?_⟩
  rw [values]
  rw [sigmaValue] at pairTyped
  obtain ⟨x, _, y, inside, equal⟩ := ZFSetDependentProducts.mem_sigmaSet.mp pairTyped
  simp [assemble, atPair] at atResult
  subst result
  change ZFSetOrderedPair.second (pairMeaning.value env) ∈
    bodyMeaning.value (extend env (ZFSetOrderedPair.first (pairMeaning.value env)))
  rw [equal, ZFSetOrderedPair.first_pair, ZFSetOrderedPair.second_pair]
  exact inside

#print axioms application_resultFormation_interpretation
#print axioms application_result_membership
#print axioms first_result_membership
#print axioms second_resultFormation_interpretation
#print axioms second_result_membership

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
