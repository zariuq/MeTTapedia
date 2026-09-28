import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContext
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySubstitution

/-!
# Introduction into the types extracted from replay

Lambda introduction uses the actual Pi formation children and the context
extension assembled from its domain child. Pair introduction uses the actual
instantiated codomain certificate. Reflexivity uses the formation extracted
from its argument. These are constructor-level membership laws; semantic
typing of immediate premises is explicit, not assumed for all derivations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph sigmaSet)
open ZFSetTraceProducts (tracePiSet traceLam)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
variable (universeSuccessor : Head → Head)

theorem context_extension_valid_iff
    (context : Ctx Head n) (A : Tm Head n) (contextCode : ContextCode Head ConversionCode n)
    (level : Head) (formation : Code Head ConversionCode n)
    (valid : Environment.{u} n → Prop) (extended : Environment.{u} (n + 1) → Prop)
    (domain : Meaning.{u} n)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (atDomain : assemble heads constants formation A (.head level) = some domain)
    (atExtension : assembleContext heads constants (.snoc contextCode level formation)
      (.snoc context A) = some extended)
    (env : Environment.{u} n) (x : ZFSet.{u}) :
    extended (extend env x) ↔ valid env ∧ x ∈ domain.value env := by
  simp [assembleContext, atContext, atDomain] at atExtension
  subst extended
  rfl

/-- A body which inhabits the Pi child's codomain on the assembled extended
context gives a lambda in the Pi set extracted by resultFormation. -/
theorem lambda_result_membership
    (context : Ctx Head n) (contextCode : ContextCode Head ConversionCode n)
    (A : Tm Head n) (B body : Tm Head (n + 1))
    (formation domainCode : Code Head ConversionCode n)
    (codomainCode bodyCode : Code Head ConversionCode (n + 1))
    (level domainLevel bodyLevel : Head)
    (formed domain result : Meaning.{u} n) (codomain bodyMeaning : Meaning.{u} (n + 1))
    (valid : Environment.{u} n → Prop) (extended : Environment.{u} (n + 1) → Prop)
    (atParts : formation.piFormation = some (domainLevel, bodyLevel, domainCode, codomainCode))
    (atFormation : assemble heads constants formation (.pi A B) (.head level) = some formed)
    (atDomain : assemble heads constants domainCode A (.head domainLevel) = some domain)
    (atCodomain : assemble heads constants codomainCode B (.head bodyLevel) = some codomain)
    (atBody : assemble heads constants bodyCode body B = some bodyMeaning)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (atExtension : assembleContext heads constants (.snoc contextCode domainLevel domainCode)
      (.snoc context A) = some extended)
    (atResult : assemble heads constants (.lamIntro level formation bodyCode)
      (.lam body) (.pi A B) = some result)
    (bodyTyped : ∀ env, extended env → bodyMeaning.value env ∈ codomain.value env)
    (env : Environment.{u} n) (admitted : valid env) :
    (Code.lamIntro level formation bodyCode).resultFormation
      renameConversion substituteConversion universeSuccessor contextCode (.lam body) (.pi A B) =
        some (level, formation) ∧ result.value env ∈ formed.value env := by
  refine ⟨rfl, ?_⟩
  obtain ⟨a, b, atA, atB, productValue, productDomain⟩ :=
    assemble_piFormation heads constants formation atParts atFormation
  rw [atDomain] at atA
  rw [atCodomain] at atB
  cases Option.some.inj atA
  cases Option.some.inj atB
  simp [assemble, atFormation, productDomain, atBody] at atResult
  subst result
  rw [productValue]
  apply ZFSetTraceProducts.mem_tracePiSet.mpr
  refine ⟨graph (domain.value env) (fun x => bodyMeaning.value (extend env x)), ?_, rfl⟩
  apply ZFSetDependentProducts.graph_mem_piSet
  intro x inside
  exact bodyTyped _ ((context_extension_valid_iff heads constants context A contextCode
    domainLevel domainCode valid extended domain atContext atDomain atExtension env x).mpr
      ⟨admitted, inside⟩)

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

/-- The second component is checked semantically against the codomain
certificate produced by actual instantiation, not an unrelated fibre. -/
theorem pair_result_membership
    (context : Ctx Head n) (contextCode : ContextCode Head ConversionCode n)
    (A x y : Tm Head n) (B : Tm Head (n + 1))
    (formation domainCode firstCode secondCode : Code Head ConversionCode n)
    (codomainCode : Code Head ConversionCode (n + 1))
    (level domainLevel bodyLevel : Head)
    (formed domain first second secondType result : Meaning.{u} n)
    (codomain : Meaning.{u} (n + 1))
    (atParts : formation.sigmaFormation = some (domainLevel, bodyLevel, domainCode, codomainCode))
    (atFormation : assemble heads constants formation (.sigma A B) (.head level) = some formed)
    (atDomain : assemble heads constants domainCode A (.head domainLevel) = some domain)
    (atCodomain : assemble heads constants codomainCode B (.head bodyLevel) = some codomain)
    (codomainChecked : check R conversionCheck (.snoc context A) B (.head bodyLevel) codomainCode = true)
    (atFirst : assemble heads constants firstCode x A = some first)
    (atSecond : assemble heads constants secondCode y (inst0 x B) = some second)
    (atSecondType : assemble heads constants (codomainCode.instantiateFormation
      renameConversion substituteConversion B bodyLevel x firstCode) (inst0 x B) (.head bodyLevel) =
        some secondType)
    (atResult : assemble heads constants (.pairIntro level formation firstCode secondCode)
      (.pair x y) (.sigma A B) = some result)
    (env : Environment.{u} n) (firstTyped : first.value env ∈ domain.value env)
    (secondTyped : second.value env ∈ secondType.value env) :
    (Code.pairIntro level formation firstCode secondCode).resultFormation
      renameConversion substituteConversion universeSuccessor contextCode (.pair x y) (.sigma A B) =
        some (level, formation) ∧ result.value env ∈ formed.value env := by
  refine ⟨rfl, ?_⟩
  obtain ⟨a, b, atA, atB, sigmaValue⟩ :=
    assemble_sigmaFormation heads constants formation atParts atFormation
  rw [atDomain] at atA
  rw [atCodomain] at atB
  cases Option.some.inj atA
  cases Option.some.inj atB
  obtain ⟨instantiated, assembled, values⟩ := assemble_instantiate
    renameConversion substituteConversion heads constants R conversionCheck codomainCode firstCode
    codomain first codomainChecked atCodomain atFirst
  change assemble heads constants (codomainCode.instantiateFormation
    renameConversion substituteConversion B bodyLevel x firstCode) (inst0 x B) (.head bodyLevel) =
      some instantiated at assembled
  rw [atSecondType] at assembled
  cases Option.some.inj assembled
  rw [values] at secondTyped
  simp [assemble, atFirst, atSecond] at atResult
  subst result
  rw [sigmaValue]
  exact ZFSetDependentProducts.mem_sigmaSet.mpr
    ⟨_, firstTyped, _, secondTyped, rfl⟩

omit [DecidableEq Head] in
/-- Reflexivity inhabits the identity set assembled from the exact
resultFormation output, including its argument's formation certificate. -/
theorem reflexivity_result_membership
    (contextCode : ContextCode Head ConversionCode n) (A term : Tm Head n)
    (termCode formation : Code Head ConversionCode n) (level : Head)
    (meaning : Meaning.{u} n)
    (atType : termCode.resultFormation renameConversion substituteConversion universeSuccessor
      contextCode term A = some (level, formation))
    (atTerm : assemble heads constants termCode term A = some meaning) :
    ∃ result resultType,
      (Code.reflIntro A termCode).resultFormation renameConversion substituteConversion universeSuccessor
        contextCode (.refl term) (.id A term term) =
          some (level, .idForm level formation termCode termCode) ∧
      assemble heads constants (.reflIntro A termCode) (.refl term) (.id A term term) = some result ∧
      assemble heads constants (.idForm level formation termCode termCode)
        (.id A term term) (.head level) = some resultType ∧
      ∀ env, result.value env ∈ resultType.value env := by
  refine ⟨.plain (fun _ => ∅), .plain (fun env => truthCode (meaning.value env = meaning.value env)),
    ?_, rfl, ?_, ?_⟩
  · simp [Code.resultFormation, atType]
  · simp [assemble, atTerm]
  · intro env
    exact (mem_truthCode _ _).mpr ⟨rfl, rfl⟩

#print axioms context_extension_valid_iff
#print axioms lambda_result_membership
#print axioms pair_result_membership
#print axioms reflexivity_result_membership

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
