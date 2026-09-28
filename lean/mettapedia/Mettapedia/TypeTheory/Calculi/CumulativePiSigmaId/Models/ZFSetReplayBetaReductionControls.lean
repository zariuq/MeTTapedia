import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayBetaReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayVariableMembership
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayApplicationComparisonControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayInterpretationControls

/-!
# Executing root beta contraction on retained certificates

These controls exercise the actual certificate transformer: two internal
universe domains, cumulative result wrappers, and capture-avoiding returned
closures. An ignored ill-typed argument demonstrates why successful mechanical
contraction, even to an accepted reduct, does not authorize the source.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayBetaReductionControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay
open ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)

universe u

namespace PairProgram

open ZFSetReplayApplicationComparisonControls

theorem lower_contracts : lowerCode.contractBeta body (.var 0) pairType = some reductCode := rfl
theorem upper_contracts : upperCode.contractBeta body (.var 0) pairType = some reductCode := rfl

/-- Distinct accepted source trees compute the same retained reduct tree,
including both occurrences of the argument in the dependent pair. -/
theorem contracted_pair_checked :
    check Tower.rules noConversionCheck context reduct pairType reductCode = true :=
  lowerCode.contractBeta_result_checked Tower.rules reductCode lower_checked lower_contracts

theorem pair_judgment_contracts :
    ∃ result, upperCode.contractBeta body (.var 0) pairType = some result ∧
      checkJudgment Tower.rules noConversionCheck context reduct pairType contextCode result = true ∧
      StepCore Tower.rules.computation Tower.rules.headEq term reduct := by
  apply upperCode.contractBeta_judgment Tower.rules contextCode
  simpa only [checkJudgment, Bool.and_eq_true, term] using And.intro context_checked upper_checked

theorem unsuitable_root_returns_none :
    (Code.var : Code Tower.Head NoConversion 1).contractBeta body (.var 0) pairType = none := rfl

/-- Domain admission is derived from the checked variable argument and its
formed context. Universe inclusion is supplied once as the model's general
cumulativity law, rather than as two manually established memberships. -/
theorem pair_domains_admitted (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (env : Environment.{u} 1) (admitted : valid h env) :
    RootBetaAdmitted (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (.var 0) pairType env lowerCode ∧
    RootBetaAdmitted (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (.var 0) pairType env upperCode := by
  have monotone : ∀ lower upper, Tower.rules.cumulative lower upper →
      interpretHead h ∅ (twoCode h).1 (fun _ => 0) lower ⊆
        interpretHead h ∅ (twoCode h).1 (fun _ => 0) upper :=
    fun _ _ below => ZFSetReplayUniverseFormation.cumulative_subset h ∅ (twoCode h).1 (fun _ => 0) below
  constructor
  · exact rootBeta_variable_admitted (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      Tower.rules monotone contextCode 0 (.head (.sort Tower.zero)) pairType body
      (.sort (.max (.succ Tower.zero) (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))))
      (.sort (.succ Tower.zero)) (.sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))
      lowerFormation .headType .var pairFormation lowerBodyCode context_checked lower_checked
      rfl rfl (context_assembles h constants) env admitted
  · exact rootBeta_variable_admitted (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      Tower.rules monotone contextCode 0 (.head (.sort (.succ Tower.zero))) pairType body
      (.sort (.max (.succ (.succ Tower.zero)) (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))))
      (.sort (.succ (.succ Tower.zero))) (.sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))
      upperFormation .headType (.cumul (.sort Tower.zero) .var) pairFormation upperBodyCode
      context_checked upper_checked rfl rfl (context_assembles h constants) env admitted

/-- The checked algorithmic result, not a substitute typing certificate,
has the source value at every admitted argument. -/
theorem pair_contraction_preserves_value (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (source : Meaning.{u} 1)
    (atSource : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerCode term pairType = some source)
    (env : Environment.{u} 1) (admitted : valid h env) :
    ∃ target, assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      reductCode reduct pairType = some target ∧ source.value env = target.value env :=
  contractBeta_value (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants Tower.rules
    lowerCode source lower_checked atSource lower_contracts env
    (pair_domains_admitted h constants env admitted).1

/-- Root-beta coherence consumes the independently qualified reduct and
both retained-domain admission proofs, without identifying the domains. -/
theorem pair_certificates_coherent (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (lower upper : Meaning.{u} 1)
    (atLower : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerCode term pairType = some lower)
    (atUpper : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperCode term pairType = some upper)
    (env : Environment.{u} 1) (admitted : valid h env) : lower.value env = upper.value env :=
  rootBeta_coherent_of_normal_reduct (interpretHead h ∅ (twoCode h).1 (fun _ => 0))
    constants Tower.rules lowerCode upperCode reductCode lower upper reductMeaning
    lower_checked upper_checked atLower atUpper reduct_checked reduct_qualified
    (reduct_assembles h constants) env
    (pair_domains_admitted h constants env admitted).1 (pair_domains_admitted h constants env admitted).2

end PairProgram

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

namespace CumulativeResult

def identityBody : Tower.Tm 2 := .var 0
def identityTerm : Tower.Tm 1 := .app (.lam identityBody) (.var 0)
def identityCode : Replay 1 :=
  .appElim (.head zero) (.head zero)
    (.lamIntro (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))
      (.piForm one one .headType .headType) .var) .var
def raisedCode : Replay 1 := .cumul zero identityCode
def raisedReductCode : Replay 1 := .cumul zero .var

theorem raised_checked : check Tower.rules noConversionCheck
    ZFSetReplayApplicationComparisonControls.context identityTerm (.head one) raisedCode = true := by
  decide

theorem raised_contracts :
    raisedCode.contractBeta identityBody (.var 0) (.head one) = some raisedReductCode := rfl

theorem raised_reduct_checked : check Tower.rules noConversionCheck
    ZFSetReplayApplicationComparisonControls.context (.var 0) (.head one) raisedReductCode = true :=
  raisedCode.contractBeta_result_checked Tower.rules raisedReductCode raised_checked raised_contracts

theorem cumulative_wrapper_retained : raisedReductCode ≠ (Code.var : Replay 1) := by
  intro equal
  cases equal

theorem cumulative_nonhead_returns_none :
    raisedCode.contractBeta identityBody (.var 0) (.pi ground ground) = none := rfl

/-- A cumulative wrapper around the source and generated target remains
present while the semantic beta theorem follows the inner retained domain. -/
theorem raised_contraction_preserves_value (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (source : Meaning.{u} 1)
    (atSource : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      raisedCode identityTerm (.head one) = some source)
    (env : Environment.{u} 1) (inside : env 0 ∈ universeSet h ∅ 0) :
    ∃ target, assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      raisedReductCode (.var 0) (.head one) = some target ∧
      source.value env = target.value env := by
  apply contractBeta_value (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants Tower.rules
    raisedCode source raised_checked atSource raised_contracts env
  exact ⟨⟨fun _ => ZFSetTraceProducts.tracePiSet (universeSet h ∅ 0)
    (fun _ => universeSet h ∅ 0), some (fun _ => universeSet h ∅ 0)⟩,
    .plain (fun env => env 0), (fun _ => universeSet h ∅ 0), rfl, rfl, rfl, inside⟩

end CumulativeResult

namespace ReturnedClosure

open ZFSetReplayInterpretationControls

theorem closure_contracts : keepOpenApplicationCode.contractBeta keepOpenBody (.var 0)
    (.pi ground ground) = some keepOpenReductCode := rfl

theorem closure_reduct_checked : check Tower.rules noConversionCheck (.snoc .nil ground)
    keepOpenReduct (.pi ground ground) keepOpenReductCode = true :=
  keepOpenApplicationCode.contractBeta_result_checked Tower.rules keepOpenReductCode
    keep_open_application_checked closure_contracts

theorem closure_keeps_outer_variable : keepOpenReduct = .lam (.var 1) := rfl

theorem closure_does_not_capture : keepOpenReduct ≠ (.lam (.var 0) : Tower.Tm 1) := by
  decide

end ReturnedClosure

namespace RejectedSource

def context : Tower.Ctx 1 := .snoc .nil ground
def contextCode : ContextCode Tower.Head NoConversion 1 := .snoc .nil zero .headType
def body : Tower.Tm 2 := .var 1
def argument : Tower.Tm 1 := .head zero
def term : Tower.Tm 1 := .app (.lam body) argument
def sourceCode : Replay 1 :=
  .appElim ground ground
    (.lamIntro (.sort (.max Tower.zero Tower.zero))
      (.piForm zero zero .headType .headType) .var) .headType

theorem context_checked : checkContext Tower.rules noConversionCheck context contextCode = true := by
  decide

theorem source_rejected :
    check Tower.rules noConversionCheck context term ground sourceCode = false := by decide

theorem rejected_source_contracts : sourceCode.contractBeta body argument ground = some .var := rfl

theorem reduct_checked :
    check Tower.rules noConversionCheck context (inst0 argument body) ground (Code.var : Replay 1) = true := by
  decide

/-- The transformer succeeds and the reduct checks, but their conjunction
does not imply that the original application was well typed. -/
theorem contraction_does_not_authorize_source :
    sourceCode.contractBeta body argument ground = some .var ∧
      checkJudgment Tower.rules noConversionCheck context (inst0 argument body) ground contextCode .var = true ∧
      checkJudgment Tower.rules noConversionCheck context term ground contextCode sourceCode = false := by
  exact ⟨rejected_source_contracts, by decide, by decide⟩

end RejectedSource

#print axioms PairProgram.contracted_pair_checked
#print axioms PairProgram.pair_judgment_contracts
#print axioms PairProgram.pair_contraction_preserves_value
#print axioms PairProgram.pair_certificates_coherent
#print axioms CumulativeResult.raised_reduct_checked
#print axioms CumulativeResult.raised_contraction_preserves_value
#print axioms ReturnedClosure.closure_reduct_checked
#print axioms ReturnedClosure.closure_does_not_capture
#print axioms RejectedSource.contraction_does_not_authorize_source

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayBetaReductionControls
