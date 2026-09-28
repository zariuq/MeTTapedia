import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBodyPathCoherence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedApplicationControls

/-!
# A checked computed body at two cumulative product domains

The argument is a recursively nested identity computation. The lambda body
itself applies another identity lambda to its bound variable, so its meaning
depends on a retained product certificate before contraction. Lower and upper
universe routes use different body contexts and certificates, then reach the
same supported variable. The comparison is only on valid environments.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedBodyApplicationControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayApplicationComparisonControls (context contextCode context_checked
  context_assembles valid)
open ZFSetReplayQualifiedApplicationControls (lower_argument_qualified
  upper_argument_qualified lower_argument_path upper_argument_path)
open ZFSetReplayComputedArgumentControls (program lowerCode upperCode lower_checked upper_checked)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev oneJoin : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))
private abbrev twoJoin : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
private abbrev Replay (m : Nat) := Code Tower.Head NoConversion m

def computedBody : Tower.Tm 2 := .app (.lam (.var 0)) (.var 0)

def lowerBodyCode : Replay 2 :=
  .appElim (.head zero) (.head zero)
    (.lamIntro oneJoin (.piForm one one .headType .headType) .var) .var

def upperBodyCode : Replay 2 :=
  .appElim (.head one) (.head one)
    (.lamIntro twoJoin (.piForm two two .headType .headType) .var) .var

def lowerFormation : Replay 1 := .piForm one one .headType .headType
def upperFormation : Replay 1 := .piForm two two .headType .headType

def computedProgram (depth : Nat) : Tower.Tm 1 :=
  .app (.lam computedBody) (program depth)

def lowerApplicationCode (depth : Nat) : Replay 1 :=
  .appElim (.head zero) (.head zero)
    (.lamIntro oneJoin lowerFormation lowerBodyCode) (lowerCode depth)

def upperApplicationCode (depth : Nat) : Replay 1 :=
  .appElim (.head one) (.head one)
    (.lamIntro twoJoin upperFormation upperBodyCode) (upperCode depth)

theorem lower_body_checked :
    check Tower.rules noConversionCheck (.snoc context (.head zero))
      computedBody (.head zero) lowerBodyCode = true := by decide

theorem upper_body_checked :
    check Tower.rules noConversionCheck (.snoc context (.head one))
      computedBody (.head one) upperBodyCode = true := by decide

theorem lower_application_checked (depth : Nat) :
    check Tower.rules noConversionCheck context (computedProgram depth)
      (.head zero) (lowerApplicationCode depth) = true := by
  change ((true && check Tower.rules noConversionCheck context (program depth)
    (.head zero) (lowerCode depth)) && true) = true
  simpa only [Bool.true_and, Bool.and_true] using lower_checked depth

theorem upper_application_checked (depth : Nat) :
    check Tower.rules noConversionCheck context (computedProgram depth)
      (.head one) (upperApplicationCode depth) = true := by
  change ((true && check Tower.rules noConversionCheck context (program depth)
    (.head one) (upperCode depth)) && true) = true
  simpa only [Bool.true_and, Bool.and_true] using upper_checked depth

theorem lower_body_contracts :
    lowerBodyCode.contractBeta (.var 0) (.var 0) (.head zero) = some .var := rfl

theorem upper_body_contracts :
    upperBodyCode.contractBeta (.var 0) (.var 0) (.head one) = some .var := rfl

theorem lower_body_qualified :
    lowerBodyCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      (.snoc contextCode one .headType) computedBody (.head zero) = true := by decide

theorem upper_body_qualified :
    upperBodyCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      (.snoc contextCode two .headType) computedBody (.head one) = true := by decide

theorem lower_body_path : QualifiedBetaPath Tower.rules TowerDecisions.headTarget
    (.snoc contextCode one .headType) (.head zero) computedBody lowerBodyCode
    (.var 0) .var := by
  exact .contraction lower_body_qualified lower_body_contracts
    (.terminal (.var 0) .var (by decide))

theorem upper_body_path : QualifiedBetaPath Tower.rules TowerDecisions.headTarget
    (.snoc contextCode two .headType) (.head one) computedBody upperBodyCode
    (.var 0) .var := by
  exact .contraction upper_body_qualified upper_body_contracts
    (.terminal (.var 0) .var (by decide))

theorem computed_body_not_structurally_supported :
    ZFSetTypeExpressionInterpretation.supported computedBody = false := rfl

/-- The upper body certificate cannot be reused at the lower displayed type.
Qualified paths compare two accepted routes; they do not turn an invalid
certificate into an accepted one. -/
theorem mismatched_body_certificate_rejected :
    check Tower.rules noConversionCheck (.snoc context (.head zero))
      computedBody (.head zero) upperBodyCode = false := by decide

noncomputable def lowerResultMeaning (h : CofinalInaccessibles.{u}) (depth : Nat) :
    Meaning.{u} 1 :=
  .plain (fun env =>
    ZFSetTraceProducts.traceApp
      (ZFSetTraceProducts.traceLam
        (ZFSetDependentProducts.graph (universeSet h ∅ 0)
          (fun x => ZFSetTraceProducts.traceApp
            (ZFSetTraceProducts.traceLam
              (ZFSetDependentProducts.graph (universeSet h ∅ 0) id)) x)))
      (ZFSetReplayComputedArgumentControls.iteratedValue h 0 depth (env 0)))

theorem lower_result_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (lowerApplicationCode depth) (computedProgram depth) (.head zero) =
      some (lowerResultMeaning h depth) := by
  simp only [lowerApplicationCode, computedProgram, lowerBodyCode, lowerFormation,
    computedBody, assemble, Option.pure_def,
    ZFSetReplayComputedArgumentControls.lower_assembles h constants depth]
  rfl

/-- On an actual context member the inner computation returns its bound
argument, and the outer computation returns the independently computed input. -/
theorem lower_result_returns_input (h : CofinalInaccessibles.{u})
    (env : Environment.{u} 1) (admitted : valid h env) (depth : Nat) :
    (lowerResultMeaning h depth).value env = env 0 := by
  have input := ZFSetReplayComputedArgumentControls.iterated_value_of_member h 0 depth
    (env 0) admitted.2
  change ZFSetTraceProducts.traceApp
    (ZFSetTraceProducts.traceLam
      (ZFSetDependentProducts.graph (universeSet h ∅ 0)
        (fun x => ZFSetTraceProducts.traceApp
          (ZFSetTraceProducts.traceLam
            (ZFSetDependentProducts.graph (universeSet h ∅ 0) id)) x)))
    (ZFSetReplayComputedArgumentControls.iteratedValue h 0 depth (env 0)) = env 0
  rw [input]
  rw [ZFSetTraceProducts.traceApp_graph_beta _ admitted.2]
  exact ZFSetTraceProducts.traceApp_graph_beta _ admitted.2

/-- Both accepted routes really execute the certificate-dependent inner
application. Their product domains and body contexts differ, while their
results agree wherever the source context is valid. -/
theorem computed_body_applications_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ lower upper : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerApplicationCode depth) (computedProgram depth) (.head zero) = some lower ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (upperApplicationCode depth) (computedProgram depth) (.head one) = some upper ∧
      ∀ env, valid h env → lower.value env = upper.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  exact qualified_cross_domain_lambda_applications_coherent_of_body_paths
    heads constants Tower.rules TowerDecisions.headTarget
    FormationSensitive.towerUniverseRegularity successor_qualified
    (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) context contextCode context_checked
    (context_assembles h constants) (.head zero) (.head one) (.head zero)
    (.head one) computedBody oneJoin twoJoin one one two two lowerFormation
    upperFormation (lowerCode depth) (upperCode depth) .headType .headType
    .headType .headType lowerBodyCode upperBodyCode .var .var
    (program depth) (program depth) (.var 0) .var (.cumul zero .var)
    (.var 0) (lower_application_checked depth) (upper_application_checked depth)
    (lower_argument_qualified depth) (upper_argument_qualified depth)
    (lower_argument_path depth) (upper_argument_path depth) rfl rfl rfl
    lower_body_path upper_body_path rfl

/-- The common checked result is the source context value. This combines the
qualified cross-domain comparison with the concrete two-stage beta meaning;
the upper route is not recomputed using an erased certificate. -/
theorem computed_body_both_return_input (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ lower upper : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerApplicationCode depth) (computedProgram depth) (.head zero) = some lower ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (upperApplicationCode depth) (computedProgram depth) (.head one) = some upper ∧
      ∀ env, valid h env → lower.value env = env 0 ∧ upper.value env = env 0 := by
  obtain ⟨lower, upper, atLower, atUpper, equal⟩ :=
    computed_body_applications_agree h constants depth
  have same : lower = lowerResultMeaning h depth :=
    Option.some.inj (atLower.symm.trans (lower_result_assembles h constants depth))
  subst lower
  refine ⟨lowerResultMeaning h depth, upper,
    lower_result_assembles h constants depth, atUpper, ?_⟩
  intro env admitted
  have returned := lower_result_returns_input h env admitted depth
  exact ⟨returned, (equal env admitted).symm.trans returned⟩

#print axioms lower_body_checked
#print axioms upper_body_checked
#print axioms computed_body_applications_agree
#print axioms computed_body_both_return_input
#print axioms computed_body_not_structurally_supported
#print axioms mismatched_body_certificate_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedBodyApplicationControls
