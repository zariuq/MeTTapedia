import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayComputedArgumentConstantReturn
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputedApplicationFamily

/-!
# A computed application selects a dependent identity family

At every finite depth, two checked versions of an identity-application
computation are fed to a constant-returning lambda. The lambda's domains are
different object-theory universes, but both applications return the older
context variable. Their results instantiate one non-diagonal identity family
through the actual certificate-instantiation operation. A forged certificate
for the computed argument remains rejected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedApplicationFamilyControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet TraceFunctionRelated
  traceFunctionRelated_graph_iff)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayApplicationComparisonControls (context contextCode context_checked
  context_assembles valid)
open ZFSetReplayComputedArgumentControls (program lowerCode upperCode lower_assembles
  upper_assembles programMeaning computed_values_agree)
open ZFSetReplayQualifiedApplicationControls (lower_argument_qualified upper_argument_qualified)
open ZFSetReplayComputedArgumentConstantReturn (term lowerFormation upperFormation
  lowerApplicationCode upperApplicationCode lower_checked upper_checked
  lower_returns_context_value)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n
private abbrev lowerJoin : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))
private abbrev upperJoin : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ Tower.zero))

def family : Tower.Tm 2 := .id (.head zero) (.var 0) (.var 1)
def familyCode : Replay 2 := .idForm one .headType .var .var

theorem family_checked :
    check Tower.rules noConversionCheck (.snoc context (.head zero)) family
      (.head one) familyCode = true := by decide

theorem family_qualified :
    familyCode.neutralEliminations family (.head one) = true := rfl

noncomputable def formationMeaning (h : CofinalInaccessibles.{u}) (level : Nat) :
    Meaning.{u} 1 :=
  ⟨fun _ => tracePiSet (universeSet h ∅ level) (fun _ => universeSet h ∅ 0),
    some (fun _ => universeSet h ∅ level)⟩

noncomputable def functionMeaning (h : CofinalInaccessibles.{u}) (level : Nat) :
    Meaning.{u} 1 :=
  .plain (fun env => traceLam (graph (universeSet h ∅ level) (fun _ => env 0)))

theorem formations_assemble (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerFormation (.pi (.head zero) (.head zero)) (.head lowerJoin) =
        some (formationMeaning h 0) ∧
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperFormation (.pi (.head one) (.head zero)) (.head upperJoin) =
        some (formationMeaning h 1) := ⟨rfl, rfl⟩

theorem functions_assemble (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (.lamIntro lowerJoin lowerFormation .var) (.lam (.var 1))
      (.pi (.head zero) (.head zero)) = some (functionMeaning h 0) ∧
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (.lamIntro upperJoin upperFormation .var) (.lam (.var 1))
      (.pi (.head one) (.head zero)) = some (functionMeaning h 1) := ⟨rfl, rfl⟩

theorem functions_related (h : CofinalInaccessibles.{u})
    (env : Environment.{u} 1) :
    TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
      ((functionMeaning h 0).value env) ((functionMeaning h 1).value env) := by
  change TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
    (traceLam (graph (universeSet h ∅ 0) (fun _ => env 0)))
    (traceLam (graph (universeSet h ∅ 1) (fun _ => env 0)))
  apply (traceFunctionRelated_graph_iff _ _ Eq Eq _ _).mpr
  intro _ _ _ _ _
  rfl

/-- The two generated identity formations agree for every admitted input,
even though their argument computation can be arbitrarily deep and their
function graphs have different retained domains. -/
theorem checked_application_identity_family_formations (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    let leftApp := term depth
    let rightApp := term depth
    let leftInstance := Code.instantiate noConversionRename noConversionSubstitute
      family (.head one) leftApp familyCode (lowerApplicationCode depth)
    let rightInstance := Code.instantiate noConversionRename noConversionSubstitute
      family (.head one) rightApp familyCode (upperApplicationCode depth)
    check Tower.rules noConversionCheck context (inst0 leftApp family)
      (.head one) leftInstance = true ∧
    check Tower.rules noConversionCheck context (inst0 rightApp family)
      (.head one) rightInstance = true ∧
    ∃ left right : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        leftInstance (inst0 leftApp family) (.head one) = some left ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        rightInstance (inst0 rightApp family) (.head one) = some right ∧
      ∀ env, valid h env → left.value env = right.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨leftResult, atLeft, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck (lowerApplicationCode depth) (lower_checked depth)
  obtain ⟨rightResult, atRight, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck (upperApplicationCode depth) (upper_checked depth)
  simpa only [term, lowerApplicationCode, upperApplicationCode] using
    (qualified_computed_applications_family_values heads constants Tower.rules
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
      successor_qualified (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
      (empty_constants_model heads constants) context contextCode (valid h)
      context_checked (context_assembles h constants) lowerJoin upperJoin
      (.head zero) (.head one) (.head zero) (.head zero)
      (.lam (.var 1)) (.lam (.var 1)) (program depth) (program depth)
      lowerFormation upperFormation (.lamIntro lowerJoin lowerFormation .var)
      (.lamIntro upperJoin upperFormation .var) (lowerCode depth) (upperCode depth)
      (formationMeaning h 0) (formationMeaning h 1) (functionMeaning h 0)
      (functionMeaning h 1) (programMeaning h 0 depth) (programMeaning h 1 depth)
      leftResult rightResult (fun _ => universeSet h ∅ 0) (fun _ => universeSet h ∅ 1)
      (by decide) (by decide) (lower_checked depth) (upper_checked depth)
      (lower_argument_qualified depth) (upper_argument_qualified depth)
      (formations_assemble h constants).1 (formations_assemble h constants).2
      rfl rfl (functions_assemble h constants).1 (functions_assemble h constants).2
      (lower_assembles h constants depth) (upper_assembles h constants depth)
      atLeft atRight rfl
      (fun env admitted => computed_values_agree h constants depth env admitted)
      (fun env _ => functions_related h env)
      family one one familyCode familyCode family_checked family_checked family_qualified)

/-- The equality witness is genuinely available in both independently
generated fibres on valid environments. It comes from the checked program's
computed return value, not from declaring the two set codes equal by fiat. -/
theorem computed_application_identity_fibres_inhabited (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    let leftInstance := Code.instantiate noConversionRename noConversionSubstitute
      family (.head one) (term depth) familyCode (lowerApplicationCode depth)
    let rightInstance := Code.instantiate noConversionRename noConversionSubstitute
      family (.head one) (term depth) familyCode (upperApplicationCode depth)
    ∃ left right : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        leftInstance (inst0 (term depth) family) (.head one) = some left ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        rightInstance (inst0 (term depth) family) (.head one) = some right ∧
      ∀ env, valid h env →
        (∅ : ZFSet.{u}) ∈ left.value env ∧ ∅ ∈ right.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨_, _, left, right, atLeft, atRight, agree⟩ :=
    checked_application_identity_family_formations h constants depth
  obtain ⟨lowerResult, atLowerResult, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck (lowerApplicationCode depth) (lower_checked depth)
  let familyMeaning : Meaning.{u} 2 :=
    .plain (fun env => truthCode (env 0 = env 1))
  have atFamily : assemble heads constants familyCode family (.head one) =
      some familyMeaning := rfl
  obtain ⟨instantiated, atInstantiated, valueInstantiated⟩ :=
    assemble_instantiate noConversionRename noConversionSubstitute heads constants
      Tower.rules noConversionCheck familyCode (lowerApplicationCode depth)
      familyMeaning lowerResult family_checked atFamily atLowerResult
  change assemble heads constants _ (inst0 (term depth) family) (.head one) =
    some instantiated at atInstantiated
  rw [atLeft] at atInstantiated
  cases Option.some.inj atInstantiated
  refine ⟨left, right, atLeft, atRight, ?_⟩
  intro env admitted
  have leftMember : (∅ : ZFSet.{u}) ∈ left.value env := by
    rw [valueInstantiated]
    change (∅ : ZFSet.{u}) ∈ truthCode (lowerResult.value env = env 0)
    exact (mem_truthCode _ ∅).mpr
      ⟨rfl, lower_returns_context_value h constants depth lowerResult atLowerResult env admitted⟩
  exact ⟨leftMember, (agree env admitted) ▸ leftMember⟩

def forgedApplicationCode : Nat → Replay 1 := fun _ =>
  .appElim (.head zero) (.head zero)
    (.lamIntro lowerJoin lowerFormation .var) .var

def forgedFamilyInstance (depth : Nat) : Replay 1 :=
  Code.instantiate noConversionRename noConversionSubstitute family (.head one)
    (term (depth + 1)) familyCode (forgedApplicationCode depth)

/-- The dependent-family certificate cannot turn a forged application
certificate into an accepted one. The omitted evidence is for the computed
argument, not for the identity family itself. -/
theorem forged_family_instance_rejected (depth : Nat) :
    check Tower.rules noConversionCheck context
      (inst0 (term (depth + 1)) family) (.head one)
      (forgedFamilyInstance depth) = false := by
  rfl

#print axioms checked_application_identity_family_formations
#print axioms computed_application_identity_fibres_inhabited
#print axioms forged_family_instance_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedApplicationFamilyControls
