import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayElimination
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContext
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayNeutral
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceUniverseInterpretation

/-!
# A neutral program whose extracted formation contains beta redexes

The formed context has x : Ground and
g : Π(F : Ground → U₀). (F x → F x).
The neutral application g (λ_. Ground) returns an endomorphism whose displayed
domain is (λ_. Ground) x. Actual result-formation extraction therefore produces
beta redexes even though the term and context formation use neutral eliminations.

The context has real inhabitants: g can be the family of identity functions.
Semantic membership uses the existing application law and the exact extracted
formation, without imposing normality on that generated type or introducing
an implicit conversion rule.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayFormationRedex

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph graph_mem_piSet)
open ZFSetTraceProducts (traceLam traceApp tracePiSet mem_tracePiSet traceApp_graph_beta)

universe u

private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n
private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev functionLevel : Tower.Head := .sort (.max Tower.zero (.succ Tower.zero))
private abbrev identityLevel : Tower.Head := .sort (.max Tower.zero Tower.zero)
private abbrev operatorLevel : Tower.Head :=
  .sort (.max (.max Tower.zero (.succ Tower.zero)) (.max Tower.zero Tower.zero))
private abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround

def functionType {n : Nat} : Tower.Tm n := .pi ground (.head zero)
def functionFormation {n : Nat} : Replay n := .piForm zero one .headType .headType
def operatorType : Tower.Tm 1 :=
  .pi functionType (.pi (.app (.var 0) (.var 1)) (.app (.var 1) (.var 2)))
def familyCode {n : Nat} : Replay n :=
  .piForm zero zero (.appElim ground (.head zero) .var .var)
    (.appElim ground (.head zero) .var .var)
def operatorFormation {n : Nat} : Replay n :=
  .piForm functionLevel identityLevel functionFormation familyCode

def context : Tower.Ctx 2 := .snoc (.snoc .nil ground) operatorType
def contextCode : ContextCode Tower.Head NoConversion 2 :=
  .snoc (.snoc .nil zero .headType) operatorLevel operatorFormation
def argument : Tower.Tm 2 := .lam ground
def argumentCode : Replay 2 := .lamIntro functionLevel functionFormation .headType
def family : Tower.Tm 3 :=
  .pi (.app (.var 0) (.var 2)) (.app (.var 1) (.var 3))
def program : Tower.Tm 2 := .app (.var 0) argument
def displayedType : Tower.Tm 2 := inst0 argument family
def programCode : Replay 2 := .appElim functionType family .var argumentCode

def resultFormation : Replay 2 :=
  Code.instantiate noConversionRename noConversionSubstitute family (.head identityLevel)
    argument familyCode argumentCode

theorem context_checked : checkContext Tower.rules noConversionCheck context contextCode = true := by decide
theorem program_checked : check Tower.rules noConversionCheck context program displayedType programCode = true := by decide
theorem program_neutral : programCode.neutralEliminations program displayedType = true := by decide
theorem operator_formation_neutral :
    (operatorFormation : Replay 1).neutralEliminations operatorType (.head operatorLevel) = true := by decide

theorem extraction_exact :
    programCode.resultFormation noConversionRename noConversionSubstitute TowerDecisions.headTarget
      contextCode program displayedType = some (identityLevel, resultFormation) := rfl

theorem result_formation_checked :
    check Tower.rules noConversionCheck context displayedType (.head identityLevel) resultFormation = true := by decide

theorem result_formation_not_neutral :
    resultFormation.neutralEliminations displayedType (.head identityLevel) = false := by decide

theorem displayed_type_contains_redex :
    displayedType = .pi (.app (.lam ground) (.var 1)) (.app (.lam ground) (.var 2)) := rfl

theorem displayed_type_not_syntactic_ground_arrow : displayedType ≠ .pi ground ground := by decide

noncomputable def functions (h : CofinalInaccessibles.{u}) : ZFSet.{u} :=
  tracePiSet (twoCode h).1 (fun _ => universeSet h ∅ 0)

noncomputable def identityType (A : ZFSet.{u}) : ZFSet.{u} := tracePiSet A (fun _ => A)

noncomputable def constantGround (h : CofinalInaccessibles.{u}) : ZFSet.{u} :=
  traceLam (graph (twoCode h).1 (fun _ => (twoCode h).1))

noncomputable def valid (h : CofinalInaccessibles.{u}) (env : Environment.{u} 2) : Prop :=
  (True ∧ env 1 ∈ (twoCode h).1) ∧
    env 0 ∈ tracePiSet (functions h) (fun F => identityType (traceApp F (env 1)))

theorem context_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants contextCode context =
      some (valid h) := rfl

noncomputable def programMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 2 :=
  .plain (fun env => traceApp (env 0) (constantGround h))

noncomputable def typeMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 2 :=
  ⟨fun env => identityType (traceApp (constantGround h) (env 1)),
    some (fun env => traceApp (constantGround h) (env 1))⟩

theorem program_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      programCode program displayedType = some (programMeaning h) := rfl

theorem type_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      resultFormation displayedType (.head identityLevel) = some (typeMeaning h) := rfl

theorem argument_in_domain (h : CofinalInaccessibles.{u}) : constantGround h ∈ functions h := by
  apply mem_tracePiSet.mpr
  exact ⟨graph (twoCode h).1 (fun _ => (twoCode h).1),
    graph_mem_piSet (fun _ _ => (twoCode h).2), rfl⟩

noncomputable def identityOperator (h : CofinalInaccessibles.{u}) (x : ZFSet.{u}) : ZFSet.{u} :=
  traceLam (graph (functions h) (fun F => traceLam (graph (traceApp F x) id)))

theorem identity_operator_typed (h : CofinalInaccessibles.{u}) (x : ZFSet.{u}) :
    identityOperator h x ∈ tracePiSet (functions h) (fun F => identityType (traceApp F x)) := by
  apply mem_tracePiSet.mpr
  refine ⟨_, graph_mem_piSet ?_, rfl⟩
  intro F _
  apply mem_tracePiSet.mpr
  exact ⟨_, graph_mem_piSet (fun _ inside => inside), rfl⟩

noncomputable def inhabitedEnvironment (h : CofinalInaccessibles.{u}) : Environment.{u} 2 :=
  Fin.cases (identityOperator h ∅) (fun _ => ∅)

theorem environment_valid (h : CofinalInaccessibles.{u}) : valid h (inhabitedEnvironment h) :=
  ⟨⟨True.intro, ZFSetDependentProducts.Controls.empty_mem_two⟩, identity_operator_typed h ∅⟩

/-- The existing application theorem validates the program against the exact
formation extracted above. Function membership comes from the interpreted
context, and the lambda argument's membership is proved in the actual tower. -/
theorem program_has_extracted_type (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (env : Environment.{u} 2) (admitted : valid h env) :
    (programMeaning h).value env ∈ (typeMeaning h).value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  let functionMeaning : Meaning.{u} 2 := .plain (fun values => values 0)
  let functionTypeMeaning : Meaning.{u} 2 :=
    ⟨fun values => tracePiSet (functions h) (fun F => identityType (traceApp F (values 1))),
      some (fun _ => functions h)⟩
  let domainMeaning : Meaning.{u} 2 :=
    ⟨fun _ => functions h, some (fun _ => (twoCode h).1)⟩
  let familyMeaning : Meaning.{u} 3 :=
    ⟨fun values => identityType (traceApp (values 0) (values 2)),
      some (fun values => traceApp (values 0) (values 2))⟩
  obtain ⟨resultType, _, assembled, member⟩ :=
    application_result_membership heads constants noConversionRename noConversionSubstitute
      TowerDecisions.headTarget Tower.rules noConversionCheck
      context contextCode functionType (.var 0) argument family
      .var argumentCode operatorFormation functionFormation familyCode
      operatorLevel functionLevel identityLevel
      functionMeaning functionTypeMeaning domainMeaning (.plain (fun _ => constantGround h))
      (programMeaning h) familyMeaning
      rfl rfl (by decide) rfl rfl rfl rfl rfl (program_assembles h constants)
      env admitted.2 (argument_in_domain h)
  change assemble heads constants resultFormation displayedType (.head identityLevel) = some resultType at assembled
  rw [type_assembles] at assembled
  cases Option.some.inj assembled
  exact member

theorem program_is_ground_endomorphism (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (env : Environment.{u} 2) (admitted : valid h env) :
    (programMeaning h).value env ∈ identityType (twoCode h).1 := by
  have member := program_has_extracted_type h constants env admitted
  change (programMeaning h).value env ∈ identityType (traceApp (constantGround h) (env 1)) at member
  rw [show traceApp (constantGround h) (env 1) = (twoCode h).1 from
    traceApp_graph_beta _ admitted.1.2] at member
  exact member

/-- The exhibited valid environment computes the actual identity function,
not merely some inhabitant of an empty or conditionally assumed context. -/
theorem exhibited_program_is_identity (h : CofinalInaccessibles.{u}) :
    (programMeaning h).value (inhabitedEnvironment h) = traceLam (graph (twoCode h).1 id) := by
  change traceApp (traceLam (graph (functions h) _)) (constantGround h) = _
  rw [traceApp_graph_beta _ (argument_in_domain h)]
  rw [show traceApp (constantGround h) ∅ = (twoCode h).1 from
    traceApp_graph_beta _ ZFSetDependentProducts.Controls.empty_mem_two]

theorem exhibited_program_computes (h : CofinalInaccessibles.{u})
    (value : ZFSet.{u}) (inside : value ∈ (twoCode h).1) :
    traceApp ((programMeaning h).value (inhabitedEnvironment h)) value = value := by
  rw [exhibited_program_is_identity, traceApp_graph_beta _ inside]
  rfl

#print axioms context_checked
#print axioms program_checked
#print axioms extraction_exact
#print axioms result_formation_checked
#print axioms result_formation_not_neutral
#print axioms displayed_type_not_syntactic_ground_arrow
#print axioms argument_in_domain
#print axioms environment_valid
#print axioms program_has_extracted_type
#print axioms program_is_ground_endomorphism
#print axioms exhibited_program_is_identity
#print axioms exhibited_program_computes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayFormationRedex
