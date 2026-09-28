import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContext
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceUniverseInterpretation

/-!
# Replay agreement requires a valid environment

In the formed context y : Ground, X : U₀, the term (λ_. y) X has two
accepted certificates, using function domains U₀ and U₁ respectively. Their
values agree on every environment admitted by context interpretation. They
differ at X = U₀, which is not an inhabitant of its declared type U₀.

Thus equality of assembled value functions on all raw environments is false,
even with no conversion payloads and identical subject, context and displayed
type. This is not a counterexample to agreement on valid environments, nor a
proof of that agreement for arbitrary certificates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayEnvironmentBoundary

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp traceApp_graph_beta)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround

def context : Tower.Ctx 2 := .snoc (.snoc .nil ground) (.head zero)
def contextCode : ContextCode Tower.Head NoConversion 2 :=
  .snoc (.snoc .nil zero .headType) one .headType
def term : Tower.Tm 2 := .app (.lam (.var 2)) (.var 0)

def lowerCode : Code Tower.Head NoConversion 2 :=
  .appElim (.head zero) ground
    (.lamIntro (.sort (.max (.succ Tower.zero) Tower.zero))
      (.piForm one zero .headType .headType) .var) .var

def upperCode : Code Tower.Head NoConversion 2 :=
  .appElim (.head one) ground
    (.lamIntro (.sort (.max (.succ (.succ Tower.zero)) Tower.zero))
      (.piForm two zero .headType .headType) .var) (.cumul zero .var)

theorem context_checked : checkContext Tower.rules noConversionCheck context contextCode = true := by
  decide

theorem lower_checked : check Tower.rules noConversionCheck context term ground lowerCode = true := by
  decide

theorem upper_checked : check Tower.rules noConversionCheck context term ground upperCode = true := by
  decide

noncomputable def meaning (h : CofinalInaccessibles.{u}) (level : Nat) : Meaning.{u} 2 :=
  .plain (fun env => traceApp (traceLam (graph (universeSet h ∅ level) (fun _ => env 1))) (env 0))

noncomputable def valid (h : CofinalInaccessibles.{u}) (env : Environment.{u} 2) : Prop :=
  (True ∧ env 1 ∈ (twoCode h).1) ∧ env 0 ∈ universeSet h ∅ 0

theorem context_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants contextCode context =
      some (valid h) := rfl

theorem lower_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants lowerCode term ground =
      some (meaning h 0) := rfl

theorem upper_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants upperCode term ground =
      some (meaning h 1) := rfl

theorem meanings_agree_on_valid_environment (h : CofinalInaccessibles.{u})
    (env : Environment.{u} 2) (admitted : valid h env) :
    (meaning h 0).value env = env 1 ∧ (meaning h 1).value env = env 1 := by
  exact ⟨traceApp_graph_beta _ admitted.2,
    traceApp_graph_beta _ (universeSet_subset_next h ∅ 0 admitted.2)⟩

theorem assembled_values_agree_on_valid_environment (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (lower upper : Meaning.{u} 2)
    (atLower : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerCode term ground = some lower)
    (atUpper : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperCode term ground = some upper)
    (env : Environment.{u} 2) (admitted : valid h env) : lower.value env = upper.value env := by
  rw [lower_assembles] at atLower
  rw [upper_assembles] at atUpper
  cases Option.some.inj atLower
  cases Option.some.inj atUpper
  obtain ⟨left, right⟩ := meanings_agree_on_valid_environment h env admitted
  exact left.trans right.symm

private theorem application_outside_domain {A x y : ZFSet.{u}} (outside : x ∉ A) :
    traceApp (traceLam (graph A (fun _ => y))) x = ∅ := by
  apply ZFSet.ext
  intro z
  rw [ZFSetTraceProducts.mem_traceApp, ZFSetTraceProducts.pair_mem_traceLam]
  constructor
  · rintro ⟨value, member, _⟩
    exact (outside (ZFSetDependentProducts.pair_mem_graph.mp member).1).elim
  · exact fun impossible => (ZFSet.notMem_empty z impossible).elim

noncomputable def invalidEnvironment (h : CofinalInaccessibles.{u}) : Environment.{u} 2 :=
  Fin.cases (universeSet h ∅ 0) (fun _ => ZFSet.powerset ∅)

theorem environment_not_valid (h : CofinalInaccessibles.{u}) : ¬ valid h (invalidEnvironment h) := by
  intro admitted
  exact universeSet_no_self_membership h ∅ 0 admitted.2

theorem invalid_environment_values (h : CofinalInaccessibles.{u}) :
    (meaning h 0).value (invalidEnvironment h) = ∅ ∧
      (meaning h 1).value (invalidEnvironment h) = ZFSet.powerset ∅ := by
  exact ⟨application_outside_domain (universeSet_no_self_membership h ∅ 0),
    traceApp_graph_beta _ (universeSet_mem_next h ∅ 0)⟩

/-- The actual accepted certificates do not induce the same function on all
raw environments. Restricting a coherence statement to valid inputs is essential. -/
theorem assembled_value_functions_differ (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (lower upper : Meaning.{u} 2)
    (atLower : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerCode term ground = some lower)
    (atUpper : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperCode term ground = some upper) : lower.value ≠ upper.value := by
  rw [lower_assembles] at atLower
  rw [upper_assembles] at atUpper
  cases Option.some.inj atLower
  cases Option.some.inj atUpper
  intro equal
  have atEnv := congrFun equal (invalidEnvironment h)
  obtain ⟨left, right⟩ := invalid_environment_values h
  rw [left, right] at atEnv
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ := by simp
  rw [← atEnv] at member
  exact ZFSet.notMem_empty _ member

/-- The positive side is not vacuous: the empty type and a nonempty ground
value form a valid environment, and both accepted terms return the ground value. -/
theorem valid_environment_exists (h : CofinalInaccessibles.{u}) :
    valid h (Fin.cases ∅ (fun _ => ZFSet.powerset ∅)) :=
  ⟨⟨True.intro, ZFSetDependentProducts.Controls.power_empty_mem_two⟩, seed_mem_zero h ∅⟩

#print axioms context_checked
#print axioms lower_checked
#print axioms upper_checked
#print axioms assembled_values_agree_on_valid_environment
#print axioms environment_not_valid
#print axioms invalid_environment_values
#print axioms assembled_value_functions_differ
#print axioms valid_environment_exists

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayEnvironmentBoundary
