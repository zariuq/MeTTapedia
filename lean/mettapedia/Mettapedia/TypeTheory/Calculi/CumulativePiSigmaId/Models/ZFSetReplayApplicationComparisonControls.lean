import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayApplicationComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayNeutral
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContext
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceUniverseInterpretation

/-!
# Comparing applications with different retained lambda domains

In the context `X : U₀`, the program `(λx. (x, refl x)) X` has two checked
certificates: the lambda can bind an element of `U₀` or of `U₁`. Both display
the dependent result type `Σ z : U₁, Id U₁ z z`. The result retains the actual
input set, rather than ignoring the argument across the universe boundary.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayApplicationComparisonControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph sigmaSet)
open ZFSetTraceProducts (traceLam traceApp traceApp_graph_beta tracePiSet)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev pairLevel : Tower.Head := .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
private abbrev lowerLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))
private abbrev upperLevel : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def context : Tower.Ctx 1 := .snoc .nil (.head zero)
def contextCode : ContextCode Tower.Head NoConversion 1 := .snoc .nil one .headType
def pairType {n : Nat} : Tower.Tm n := .sigma (.head one) (.id (.head one) (.var 0) (.var 0))
def pairFormation {n : Nat} : Replay n :=
  .sigmaForm two two .headType (.idForm two .headType .var .var)
def body : Tower.Tm 2 := .pair (.var 0) (.refl (.var 0))
def term : Tower.Tm 1 := .app (.lam body) (.var 0)
def reduct : Tower.Tm 1 := .pair (.var 0) (.refl (.var 0))

def lowerBodyCode : Replay 2 :=
  .pairIntro pairLevel pairFormation (.cumul zero .var)
    (.reflIntro (.head one) (.cumul zero .var))
def upperBodyCode : Replay 2 :=
  .pairIntro pairLevel pairFormation .var (.reflIntro (.head one) .var)
def lowerFormation : Replay 1 := .piForm one pairLevel .headType pairFormation
def upperFormation : Replay 1 := .piForm two pairLevel .headType pairFormation
def lowerCode : Replay 1 :=
  .appElim (.head zero) pairType (.lamIntro lowerLevel lowerFormation lowerBodyCode) .var
def upperCode : Replay 1 :=
  .appElim (.head one) pairType (.lamIntro upperLevel upperFormation upperBodyCode) (.cumul zero .var)
def reductCode : Replay 1 :=
  .pairIntro pairLevel pairFormation (.cumul zero .var)
    (.reflIntro (.head one) (.cumul zero .var))

theorem context_checked : checkContext Tower.rules noConversionCheck context contextCode = true := by
  decide

theorem lower_checked : check Tower.rules noConversionCheck context term pairType lowerCode = true := by
  decide

theorem upper_checked : check Tower.rules noConversionCheck context term pairType upperCode = true := by
  decide

theorem codes_differ : lowerCode ≠ upperCode := by
  intro equal
  cases equal

theorem reduct_checked : check Tower.rules noConversionCheck context reduct pairType reductCode = true := by
  decide

theorem reduct_qualified : reductCode.neutralEliminations reduct pairType = true := rfl

noncomputable def meaning (h : CofinalInaccessibles.{u}) (level : Nat) : Meaning.{u} 1 :=
  .plain (fun env => traceApp (traceLam (graph (universeSet h ∅ level)
    (fun x => ZFSet.pair x ∅))) (env 0))

noncomputable def reductMeaning : Meaning.{u} 1 :=
  .plain (fun env => ZFSet.pair (env 0) ∅)

noncomputable def bodyMeaning : Meaning.{u} 2 :=
  .plain (fun env => ZFSet.pair (env 0) ∅)

noncomputable def formationMeaning (h : CofinalInaccessibles.{u}) (level : Nat) : Meaning.{u} 1 :=
  ⟨fun _ => tracePiSet (universeSet h ∅ level)
    (fun _ => sigmaSet (universeSet h ∅ 1) (fun x => truthCode (x = x))),
    some (fun _ => universeSet h ∅ level)⟩

noncomputable def valid (h : CofinalInaccessibles.{u}) (env : Environment.{u} 1) : Prop :=
  True ∧ env 0 ∈ universeSet h ∅ 0

theorem context_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants contextCode context =
      some (valid h) := rfl

theorem lower_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants lowerCode term pairType =
      some (meaning h 0) := rfl

theorem upper_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants upperCode term pairType =
      some (meaning h 1) := rfl

theorem reduct_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants reductCode reduct pairType =
      some reductMeaning := rfl

theorem result_type_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (pairFormation : Replay 1) pairType (.head pairLevel) =
      some (.plain (fun _ => sigmaSet (universeSet h ∅ 1) (fun x => truthCode (x = x)))) := rfl

theorem retained_domains_differ (h : CofinalInaccessibles.{u}) :
    universeSet h ∅ 0 ≠ universeSet h ∅ 1 := by
  intro equal
  have member := universeSet_mem_next h ∅ 0
  rw [← equal] at member
  exact universeSet_no_self_membership h ∅ 0 member

/-- The application-comparison law relates the actual independently
assembled certificates. Its body premise is computed from the pair-valued
body, while domain membership follows from the interpreted source context. -/
theorem assembled_values_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (lower upper : Meaning.{u} 1)
    (atLower : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerCode term pairType = some lower)
    (atUpper : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperCode term pairType = some upper)
    (env : Environment.{u} 1) (admitted : valid h env) : lower.value env = upper.value env := by
  exact application_lambda_related (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    lowerLevel upperLevel (.head zero) (.head one) pairType pairType body body (.var 0) (.var 0)
    lowerFormation upperFormation .var (.cumul zero .var) lowerBodyCode upperBodyCode
    (formationMeaning h 0) (formationMeaning h 1)
    (.plain (fun env => env 0)) (.plain (fun env => env 0)) lower upper bodyMeaning bodyMeaning
    (fun _ => universeSet h ∅ 0) (fun _ => universeSet h ∅ 1)
    rfl rfl rfl rfl rfl rfl rfl rfl atLower atUpper env env Eq Eq
    admitted.2 (universeSet_subset_next h ∅ 0 admitted.2) rfl
    (by intro x _ y _ equal; subst y; rfl)

theorem lower_computes (h : CofinalInaccessibles.{u})
    (env : Environment.{u} 1) (admitted : valid h env) :
    (meaning h 0).value env = ZFSet.pair (env 0) ∅ := traceApp_graph_beta _ admitted.2

theorem upper_computes (h : CofinalInaccessibles.{u})
    (env : Environment.{u} 1) (admitted : valid h env) :
    (meaning h 1).value env = ZFSet.pair (env 0) ∅ :=
  traceApp_graph_beta _ (universeSet_subset_next h ∅ 0 admitted.2)

/-- The result's first component is genuinely its input, and the dependent
second component inhabits the corresponding reflexivity fibre. -/
theorem result_member (h : CofinalInaccessibles.{u})
    (env : Environment.{u} 1) (admitted : valid h env) :
    (meaning h 0).value env ∈ sigmaSet (universeSet h ∅ 1) (fun x => truthCode (x = x)) := by
  rw [lower_computes h env admitted]
  exact ZFSetDependentProducts.mem_sigmaSet.mpr
    ⟨env 0, universeSet_subset_next h ∅ 0 admitted.2, ∅,
      (mem_truthCode _ _).mpr ⟨rfl, rfl⟩, rfl⟩

/-- A nonempty actual set code is an admissible argument, so the comparison
has an inhabited, set-valued input domain. -/
theorem nonempty_input_valid (h : CofinalInaccessibles.{u}) :
    valid h (fun _ => (twoCode h).1) := ⟨True.intro, (twoCode h).2⟩

theorem inputs_distinguished (h : CofinalInaccessibles.{u}) :
    (meaning h 0).value (fun _ => ∅) ≠ (meaning h 0).value (fun _ => (twoCode h).1) := by
  rw [lower_computes h _ ⟨True.intro, seed_mem_zero h ∅⟩,
    lower_computes h _ (nonempty_input_valid h)]
  intro equal
  have codesEqual := (ZFSet.pair_inj.mp equal).1
  have member := ZFSetDependentProducts.Controls.empty_mem_two
  change (∅ : ZFSet.{u}) ∈ (twoCode h).1 at member
  rw [← codesEqual] at member
  exact ZFSet.notMem_empty _ member

/-- Evaluating outside the declared telescope can separate the certificates:
`U₀` is an element of `U₁`, but not an element of itself. -/
theorem invalid_input_values (h : CofinalInaccessibles.{u}) :
    ¬ valid h (fun _ => universeSet h ∅ 0) ∧
      (meaning h 0).value (fun _ => universeSet h ∅ 0) = ∅ ∧
      (meaning h 1).value (fun _ => universeSet h ∅ 0) = ZFSet.pair (universeSet h ∅ 0) ∅ := by
  refine ⟨fun admitted => universeSet_no_self_membership h ∅ 0 admitted.2, ?_,
    traceApp_graph_beta _ (universeSet_mem_next h ∅ 0)⟩
  apply ZFSet.ext
  intro z
  change z ∈ traceApp (traceLam (graph (universeSet h ∅ 0) _)) (universeSet h ∅ 0) ↔ _
  rw [ZFSetTraceProducts.mem_traceApp, ZFSetTraceProducts.pair_mem_traceLam]
  constructor
  · rintro ⟨value, member, _⟩
    exact (universeSet_no_self_membership h ∅ 0
      (ZFSetDependentProducts.pair_mem_graph.mp member).1).elim
  · exact fun impossible => (ZFSet.notMem_empty z impossible).elim

theorem invalid_input_distinguishes (h : CofinalInaccessibles.{u}) :
    (meaning h 0).value (fun _ => universeSet h ∅ 0) ≠
      (meaning h 1).value (fun _ => universeSet h ∅ 0) := by
  obtain ⟨_, lower, upper⟩ := invalid_input_values h
  rw [lower, upper]
  intro equal
  have member : ({universeSet h ∅ 0} : ZFSet.{u}) ∈ ZFSet.pair (universeSet h ∅ 0) ∅ := by
    simp [ZFSet.pair]
  rw [← equal] at member
  exact ZFSet.notMem_empty _ member

#print axioms lower_checked
#print axioms upper_checked
#print axioms codes_differ
#print axioms retained_domains_differ
#print axioms assembled_values_agree
#print axioms result_member
#print axioms inputs_distinguished
#print axioms invalid_input_values
#print axioms invalid_input_distinguishes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayApplicationComparisonControls
