import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.AnnotatedPredicatePolymorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.CodedHOL
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Examples

/-!
# Polymorphic programs in the coded reading

Both instances have one object carrier and the original program is read
without first specializing it. Actual set traces compute the two identities.
The chosen finite set of type codes witnesses these computations only; it is
not asserted to be a universe model of the source rule package. A false
universe interpretation refutes the generated source-head typing formula.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.AnnotatedCodedPolymorphism
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated TowerInterpretation
open HOL.Embedding ZFSetDependentProducts ZFSetTraceProducts
namespace Source
export AnnotatedPredicatePolymorphism (rules church polymorphicIdentity)
end Source
open CodedHOL
universe u

def ground : ZFSet.{u} := {∅,{∅}}
noncomputable def arrows : ZFSet.{u} := tracePiSet ground (fun _ => ground)
noncomputable def typeCodes : ZFSet.{u} := {ground,arrows}
noncomputable def heads (h : Nat) : ZFSet.{u} := if h = 0 then ground else if h = 1 then typeCodes else ∅
def constants (_ : DeclName) : ZFSet.{u} := ∅

def code (source : CTm Nat 0) : ClosedTerm (Symbol Nat) object :=
  AnnotatedCodedReading.readAt operations Fin.elim0 source

noncomputable def value (source : CTm Nat 0) : ZFSet.{u} :=
  (model heads constants).denote (code source) (fun i => nomatch i)

theorem value_exact (source : CTm Nat 0) : value.{u} source = ev heads constants source Fin.elim0 := by
  have exactCode := denote_readAt heads constants source
    (Fin.elim0 : Fin 0 → ClosedTerm (Symbol Nat) object) (fun i => nomatch i)
  apply exactCode.trans
  apply congrArg (ev heads constants source)
  funext i
  exact Fin.elim0 i

def baseApplication : CTm Nat 0 := .app Source.polymorphicIdentity (.head 0)
def functionApplication : CTm Nat 0 := .app Source.polymorphicIdentity (.pi (.head 0) (.head 0))

theorem base_identity_value : value.{u} baseApplication = traceLam (graph ground (fun x => x)) := by
  rw [value_exact]
  change traceApp (traceLam (graph typeCodes (fun A => traceLam (graph A (fun x => x))))) ground = _
  exact traceApp_graph_beta _ (by simp [typeCodes])

theorem function_identity_value : value.{u} functionApplication = traceLam (graph arrows (fun x => x)) := by
  rw [value_exact]
  change traceApp (traceLam (graph typeCodes (fun A => traceLam (graph A (fun x => x))))) arrows = _
  exact traceApp_graph_beta _ (by simp [typeCodes])

theorem base_returns {x : ZFSet.{u}} (member : x ∈ ground) :
    traceApp (value baseApplication) x = x := by
  rw [base_identity_value]
  exact traceApp_graph_beta _ member

theorem function_returns {f : ZFSet.{u}} (member : f ∈ arrows) :
    traceApp (value functionApplication) f = f := by
  rw [function_identity_value]
  exact traceApp_graph_beta _ member

theorem two_distinct_answers :
    traceApp (value.{u} baseApplication) ∅ ≠ traceApp (value.{u} baseApplication) {∅} := by
  rw [base_returns (by simp [ground]),base_returns (by simp [ground])]
  intro same
  have member : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := by simp
  rw [← same] at member
  simp at member

def badHeads (h : Nat) : ZFSet.{u} := if h = 0 then ground else ∅
def headStatement : CStatement Nat := .typing .nil (.head 0) (.head 1)
theorem headStatement_derivable : CDerivable Source.church headStatement := .headType rfl

theorem bad_universe_refused :
    ¬ ((model badHeads.{u} constants).denote
      (judgmentAt headStatement (Fin.elim0 : Fin 0 → ClosedTerm (Symbol Nat) object))
      (fun i => nomatch i)).down := by
  change ¬ (True → ground ∈ (∅ : ZFSet.{u}))
  simp

theorem bad_model_not_available : ¬ SetModel badHeads.{u} constants Source.church := by
  intro interpretation
  have impossible := interpretation.universes.headTyping_mem (show Source.rules.headTyping 0 1 from rfl)
  change ground ∈ (∅ : ZFSet.{u}) at impossible
  simp at impossible

/-- The existing nontrivial universe tower discharges the abstract model
contracts; this control does not use the finite type-code set above. -/
theorem actual_tower_polymorphic_holds (h : ZFSetUniverseClosure.CofinalInaccessibles.{u}) :
    ((CodedHOL.model
      (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation.interpretHead h ∅ ∅ (fun _ => (0 : Nat)))
      (fun _ => ∅)).denote
      (judgmentAt (.typing .nil TowerInterpretation.Examples.polyId TowerInterpretation.Examples.polyIdType)
        (Fin.elim0 : Fin 0 → ClosedTerm (Symbol Tower.Head) object))
      (fun i => nomatch i)).down :=
  CodedTower.generated_judgment_holds (Γ := []) h ∅ ∅ (fun _ => (0 : Nat))
    (empty_mem_universeSet h ∅ 0) (fun _ => ∅) TowerInterpretation.Examples.polyId_typed
    Fin.elim0 (fun i => nomatch i)

#print axioms value_exact
#print axioms function_returns
#print axioms two_distinct_answers
#print axioms bad_universe_refused
#print axioms bad_model_not_available
#print axioms actual_tower_polymorphic_holds
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.AnnotatedCodedPolymorphism
