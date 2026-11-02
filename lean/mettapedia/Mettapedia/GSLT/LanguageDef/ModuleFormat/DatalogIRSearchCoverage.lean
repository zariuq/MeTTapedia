import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSourcePlan
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureCommitLaws
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureMachine

/-! A completed shared snapshot search publishes every authorized source
inference. If committing that complete publication adds no facts, the source
fact set is closed under all of its clauses. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SearchCoverage

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

private theorem equivalent_eq (plan : GeneralExecutionAdmission.Plan) (empty : plan.equations = [])
    (left right : Pattern)
    (equivalent : Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan [] (.base "DlStatement")) left right) : left = right := by
  induction equivalent with
  | rel first second step =>
    obtain ⟨receipt,completed,_⟩ := step
    have member := List.fst_mem_of_mem_zipIdx completed.job.1
    rw [empty] at member
    cases member
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem authorized_published (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (complete : (Executable.plan prepared codes).complete = true)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (work : Nat)
    (finished : (ClosureMachine.search prepared codes).status
      ((ClosureMachine.search prepared codes).run (Executable.request prepared.vocabulary) work) = .complete)
    (wanted : GroundInstances.Instance) (authorized : ProgramGrounding.SourceAuthorized Executable.policy program facts wanted) :
    ∃ receipt ∈ (ClosureMachine.search prepared codes).publication
        ((ClosureMachine.search prepared codes).run (Executable.request prepared.vocabulary) work),
      Executable.fact? prepared.vocabulary wanted.conclusion = some receipt.target := by
  obtain ⟨original,valid,formed⟩ := SourcePlan.authorized_receipt program seeds prepared accepted facts codes encoded complete scope wanted authorized
  have checked := Complete.Predecessors.equationsChecked_of_complete complete
  have done : Complete.Classes.complete (Executable.plan prepared codes)
      (Complete.Classes.runAt (Executable.plan prepared codes) [] (.base "DlStatement") (Executable.request prepared.vocabulary) work) = true := by
    simpa only [ClosureMachine.search,Complete.Normalized.search,Complete.Classes.search,Complete.Classes.status,
      ite_eq_left_iff,reduceCtorEq,imp_false,not_not] using finished
  obtain ⟨receipt,present,equivalent⟩ := Complete.Classes.exact_of_complete (Executable.plan prepared codes) [] (.base "DlStatement")
    (Executable.request prepared.vocabulary) work checked done (GeneralOccurrenceSemantics.Receipt.semantic_step _ _ _ valid)
  have same := equivalent_eq (Executable.plan prepared codes) (PlanReading.equations_empty program seeds prepared accepted codes) _ _ equivalent
  exact ⟨receipt,present,by rw [same]; exact formed⟩

private theorem encoded_source (prepared : Executable.Prepared) (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (code : Pattern) (member : code ∈ codes) :
    ∃ fact ∈ facts, Executable.fact? prepared.vocabulary fact = some code := by
  induction encoded with
  | nil => cases member
  | @cons fact first facts codes formed rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨fact,List.mem_cons_self,formed⟩
    · obtain ⟨other,present,encoded⟩ := ih later
      exact ⟨other,List.mem_cons_of_mem _ present,encoded⟩

theorem stable_commit_closed (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (complete : (Executable.plan prepared codes).complete = true)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (work : Nat)
    (finished : (ClosureMachine.search prepared codes).status
      ((ClosureMachine.search prepared codes).run (Executable.request prepared.vocabulary) work) = .complete)
    (before after : List ClosureMachine.Key)
    (committed : ClosureMachine.commit? prepared codes
      ((ClosureMachine.search prepared codes).publication ((ClosureMachine.search prepared codes).run (Executable.request prepared.vocabulary) work))
      codes before = some (codes,after)) :
    ∀ wanted : GroundInstances.Instance, ProgramGrounding.SourceAuthorized Executable.policy program facts wanted →
      wanted.conclusion ∈ facts := by
  intro wanted authorized
  obtain ⟨receipt,present,formed⟩ := authorized_published program seeds prepared accepted facts codes encoded complete scope work finished wanted authorized
  have membership := (ClosureMachine.Conservation.commit_observations prepared codes _ codes before codes after committed).1
  have included := (membership receipt.target).mpr (Or.inr (List.mem_map.mpr ⟨receipt,present,rfl⟩))
  obtain ⟨fact,inFacts,encodedFact⟩ := encoded_source prepared facts codes encoded receipt.target included
  have first := Executable.decodeFact?_roundtrip prepared wanted.conclusion receipt.target formed
  have second := Executable.decodeFact?_roundtrip prepared fact receipt.target encodedFact
  have same : wanted.conclusion = fact := Option.some.inj (first.symm.trans second)
  exact same ▸ inFacts

#print axioms authorized_published
#print axioms stable_commit_closed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SearchCoverage
