import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureNoFault
import Mettapedia.OSLF.MeTTaIL.Complete.Termination

/-! Prepared Datalog rules have only finite provider queries as premises.
Their actual shared environments therefore satisfy structural descent,
and every immutable snapshot search finishes after finite work. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SnapshotTermination

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralExecutionAdmission

private theorem forall_right {α β : Type} {relation : α → β → Prop} {property : β → Prop}
    {left : List α} {right : List β} (related : List.Forall₂ relation left right)
    (every : ∀ first second, relation first second → property second) : ∀ second ∈ right, property second := by
  induction related with
  | nil => intro _ member; cases member
  | @cons first second left right head rest ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact every first value head
    · exact ih value later

theorem rule_queries (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (codes : List Pattern)
    (index : Nat) (rule : RewriteRule)
    (declared : (GeneralPlanEnvironment.environment (Executable.plan prepared codes)).language.rewrites[index]? = some rule) :
    ∀ premise ∈ rule.premises, ∃ relation arguments, premise = .relationQuery relation arguments := by
  have mapped : ((Executable.plan prepared codes).rules[index]?).map RulePlan.rule = some rule := by
    simpa only [GeneralPlanEnvironment.environment,List.getElem?_map] using declared
  obtain ⟨entry,atEntry,same⟩ := Option.map_eq_some_iff.mp mapped
  subst rule
  obtain ⟨raw,rawIndex,member,_,planned⟩ := compiled_rule_origin (List.mem_of_getElem? atEntry)
  have fields := rulePlan_readout planned
  have atRaw := List.mk_mem_zipIdx_iff_getElem?.mp member
  have inside : rawIndex < prepared.compiled.rewrites.length := (List.getElem?_eq_some_iff.mp atRaw).1
  obtain ⟨ordinal,clause,_,compiled,_⟩ := Executable.compiled_origin_at program seeds prepared accepted rawIndex inside
  have actual : prepared.compiled.rewrites[rawIndex] = raw := (List.getElem?_eq_some_iff.mp atRaw).2
  rw [actual] at compiled
  obtain ⟨_,positive,guards,positiveCompiled,guardsCompiled,body⟩ := ClausePremises.compiled_split prepared.vocabulary ordinal clause raw compiled
  change ∀ premise ∈ entry.authored.premises, _
  rw [fields.2.1,body]
  intro premise member
  rcases List.mem_append.mp member with positive | guard
  · exact forall_right (property := fun premise => ∃ relation arguments, premise = Syntax.Premise.relationQuery relation arguments)
      positiveCompiled (by rintro _ _ ⟨code,_,rfl⟩; exact ⟨_,_,rfl⟩) premise positive
  · exact forall_right (property := fun premise => ∃ relation arguments, premise = Syntax.Premise.relationQuery relation arguments)
      guardsCompiled (by rintro _ _ ⟨left,right,_,_,rfl⟩; exact ⟨_,_,rfl⟩) premise guard

private theorem queries_descend (rule : RewriteRule) (spec : RuleBindingSpec) (index : Nat) (premises : List Syntax.Premise)
    (queries : ∀ premise ∈ premises, ∃ relation arguments, premise = .relationQuery relation arguments) :
    StructuralDescent.checkPremises rule spec index premises = true := by
  induction premises generalizing index with
  | nil => rfl
  | cons premise premises ih =>
    obtain ⟨relation,arguments,rfl⟩ := queries premise List.mem_cons_self
    simpa only [StructuralDescent.checkPremises,StructuralDescent.checkPremise,Bool.true_and] using
      ih (index + 1) (fun other member => queries other (List.mem_cons_of_mem _ member))

theorem environment_descends (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (codes : List Pattern)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true) :
    StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment (Executable.plan prepared codes)) = true := by
  apply List.all_eq_true.mpr
  intro entry member
  rcases entry with ⟨rule,index⟩
  have declared := List.mk_mem_zipIdx_iff_getElem?.mp member
  have original : (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)).language.rewrites[index]? = some rule := by
    rw [Executable.snapshot_environment_transport prepared prepared.seedFacts codes] at declared
    exact declared
  obtain ⟨spec,specified,admitted,_⟩ := GeneralPremise.Static.checkLanguage_rule scope original
  have current : GeneralPremise.specification? (GeneralPlanEnvironment.environment (Executable.plan prepared codes)) index = some spec := by
    rw [Executable.snapshot_environment_transport prepared prepared.seedFacts codes]
    exact specified
  have checked := queries_descend rule spec 0 rule.premises (rule_queries program seeds prepared accepted codes index rule declared)
  simp only [current,StructuralDescent.checkRule,admitted,checked,Bool.true_and]

theorem search_finishes (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (codes : List Pattern)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true) :
    ∃ work, (ClosureMachine.search prepared codes).status
      ((ClosureMachine.search prepared codes).run (Executable.request prepared.vocabulary) work) = .complete := by
  obtain ⟨work,done⟩ := Complete.Classes.equationFree_eventually_complete (Executable.plan prepared codes) [] (.base "DlStatement")
    (Executable.request prepared.vocabulary) (PlanReading.equations_empty program seeds prepared accepted codes)
    (environment_descends program seeds prepared accepted codes scope)
  exact ⟨work,by simp only [ClosureMachine.search,Complete.Normalized.search,Complete.Classes.search,Complete.Classes.status,done,if_true]⟩

#print axioms rule_queries
#print axioms environment_descends
#print axioms search_finishes

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SnapshotTermination
