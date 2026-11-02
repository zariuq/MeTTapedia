import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSourcePlan
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureKeyLaws

/-! Every valid prepared receipt has a total logical-key readback. Positive
premise events address actual snapshot facts, and the completed assignment
contains all clause variables with empty dependency and ambient contexts. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ReceiptKeys

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem positive_history (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern)
    (environment : GeneralPremise.Environment) (provider : environment.provider = (Executable.snapshot prepared known).provider)
    (entries : List (Mettapedia.Languages.Datalog.Atom × Nat)) (positive tail : List Syntax.Premise)
    (compiled : List.Forall₂ (fun entry premise => ∃ code, Join.atom? prepared.vocabulary entry.2 entry.1 = some code ∧
      premise = .relationQuery Query.factRelation [code]) entries positive)
    (context : GeneralPremise.Context) (bound : context.bound = []) (depth : context.quantifierDepth = 0)
    (initial final : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (held : GeneralPremise.PremisesHold environment context (positive ++ tail) initial final history)
    (roots : GeneralPremise.RootValues 0 final) :
    CompilationFlow.VariablesBound (entries.flatMap fun entry => entry.1.variables) final ∧
      ∃ facts, ClosureMachine.premiseFacts? entries.length history known = some facts := by
  cases entries with
  | nil =>
    cases compiled
    refine ⟨?_,[],rfl⟩
    intro name member
    cases member
  | cons entry entries =>
    cases compiled with
    | @cons _ premise _ positive first rest =>
      obtain ⟨code,codeCompiled,rfl⟩ := first
      cases held with
      | @cons _ _ _ _ middle _ event events firstHeld restHeld =>
        cases firstHeld with
        | @query _ _ _ _ _ rowIndex origins query =>
          have signature := SnapshotReading.fact_signature prepared known
          rw [← provider] at signature
          have static : environment.provider.dynamicRelations = [] := by rw [provider]; rfl
          obtain ⟨value,atRow,_⟩ := QueryReading.output_row_readout prepared.vocabulary entry.2 entry.1 code codeCompiled
            (.base "DlStatement") static signature query restHeld.extension (by simpa only [bound,List.length_nil] using roots)
          rw [provider] at atRow
          have atFact := SnapshotReading.fact_row_position program seeds prepared accepted known rowIndex value atRow
          have produced := query.readout.produces _ signature
          have headBound : GeneralPremise.BoundNames middle code.freeFvarNames := by
            simpa [GeneralPremise.queryOutputNames] using produced
          have headVars := (CompilationFlow.output_variables prepared.vocabulary entry.2 entry.1 code codeCompiled middle headBound).extension restHeld.extension
          obtain ⟨tailVars,facts,tailRead⟩ := positive_history program seeds prepared accepted known environment provider entries positive tail rest
            context.next bound rfl middle final events restHeld roots
          constructor
          · simpa only [CompilationFlow.VariablesBound,List.flatMap_cons,List.map_append] using headVars.append tailVars
          · exact ⟨value :: facts,by simp [ClosureMachine.premiseFacts?,depth,atFact,tailRead]⟩
termination_by entries.length

private theorem grounding_total (names : List String) (assignment : ScopedRuleMatching.Assignment)
    (roots : GeneralPremise.RootValues 0 assignment)
    (bound : ∀ name ∈ names, ∃ value, ScopedRuleMatching.lookup assignment (Join.logicalVariable name) = some value) :
    ∃ values, ClosureMachine.grounding? names assignment = some values := by
  induction names with
  | nil => exact ⟨[],rfl⟩
  | cons name names ih =>
    obtain ⟨value,found⟩ := bound name List.mem_cons_self
    have root := roots _ value found
    obtain ⟨rest,later⟩ := ih (fun other member => bound other (List.mem_cons_of_mem _ member))
    refine ⟨(name,value.body) :: rest,?_⟩
    simp only [ClosureMachine.grounding?,List.mapM_cons] at later ⊢
    simp only [found,Option.bind_eq_bind,Option.bind_some,root.1,root.2.1,List.isEmpty_nil,beq_self_eq_true,Bool.and_self,if_true]
    simp only [Option.bind_eq_bind] at later
    rw [later]
    rfl

private theorem declaration_numbered (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern)
    (source : Pattern) (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid (Executable.plan prepared known) [] (.base "DlStatement") source) :
    ∃ ordinal clause, (LPBridge.numberedClauses program)[receipt.job.declaration.declarationIndex]? = some (ordinal,clause) ∧
      Query.compileClause? prepared.vocabulary ordinal clause = some receipt.job.declaration.authored := by
  obtain ⟨rule,index,member,_,planned⟩ := GeneralExecutionAdmission.compiled_rule_origin (List.fst_mem_of_mem_zipIdx valid.1.1)
  have fields := GeneralExecutionAdmission.rulePlan_readout planned
  have atRule := List.mk_mem_zipIdx_iff_getElem?.mp member
  have inside : index < prepared.compiled.rewrites.length := (List.getElem?_eq_some_iff.mp atRule).1
  obtain ⟨ordinal,clause,_,compiled,atNumbered⟩ := Executable.compiled_origin_at program seeds prepared accepted index inside
  have actual : prepared.compiled.rewrites[index] = rule := (List.getElem?_eq_some_iff.mp atRule).2
  rw [actual] at compiled
  exact ⟨ordinal,clause,fields.1 ▸ atNumbered,fields.2.1 ▸ compiled⟩

theorem total (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (receipt : GeneralOccurrenceSemantics.Receipt)
    (valid : receipt.Valid (Executable.plan prepared known) [] (.base "DlStatement") (Executable.request prepared.vocabulary)) :
    ∃ key, ClosureMachine.key? prepared known receipt = some key := by
  have sameSource := (PlanReading.conversion_trivial program seeds prepared accepted known valid.1).1
  have firingValid : receipt.firing.Valid (Executable.plan prepared known) [] (.base "DlStatement") (Executable.request prepared.vocabulary) := by
    rw [sameSource]
    exact valid.2
  obtain ⟨ordinal,clause,atNumbered,compiled⟩ := declaration_numbered program seeds prepared accepted known _ receipt.firing firingValid
  obtain ⟨_,positive,guards,positiveCompiled,_,body⟩ := ClausePremises.compiled_split prepared.vocabulary ordinal clause receipt.firing.job.declaration.authored compiled
  have actualBody : receipt.firing.job.declaration.rule.premises = positive ++ guards := body
  have site := PlanReading.root_site prepared known _ receipt.firing.job.site firingValid.1.2
  have declared := GeneralRuleJobs.Job.selected_rule firingValid.1
  have specified := GeneralRuleJobs.Job.selected_specification firingValid.1
  have originalDeclared : (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)).language.rewrites[receipt.firing.job.ordinal]? =
      some receipt.firing.job.declaration.rule := by
    rw [Executable.snapshot_environment_transport prepared prepared.seedFacts known] at declared
    exact declared
  have originalSpecified : GeneralPremise.specification? (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) receipt.firing.job.ordinal =
      some receipt.firing.job.declaration.binding.spec := by
    rw [Executable.snapshot_environment_transport prepared prepared.seedFacts known] at specified
    exact specified
  obtain ⟨actualSpec,actualSpecified,_,checked⟩ := GeneralPremise.Static.checkLanguage_rule scope originalDeclared
  have sameSpec : actualSpec = receipt.firing.job.declaration.binding.spec := Option.some.inj (actualSpecified.symm.trans originalSpecified)
  subst actualSpec
  have zero : GeneralPremise.checkZeroDependencies receipt.firing.job.declaration.binding.spec = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).1).1
  have firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (Executable.plan prepared known)) [] (.base "DlStatement")
      (Executable.request prepared.vocabulary) receipt.firing.job.ordinal receipt.firing.matcherTrace receipt.firing.captured receipt.firing.completed
      receipt.firing.premiseHistory receipt.firing.localTarget := by
    simpa only [site,GeneralTypedSites.SiteData.here,GeneralPlanEnvironment.environmentWith_empty] using firingValid.2.1
  have evidence : CompilationFlow.VariablesBound clause.providedVariables receipt.firing.completed ∧
      ∃ facts, ClosureMachine.premiseFacts? clause.positiveAtoms.length receipt.firing.premiseHistory known = some facts := by
    cases firing with
    | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ actualDeclared actualSpecified _ _ _ capturedTyped premises _ _ =>
      have sameRule : actualRule = receipt.firing.job.declaration.rule := Option.some.inj (actualDeclared.symm.trans declared)
      subst actualRule
      have sameSpec : actualSpec = receipt.firing.job.declaration.binding.spec := Option.some.inj (actualSpecified.symm.trans specified)
      subst actualSpec
      rw [actualBody] at premises
      have roots := (premises.typed capturedTyped).rootValues zero
      have info := positive_history program seeds prepared accepted known _ rfl clause.positiveAtoms.zipIdx positive guards positiveCompiled
        _ rfl rfl _ _ _ premises roots
      have names : (clause.positiveAtoms.zipIdx.flatMap fun entry => entry.1.variables) = clause.providedVariables := by
        have mapped := congrArg (fun atoms : List Mettapedia.Languages.Datalog.Atom => atoms.flatMap (·.variables)) (List.zipIdx_map_fst 0 clause.positiveAtoms)
        simpa only [List.flatMap_map,Function.comp_def,Clause.providedVariables] using mapped
      simpa only [names,List.length_zipIdx] using info
  obtain ⟨_,actualSpec,_,actualSpecified,typed⟩ := GeneralPremise.Interpreted.RootFiring.completed_typed firing
  have sameSpec : actualSpec = receipt.firing.job.declaration.binding.spec := Option.some.inj (actualSpecified.symm.trans specified)
  subst actualSpec
  have roots := typed.rootValues zero
  obtain ⟨grounding,groundingRead⟩ := grounding_total (DerivationIdentity.clauseVariables clause) receipt.firing.completed roots (by
    intro name member
    exact evidence.1 _ (List.mem_map.mpr ⟨name,List.mem_eraseDups.mp member,rfl⟩))
  obtain ⟨facts,factsRead⟩ := evidence.2
  refine ⟨⟨ordinal,grounding,facts⟩,?_⟩
  simp only [ClosureMachine.key?,(Executable.prepare_typed program seeds prepared accepted).1,atNumbered,
    Option.bind_eq_bind,Option.bind_some,groundingRead,factsRead]
  rfl

#print axioms total

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ReceiptKeys
