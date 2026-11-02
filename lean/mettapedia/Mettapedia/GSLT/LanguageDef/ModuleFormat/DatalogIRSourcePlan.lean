import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClauseFiring
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPlanReading
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralRootReceipt

/-! Every authorized source clause is present in the prepared program and
selected by a complete shared plan. Its elaborated metadata supplies the
actual firing; declaration indices are not inferred from rule names. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SourcePlan

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding GeneralExecutionAdmission
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem source_compilation (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (ordinal : Nat) (clause : Clause) (source : ProgramGrounding.ClauseAt program ordinal clause) :
    ∃ (index : Nat) (rule : RewriteRule), prepared.compiled.rewrites[index]? = some rule ∧
      Query.compileClause? prepared.vocabulary ordinal clause = some rule := by
  obtain ⟨core,encoded,formed,_,rfl⟩ := PlanReading.prepared_payload program seeds prepared accepted
  have rows := (Join.Program.prepare?_sound program seeds core formed).2.2.2
  obtain ⟨index,atSource⟩ := List.mem_iff_getElem?.mp ((ProgramGrounding.clauseAt_iff_numbered program ordinal clause).mp source)
  have sourceBound := (List.getElem?_eq_some_iff.mp atSource).1
  have ruleBound : index < core.rules.length := by rw [← rows.length_eq]; exact sourceBound
  let raw := core.rules[index]
  have rawCompiled : Join.compileClause? core.vocabulary ordinal clause = some raw := by
    have actual := rows.get sourceBound ruleBound
    simpa only [List.get_eq_getElem,(List.getElem?_eq_some_iff.mp atSource).2] using actual
  refine ⟨index,Query.lowerRule core.vocabulary raw,?_,?_⟩
  · change (core.rules.map (Query.lowerRule core.vocabulary))[index]? = _
    simp [raw,ruleBound]
  · exact congrArg (Option.map (Query.lowerRule core.vocabulary)) rawCompiled

private theorem free_context (entries : List (String × TypeExpr)) :
    (fun name => (entries.find? fun entry => entry.1 == name).map Prod.snd) = FreeTypeContext.ofList entries := by
  funext name
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨key,type⟩
    by_cases same : key = name
    · subst key
      simp [FreeTypeContext.ofList]
    · simp [FreeTypeContext.ofList,same,ih]

theorem plan_grammar (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (codes : List Pattern) :
    (GeneralPlanEnvironment.environment (Executable.plan prepared codes)).language.terms = Query.baseLanguage.terms := by
  obtain ⟨core,values,_,_,same⟩ := PlanReading.prepared_payload program seeds prepared accepted
  subst prepared
  rfl

theorem plan_free (prepared : Executable.Prepared) (codes : List Pattern) :
    (GeneralPlanEnvironment.environment (Executable.plan prepared codes)).free =
      FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary) := free_context _

theorem authorized_firing (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (complete : (Executable.plan prepared codes).complete = true)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (wanted : GroundInstances.Instance) (authorized : ProgramGrounding.SourceAuthorized Executable.policy program facts wanted) :
    ∃ target index trace captured completed history,
      Executable.fact? prepared.vocabulary wanted.conclusion = some target ∧
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (Executable.plan prepared codes)) [] (.base "DlStatement")
        (Executable.request prepared.vocabulary) index trace captured completed history target := by
  obtain ⟨clause,source,authorized⟩ := authorized
  obtain ⟨sourceIndex,authored,atSource,compiled⟩ := source_compilation program seeds prepared accepted wanted.key.statementIndex clause source
  have selected : selected Executable.permissions.ruleIndices sourceIndex = true := rfl
  obtain ⟨entry,member,entryCompiled⟩ := complete_rule_coverage complete (List.mk_mem_zipIdx_iff_getElem?.mpr atSource) selected
  have entryFields := rulePlan_readout entryCompiled
  obtain ⟨index,atEntry⟩ := List.mem_iff_getElem?.mp member
  have declared := GeneralPlanEnvironment.selected_rule (Executable.plan prepared codes) atEntry
  have specified := GeneralPlanEnvironment.selected_specification (Executable.plan prepared codes) atEntry
  have originalDeclared : (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)).language.rewrites[index]? = some entry.rule := by
    rw [Executable.snapshot_environment_transport prepared prepared.seedFacts codes] at declared
    exact declared
  have originalSpecified : GeneralPremise.specification? (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) index =
      some entry.binding.spec := by
    rw [Executable.snapshot_environment_transport prepared prepared.seedFacts codes] at specified
    exact specified
  obtain ⟨actualSpec,actualSpecified,_,checked⟩ := GeneralPremise.Static.checkLanguage_rule scope originalDeclared
  have sameSpec : actualSpec = entry.binding.spec := Option.some.inj (actualSpecified.symm.trans originalSpecified)
  subst actualSpec
  have zero : GeneralPremise.checkZeroDependencies entry.binding.spec = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).1).1
  have fields : entry.rule.left = authored.left ∧ entry.rule.right = authored.right ∧ entry.rule.premises = authored.premises := by
    change entry.authored.left = _ ∧ entry.authored.right = _ ∧ entry.authored.premises = _
    rw [entryFields.2.1]
    exact ⟨rfl,rfl,rfl⟩
  have ctx : entry.rule.typeContext = BindingContext.context prepared.vocabulary clause ++ entry.binding.implicitTypes := by
    change entry.authored.typeContext ++ entry.binding.implicitTypes = _
    rw [entryFields.2.1,BindingContext.compiled_context prepared.vocabulary wanted.key.statementIndex clause authored compiled]
  have grammar : (GeneralPlanEnvironment.environment (Executable.plan prepared codes)).language.terms = Query.baseLanguage.terms := by
    exact plan_grammar program seeds prepared accepted codes
  have free : (GeneralPlanEnvironment.environment (Executable.plan prepared codes)).free =
      FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary) := plan_free prepared codes
  obtain ⟨target,trace,captured,completed,history,encodedConclusion,firing⟩ := ClauseFiring.authorized_firing program seeds prepared accepted
    wanted.key.statementIndex clause source authored compiled facts codes encoded wanted authorized
    (GeneralPlanEnvironment.environment (Executable.plan prepared codes)) rfl grammar free index entry.rule entry.binding.spec fields
    entry.binding.implicitTypes ctx declared specified entryFields.2.2.2.1 zero
  exact ⟨target,index,trace,captured,completed,history,encodedConclusion,firing⟩

theorem authorized_receipt (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (complete : (Executable.plan prepared codes).complete = true)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (wanted : GroundInstances.Instance) (authorized : ProgramGrounding.SourceAuthorized Executable.policy program facts wanted) :
    ∃ receipt : GeneralOccurrenceSemantics.Receipt,
      receipt.Valid (Executable.plan prepared codes) [] (.base "DlStatement") (Executable.request prepared.vocabulary) ∧
      Executable.fact? prepared.vocabulary wanted.conclusion = some receipt.target := by
  obtain ⟨target,index,trace,captured,completed,history,formed,firing⟩ := authorized_firing program seeds prepared accepted
    facts codes encoded complete scope wanted authorized
  obtain ⟨receipt,valid,same,_⟩ := GeneralRuleJobs.root_receipt (Executable.plan prepared codes) rfl [] (.base "DlStatement")
    (Executable.request prepared.vocabulary) target index trace captured completed history firing
  refine ⟨⟨Executable.request prepared.vocabulary,[],receipt⟩,⟨.nil _,valid⟩,?_⟩
  change Executable.fact? prepared.vocabulary wanted.conclusion = some receipt.target
  rw [same]
  exact formed

#print axioms source_compilation
#print axioms authorized_firing
#print axioms authorized_receipt

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SourcePlan
