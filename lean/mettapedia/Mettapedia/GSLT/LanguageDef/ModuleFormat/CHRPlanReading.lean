import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgramOrigins
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRMatchedEncoding
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammarFirstOrder
import Mettapedia.OSLF.MeTTaIL.GeneralVectorBindingAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesGenerator

/-! Actual selected plan declarations retain the source head selection and
its compact result. Binding inference may keep explicit occurrence metadata;
the nullary-capture law applies to either inference route. Root permissions
preserve the actual request, and no premise changes its captured assignment. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.PlanReading

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding ScopedRuleMatching GeneralScopedMatch
open GeneralExecutionAdmission GeneralTypedSites GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

private theorem compiled_flags (vocabulary : Vocabulary) (query active : Nat) (source : Rule)
    (rule : RewriteRule) (compiled : compileRule? vocabulary query active source = some rule) :
    rule.bindings = none ∧ rule.premises = [] := by
  unfold compileRule? at compiled
  split at compiled
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨_, _, same⟩ := compiled
    cases Option.some.inj same
    exact ⟨rfl, rfl⟩
  · cases compiled

private theorem metavariable_vector_free (indices : List Nat) (slot : Nat → String) :
    binderFree (vector (indices.map (fun index => Pattern.fvar (slot index)))) = true := by
  apply GeneralRuleBindingInference.vector_binderFree
  apply VectorFirstOrder.vector
  intro pattern member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact .metavariable _

theorem compiled_left_binderFree (vocabulary : Vocabulary) (query active : Nat) (source : Rule)
    (rule : RewriteRule) (compiled : compileRule? vocabulary query active source = some rule) :
    binderFree rule.left = true := by
  obtain ⟨schemas, left, shapes⟩ := HeadShape.compiled_rule_heads vocabulary query active source rule compiled
  have selected : binderFreeList schemas = true :=
    GeneralRuleBindingInference.vector_binderFree (.vector schemas shapes)
  have predicates := metavariable_vector_free (List.range vocabulary.predicates.length) predicateSlot
  have scalars := metavariable_vector_free (List.range vocabulary.scalars.length) scalarSlot
  rw [left]
  simp only [poolPatterns, List.cons_append, List.nil_append, binderFree, binderFreeList,
    predicates, scalars, selected, Bool.true_and]

theorem selected_zero (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) (selectedPlan : RulePlan)
    (member : selectedPlan ∈ (plan prepared).rules) :
    GeneralPremise.checkZeroDependencies selectedPlan.binding.spec = true := by
  obtain ⟨entry, source, _, _, _, compiled, _, _⟩ :=
    ProgramOrigins.plan_rule_origin program seeds prepared accepted selectedPlan member
  obtain ⟨raw, index, _, _, planned⟩ := compiled_rule_origin member
  have fields := rulePlan_readout planned
  have inferred := fields.2.2.1
  rw [← fields.2.1] at inferred
  have flags := compiled_flags prepared.vocabulary selectedPlan.declarationIndex entry.occurrence.head source
    selectedPlan.authored compiled
  exact GeneralRuleBindingInference.compile_binderFree_zero prepared.compiled selectedPlan.authored selectedPlan.binding
    flags.1 (compiled_left_binderFree _ _ _ _ _ compiled)
    (MatchedEncoding.compiled_right_binderFree _ _ _ _ _ compiled) flags.2 inferred

theorem root_site (prepared : Prepared) (source : Pattern) (site : SiteData)
    (licensed : Licensed (GeneralPlanEnvironment.environment (plan prepared)).language
      (plan prepared).snapshot.free (plan prepared).permissions.sites
      [] (.base "ChrMatchState") source site) : site = SiteData.here [] (.base "ChrMatchState") source := by
  have generated := generate_complete licensed
  change site ∈ generate _ _ .rootOnly [] (.base "ChrMatchState") source at generated
  rw [generate_rootOnly] at generated
  split at generated
  · exact List.mem_singleton.mp generated
  · cases generated

private theorem constructor_label {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {initial captured : Assignment} {expected actual : String} {schemas targets : List Pattern}
    (matched : Matches rule spec ambient .left [] 0 initial
      (.apply expected schemas) (.apply actual targets) captured) : expected = actual := by
  cases matched
  rfl

private theorem premises_nil {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {initial final : Assignment} {history : List GeneralPremise.Event}
    (held : GeneralPremise.PremisesHold environment context [] initial final history) :
    final = initial ∧ history = [] := by
  cases held
  exact ⟨rfl, rfl⟩

theorem receipt_source_result (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) (query activeId : Nat)
    (store : List Occurrence) (known : List Pattern)
    (encoded : store.mapM (OccurrenceEncoding.encode? prepared.vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup) (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid (plan prepared) [] (.base "ChrMatchState")
      (request prepared.vocabulary query activeId known)) :
    ∃ (entry : Entry) (source : Rule) (environment : Environment) (selection : Selection),
      query = receipt.job.declaration.declarationIndex ∧
      prepared.entries[query]? = some entry ∧
      program.rules[entry.occurrence.rule]? = some source ∧
      entry.boundVariables = source.variables.eraseDups ∧
      RuleSelection.SourceReadout prepared.vocabulary (ordinary receipt.captured)
        entry.occurrence.head activeId source store environment selection ∧
      MatchedEncoding.result? prepared.vocabulary environment entry.boundVariables selection = some receipt.target := by
  have member := List.fst_mem_of_mem_zipIdx valid.1.1
  obtain ⟨entry, source, atEntry, _, sourceRead, compiled, _, boundVariables⟩ :=
    ProgramOrigins.plan_rule_origin program seeds prepared accepted receipt.job.declaration member
  have zero := selected_zero program seeds prepared accepted receipt.job.declaration member
  have flags := compiled_flags _ _ _ _ _ compiled
  have site := root_site prepared _ receipt.job.site valid.1.2
  have target : receipt.target = receipt.localTarget := by
    simpa only [site, SiteData.here, DerivedContexts.OneHoleContext.fill] using valid.2.2.2.1
  have declared := GeneralRuleJobs.Job.selected_rule valid.1
  have specified := GeneralRuleJobs.Job.selected_specification valid.1
  have firing := valid.2.1
  rw [site] at firing
  change GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (plan prepared))
    [] (.base "ChrMatchState") (request prepared.vocabulary query activeId known) receipt.job.ordinal
    receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget at firing
  cases firing with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ actualDeclared actualSpecified _ _ matched _ premises reduced _ =>
    have sameRule := Option.some.inj (actualDeclared.symm.trans declared)
    subst actualRule
    have sameSpec := Option.some.inj (actualSpecified.symm.trans specified)
    subst actualSpec
    have noPremises : receipt.job.declaration.rule.premises = [] := by
      simpa only [RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate] using flags.2
    rw [noPremises] at premises
    have completed := (premises_nil premises).1
    rw [completed] at reduced
    have plain := matched.matching
    have raw := plain.rule_fields
      (show receipt.job.declaration.rule.left = receipt.job.declaration.authored.left from rfl)
      (show receipt.job.declaration.rule.right = receipt.job.declaration.authored.right from rfl)
      (show receipt.job.declaration.rule.premises = receipt.job.declaration.authored.premises from rfl)
    change Matches receipt.job.declaration.authored receipt.job.declaration.binding.spec 0 .left [] 0 []
      receipt.job.declaration.authored.left (request prepared.vocabulary query activeId known) receipt.captured at raw
    obtain ⟨_, _, _, left, _⟩ := RuleSelection.compiled_data _ _ _ _ _ compiled
    have labelled := raw
    rw [left] at labelled
    have labels := constructor_label labelled
    have querySame : query = receipt.job.declaration.declarationIndex := by
      exact (Nat.repr_injective ((String.append_right_inj "ChrMatchQuery:").mp labels)).symm
    rw [querySame] at raw
    have roots := GeneralPremise.matching_rootValues zero (by intro name value found; cases found) raw
    obtain ⟨environment, selection, read⟩ := RuleSelection.source_selection prepared.vocabulary
      receipt.job.declaration.declarationIndex entry.occurrence.head activeId source receipt.job.declaration.authored
      store known compiled encoded distinct raw (by intro name value found; exact found) roots
    have result := MatchedEncoding.source_result prepared.vocabulary receipt.job.declaration.declarationIndex
      entry.occurrence.head activeId source receipt.job.declaration.authored store (ordinary receipt.captured)
      environment selection compiled read
    have free := MatchedEncoding.compiled_right_binderFree _ _ _ _ _ compiled
    have rightRead := binderFree_instantiation_readout free roots reduced
    refine ⟨entry, source, environment, selection, querySame, ?_, sourceRead, boundVariables, read, ?_⟩
    · simpa only [querySame] using atEntry
    · rw [boundVariables, target]
      exact result.trans (congrArg some rightRead)

theorem wrong_query_refused (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) (query activeId : Nat)
    (store : List Occurrence) (known : List Pattern)
    (encoded : store.mapM (OccurrenceEncoding.encode? prepared.vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup) (receipt : GeneralRuleJobs.Receipt)
    (different : query ≠ receipt.job.declaration.declarationIndex) :
    ¬ receipt.Valid (plan prepared) [] (.base "ChrMatchState")
      (request prepared.vocabulary query activeId known) := by
  intro valid
  obtain ⟨_, _, _, _, same, _⟩ := receipt_source_result program seeds prepared accepted query activeId
    store known encoded distinct receipt valid
  exact different same

#print axioms selected_zero
#print axioms root_site
#print axioms receipt_source_result
#print axioms wrong_query_refused

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.PlanReading
