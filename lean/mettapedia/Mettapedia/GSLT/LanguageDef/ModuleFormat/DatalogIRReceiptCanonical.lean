import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPhysicalCanonical
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSourcePlan

/-! Actual root receipts preserve the canonical physical fact encoding.
The relation slot comes from the request match; sorted value fields are
registered references in the prepared, duplicate-free literal pool. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ReceiptCanonical

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem root_target (pools : Join.Pools) (distinct : pools.literals.Nodup)
    (source : Mettapedia.Languages.Datalog.Atom) (position : Nat)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (left : rule.left = RequestInstances.schema pools)
    (right : Join.atom? pools position source = some rule.right)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    (environment : GeneralPremise.Environment)
    (grammar : environment.language.terms = Query.baseLanguage.terms)
    (free : environment.free = FreeTypeContext.ofList (Executable.freeTypes pools))
    (index : Nat) (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (firing : GeneralPremise.RootFiring environment [] (.base "DlStatement") (Executable.request pools)
      index trace captured completed history target) :
    ∃ fact : GroundFact, Executable.fact? pools fact = some target := by
  cases firing with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ actualDeclared actualSpecified _ _ matching capturedTyped premises reduced targetTyped =>
    have sameRule : actualRule = rule := Option.some.inj (actualDeclared.symm.trans declared)
    subst actualRule
    have sameSpec : actualSpec = spec := Option.some.inj (actualSpecified.symm.trans specified)
    subst actualSpec
    have roots := (premises.typed capturedTyped).rootValues zero
    have requestMatch : Matches rule spec 0 .left [] 0 [] (RequestInstances.schema pools) (Executable.request pools) captured := by
      simpa only [left,List.length_nil] using matching.matching
    have poolReads := RequestReading.physical_pools pools requestMatch premises.extension roots
    have reconstructed : applyBindings (ordinary completed) rule.right = target :=
      binderFree_instantiation_readout (ClauseDictionary.atom_binderFree pools position source rule.right right) roots reduced
    have typedInstance : OpenPatternWellSorted environment.language (FreeTypeContext.ofList (Executable.freeTypes pools)) []
        (.base "DlStatement") (applyBindings (ordinary completed) rule.right) := by
      rw [reconstructed,← free]
      exact targetTyped
    have encoded := PhysicalCanonical.atom_instance_encodes environment.language grammar pools distinct (ordinary completed)
      ⟨poolReads.1,poolReads.2⟩ position source rule.right right typedInstance
    simpa only [reconstructed] using encoded

theorem target (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (receipt : GeneralOccurrenceSemantics.Receipt)
    (valid : receipt.Valid (Executable.plan prepared known) [] (.base "DlStatement") (Executable.request prepared.vocabulary)) :
    ∃ fact : GroundFact, Executable.fact? prepared.vocabulary fact = some receipt.target := by
  have sameSource := (PlanReading.conversion_trivial program seeds prepared accepted known valid.1).1
  have firingValid : receipt.firing.Valid (Executable.plan prepared known) [] (.base "DlStatement") (Executable.request prepared.vocabulary) := by
    rw [sameSource]
    exact valid.2
  obtain ⟨ordinal,clause,rule,_,compiled,authored,_⟩ := PlanReading.declaration_source program seeds prepared accepted known _ receipt.firing firingValid
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
  have fields := FiringReading.compiled_fields prepared.vocabulary ordinal clause rule compiled
  have shape : receipt.firing.job.declaration.rule.left = rule.left ∧ receipt.firing.job.declaration.rule.right = rule.right := by
    change receipt.firing.job.declaration.authored.left = _ ∧ receipt.firing.job.declaration.authored.right = _
    rw [authored]
    exact ⟨rfl,rfl⟩
  have left : receipt.firing.job.declaration.rule.left = RequestInstances.schema prepared.vocabulary := shape.1.trans fields.1
  have right : Join.atom? prepared.vocabulary clause.body.length clause.head = some receipt.firing.job.declaration.rule.right := by
    rw [shape.2]
    exact fields.2
  have firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (Executable.plan prepared known)) [] (.base "DlStatement")
      (Executable.request prepared.vocabulary) receipt.firing.job.ordinal receipt.firing.matcherTrace receipt.firing.captured
      receipt.firing.completed receipt.firing.premiseHistory receipt.firing.localTarget := by
    simpa only [site,GeneralTypedSites.SiteData.here,GeneralPlanEnvironment.environmentWith_empty] using firingValid.2.1
  have distinct : prepared.vocabulary.literals.Nodup := by
    rw [Executable.prepare_vocabulary program seeds prepared accepted]
    exact List.nodup_dedup _
  obtain ⟨fact,encoded⟩ := root_target prepared.vocabulary distinct clause.head clause.body.length receipt.firing.job.declaration.rule
    receipt.firing.job.declaration.binding.spec left right zero (GeneralPlanEnvironment.environment (Executable.plan prepared known))
    (SourcePlan.plan_grammar program seeds prepared accepted known) (SourcePlan.plan_free prepared known) _ declared specified firing
  have targetRead := firingValid.2.2.2.1
  simp only [site,GeneralTypedSites.SiteData.here,DerivedContexts.OneHoleContext.fill] at targetRead
  refine ⟨fact,?_⟩
  change Executable.fact? prepared.vocabulary fact = some receipt.firing.target
  rw [targetRead]
  exact encoded

#print axioms root_target
#print axioms target

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ReceiptCanonical
