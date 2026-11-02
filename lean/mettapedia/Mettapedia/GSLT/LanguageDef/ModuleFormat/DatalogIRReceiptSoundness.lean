import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPlanReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRRootTotality
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticAdmission

/-! Actual shared-plan receipts reflect to independently derivable Datalog
facts. Zero-dependency scope evidence comes from the existing static checker. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ReceiptSoundness

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch
open GeneralFirstOrderProjection

theorem source_authorized (program : Program) (input : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program input = .ok prepared) (known : List Pattern) (facts : List GroundFact)
    (represented : ∀ value ∈ known, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact)
    (checked : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (receipt : GeneralOccurrenceSemantics.Receipt)
    (valid : receipt.Valid (Executable.plan prepared known) [] (.base "DlStatement") (Executable.request prepared.vocabulary))
    : ∃ row : GroundInstances.Instance, Executable.decodeFact? prepared receipt.target = some row.conclusion ∧
      ProgramGrounding.SourceAuthorized Executable.policy program facts row := by
  have sameSource := (PlanReading.conversion_trivial program input prepared accepted known valid.1).1
  have firingValid : receipt.firing.Valid (Executable.plan prepared known) [] (.base "DlStatement")
      (Executable.request prepared.vocabulary) := by rw [sameSource]; exact valid.2
  obtain ⟨ordinal,clause,rule,source,compiled,authored,_⟩ :=
    PlanReading.declaration_source program input prepared accepted known _ receipt.firing firingValid
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
  obtain ⟨actualSpec,actualSpecified,_,ruleChecked⟩ := GeneralPremise.Static.checkLanguage_rule checked originalDeclared
  have sameSpec : actualSpec = receipt.firing.job.declaration.binding.spec := Option.some.inj (actualSpecified.symm.trans originalSpecified)
  subst actualSpec
  have zero : GeneralPremise.checkZeroDependencies receipt.firing.job.declaration.binding.spec = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ruleChecked).1).1).1
  have shape : receipt.firing.job.declaration.rule.left = rule.left ∧
      receipt.firing.job.declaration.rule.right = rule.right ∧ receipt.firing.job.declaration.rule.premises = rule.premises := by
    change receipt.firing.job.declaration.authored.left = _ ∧ receipt.firing.job.declaration.authored.right = _ ∧
      receipt.firing.job.declaration.authored.premises = _
    rw [authored]
    exact ⟨rfl,rfl,rfl⟩
  have firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (Executable.plan prepared known)) [] (.base "DlStatement")
      (Executable.request prepared.vocabulary) receipt.firing.job.ordinal receipt.firing.matcherTrace receipt.firing.captured
      receipt.firing.completed receipt.firing.premiseHistory receipt.firing.localTarget := by
    simpa only [site,GeneralTypedSites.SiteData.here,GeneralPlanEnvironment.environmentWith_empty] using firingValid.2.1
  obtain ⟨row,decoded,authorized⟩ := RootTotality.source_authorized program input prepared accepted known facts represented
    ordinal clause rule source compiled receipt.firing.job.declaration.rule receipt.firing.job.declaration.binding.spec shape zero
    rfl declared specified firing
  have target := firingValid.2.2.2.1
  simp only [site,GeneralTypedSites.SiteData.here,DerivedContexts.OneHoleContext.fill] at target
  refine ⟨row,?_,authorized⟩
  change Executable.decodeFact? prepared receipt.firing.target = some row.conclusion
  rw [target]
  exact decoded

theorem source_derives (program : Program) (seeds input : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program input = .ok prepared) (known : List Pattern) (facts : List GroundFact)
    (represented : ∀ value ∈ known, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact)
    (derived : ∀ fact ∈ facts, Closure.Derives Executable.policy program seeds fact)
    (checked : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (receipt : GeneralOccurrenceSemantics.Receipt)
    (valid : receipt.Valid (Executable.plan prepared known) [] (.base "DlStatement") (Executable.request prepared.vocabulary))
    (fact : GroundFact) (decoded : Executable.decodeFact? prepared receipt.target = some fact) :
    Closure.Derives Executable.policy program seeds fact := by
  obtain ⟨row,read,authorized⟩ := source_authorized program input prepared accepted known facts represented checked receipt valid
  have same : row.conclusion = fact := Option.some.inj (read.symm.trans decoded)
  rw [← same]
  exact .fire row (Closure.authorized_on_premises _ _ _ _ authorized)
    (fun premise member => derived premise (Closure.source_firing_premises authorized premise member))

#print axioms source_authorized
#print axioms source_derives

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ReceiptSoundness
