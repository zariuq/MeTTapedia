import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoProducerAgreement
import Mettapedia.OSLF.MeTTaIL.Complete.Termination

/-! The actual root-only compiled plan's occurrence semantics agrees with
source Peano equation reduction. Complete receipts keep their native traces
and histories; only their source meaning is read back here. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoModel

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open PeanoProducer

theorem equations_empty (context : Maude.VariableContext) : (compiledPlan context).equations = [] := by cbv

theorem site_here {context : Maude.VariableContext} {source : Pattern} {job : GeneralRuleJobs.Job}
    (valid : job.Valid (compiledPlan context) [] (.base "Nat") source) :
    job.site = SiteData.here [] (.base "Nat") source := by
  have generated := generate_complete valid.2
  change job.site ∈ generate (environment context).language (environment context).free .rootOnly [] (.base "Nat") source at generated
  rw [generate_rootOnly] at generated
  split at generated
  · exact List.mem_singleton.mp generated
  · cases generated

theorem primitive_readback {context : Maude.VariableContext} {source : Maude.Term}
    {receipt : GeneralRuleJobs.Receipt}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (valid : receipt.Valid (compiledPlan context) [] (.base "Nat") (encode source)) :
    ∃ result, receipt.target = encode result ∧ Maude.EquationReduction Maude.Examples.peano context "Nat" source result := by
  obtain ⟨licensed, fired, represented, endpoint, targetTyped⟩ := valid
  have here := site_here licensed
  have localFiring : GeneralPremise.RootFiring (environment context) [] (.base "Nat") (encode source)
      receipt.job.ordinal receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget := by
    simpa only [here, SiteData.here, GeneralPlanEnvironment.environmentWith_empty,
      PeanoProducer.environment] using fired
  obtain ⟨result, decoded, reduced⟩ := root_readback typed
    ⟨receipt.job.ordinal, receipt.matcherTrace, receipt.captured, receipt.completed, receipt.premiseHistory, localFiring⟩
  refine ⟨result, ?_, reduced⟩
  have outer : receipt.target = receipt.localTarget := by
    simpa only [here, SiteData.here, DerivedContexts.OneHoleContext.fill] using endpoint
  exact outer.trans decoded

theorem primitive_complete {context : Maude.VariableContext} {source target : Maude.Term}
    (step : Maude.EquationReduction Maude.Examples.peano context "Nat" source target) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid (compiledPlan context) [] (.base "Nat") (encode source) ∧ receipt.target = encode target := by
  have sourceTyped := source_typed context source step.sorted.1
  have targetTyped := source_typed context target step.sorted.2
  obtain ⟨index, trace, captured, completed, history, firing⟩ := (roots_iff_source step.sorted.1).mpr step
  have declared : ∃ rule, (environment context).language.rewrites[index]? = some rule := by
    cases firing with
    | fire declared _ _ _ _ _ _ _ _ => exact ⟨_, declared⟩
  have position : ∃ declaration, (compiledPlan context).rules[index]? = some declaration := by
    obtain ⟨rule, declared⟩ := declared
    change ((compiledPlan context).rules.map GeneralExecutionAdmission.RulePlan.rule)[index]? = some rule at declared
    rw [List.getElem?_map] at declared
    cases found : (compiledPlan context).rules[index]? with
    | none => simp [found] at declared
    | some declaration => exact ⟨declaration, rfl⟩
  obtain ⟨declaration, selected⟩ := position
  let job : GeneralRuleJobs.Job := ⟨index, declaration, SiteData.here [] (.base "Nat") (encode source)⟩
  have generated : SiteData.here [] (.base "Nat") (encode source) ∈
      generate (environment context).language (environment context).free .rootOnly [] (.base "Nat") (encode source) := by
    rw [generate_rootOnly, if_pos ⟨sourceTyped.2.2.1,
      checkHasType_complete_of_object sourceTyped.1 sourceTyped.2.2.1⟩]
    exact List.mem_singleton_self _
  have licensed : job.Valid (compiledPlan context) [] (.base "Nat") (encode source) :=
    ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, (generate_spec _ _ _ _ _ _ _).mp generated⟩
  refine ⟨⟨job, trace, captured, completed, history, encode target, encode target⟩, ?_, rfl⟩
  exact ⟨licensed, firing, rfl, rfl, targetTyped⟩

theorem step_readback {context : Maude.VariableContext} {source : Maude.Term} {target : Pattern}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (step : (GeneralOccurrenceSemantics.gslt (compiledPlan context) [] (.base "Nat")).Step (encode source) target) :
    ∃ result, target = encode result ∧ Maude.EquationReduction Maude.Examples.peano context "Nat" source result := by
  obtain ⟨representative, receipt, before, valid, after⟩ := step
  have same := Complete.Classes.equivalent_eq_of_no_equations (compiledPlan context) [] (.base "Nat")
    (equations_empty context) before
  subst representative
  obtain ⟨result, decoded, reduced⟩ := primitive_readback typed valid
  have endpoint := Complete.Classes.equivalent_eq_of_no_equations (compiledPlan context) [] (.base "Nat")
    (equations_empty context) after
  exact ⟨result, endpoint.symm.trans decoded, reduced⟩

theorem step_iff_source {context : Maude.VariableContext} {source target : Maude.Term}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") :
    (GeneralOccurrenceSemantics.gslt (compiledPlan context) [] (.base "Nat")).Step (encode source) (encode target) ↔
      Maude.EquationReduction Maude.Examples.peano context "Nat" source target := by
  constructor
  · intro step
    obtain ⟨result, same, reduced⟩ := step_readback typed step
    have sourceSame := encode_injective same
    subst result
    exact reduced
  · intro step
    obtain ⟨receipt, valid, endpoint⟩ := primitive_complete step
    exact ⟨encode source, receipt, .refl _, valid, endpoint ▸ Relation.EqvGen.refl _⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoModel
