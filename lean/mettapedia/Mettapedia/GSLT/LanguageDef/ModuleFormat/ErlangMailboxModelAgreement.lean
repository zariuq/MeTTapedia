import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxExecution
import Mettapedia.OSLF.Framework.GeneralReferenceAgreement
import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment
import Mettapedia.OSLF.MeTTaIL.Complete.Termination

/-! The actual compiled mailbox plan preserves and reflects authored root
steps. Receipts retain their ordinals, captures and histories. Their readback
does not assume that a target is already in the queue encoding image. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Model

open Mettapedia.OSLF.MeTTaIL Syntax GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
open QuantifiedReference

def environment : GeneralPremise.Environment := GeneralPlanEnvironment.environment plan
abbrev Sorted := OpenPatternWellSorted environment.language environment.free [] (.base "ErMailboxConfig")

set_option cbv.maxSteps 2000000 in
theorem uniform_checked : checkUniformDirectedProfile environment [.base "ErMailboxConfig"] = true := by decide_cbv

theorem uniform_profile :
    UniformDirectedProfile (fun schema => Match.binderFree schema = true) environment [.base "ErMailboxConfig"] :=
  UniformDirectedProfile.of_check uniform_checked

theorem same_core : environment.language.rewrites.map ruleCore = language.rewrites.map ruleCore := by cbv

theorem aligned : ReferenceStep.ReferenceProfile language := by
  intro rule member
  have all : language.rewrites.all ReferenceStep.ruleAligned = true := by decide_cbv
  exact List.all_eq_true.mp all rule member

theorem roots_readback {source target : Pattern}
    (fired : ∃ index trace captured completed history,
      GeneralPremise.RootFiring environment [] (.base "ErMailboxConfig") source
        index trace captured completed history target) :
    ContextualStep.Step (ContextualStep.engineBasePremises Engine.RelationEnv.empty) language source target := by
  have reference := directed_step_toReference_of_forward
    (uniform_profile.forward (type := .base "ErMailboxConfig") (by simp)) Engine.RelationEnv.empty (ReadsProvider.empty _) fired
  have original := (reference_step_same_core_iff same_core Engine.RelationEnv.empty).mp reference
  exact (ReferenceStep.contextualStep_iff_step Engine.RelationEnv.empty language aligned).mpr original

theorem roots_iff_reference {source target : Pattern} (typed : Sorted source) :
    (∃ index trace captured completed history,
      GeneralPremise.RootFiring environment [] (.base "ErMailboxConfig") source
        index trace captured completed history target) ↔
      ContextualStep.Step (ContextualStep.engineBasePremises Engine.RelationEnv.empty) language source target :=
  ((uniform_profile).roots_iff_reference Engine.RelationEnv.empty
    (ReadsProvider.empty _) (by simp) typed).trans
    ((reference_step_same_core_iff same_core Engine.RelationEnv.empty).trans
      (ReferenceStep.contextualStep_iff_step Engine.RelationEnv.empty language aligned).symm)

theorem equations_empty : plan.equations = [] := by cbv

theorem site_here {source : Pattern} {job : GeneralRuleJobs.Job}
    (valid : job.Valid plan [] (.base "ErMailboxConfig") source) :
    job.site = SiteData.here [] (.base "ErMailboxConfig") source := by
  have generated := generate_complete valid.2
  change job.site ∈ generate environment.language environment.free .rootOnly [] (.base "ErMailboxConfig") source at generated
  rw [generate_rootOnly] at generated
  split at generated
  · exact List.mem_singleton.mp generated
  · cases generated

theorem primitive_readback {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan [] (.base "ErMailboxConfig") source) :
    ContextualStep.Step (ContextualStep.engineBasePremises Engine.RelationEnv.empty) language source receipt.target := by
  obtain ⟨licensed, fired, represented, endpoint, targetTyped⟩ := valid
  have here := site_here licensed
  have localFiring : GeneralPremise.RootFiring environment [] (.base "ErMailboxConfig") source
      receipt.job.ordinal receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget := by
    simpa only [here, SiteData.here, GeneralPlanEnvironment.environmentWith_empty, environment] using fired
  have outer : receipt.target = receipt.localTarget := by
    simpa only [here, SiteData.here, DerivedContexts.OneHoleContext.fill] using endpoint
  rw [outer]
  exact roots_readback ⟨_, _, _, _, _, localFiring⟩

theorem primitive_complete {source target : Pattern} (typed : Sorted source)
    (step : ContextualStep.Step (ContextualStep.engineBasePremises Engine.RelationEnv.empty) language source target) :
    ∃ receipt : GeneralRuleJobs.Receipt,
      receipt.Valid plan [] (.base "ErMailboxConfig") source ∧ receipt.target = target := by
  obtain ⟨index, trace, captured, completed, history, firing⟩ := (roots_iff_reference typed).mpr step
  have targetTyped : Sorted target := by
    cases firing with
    | fire _ _ _ _ _ _ _ _ sorted => exact sorted
  have declared : ∃ rule, environment.language.rewrites[index]? = some rule := by
    cases firing with
    | fire declared _ _ _ _ _ _ _ _ => exact ⟨_, declared⟩
  have position : ∃ declaration, plan.rules[index]? = some declaration := by
    obtain ⟨rule, declared⟩ := declared
    change (plan.rules.map GeneralExecutionAdmission.RulePlan.rule)[index]? = some rule at declared
    rw [List.getElem?_map] at declared
    cases found : plan.rules[index]? with
    | none => simp [found] at declared
    | some declaration => exact ⟨declaration, rfl⟩
  obtain ⟨declaration, selected⟩ := position
  let job : GeneralRuleJobs.Job := ⟨index, declaration, SiteData.here [] (.base "ErMailboxConfig") source⟩
  have generated : SiteData.here [] (.base "ErMailboxConfig") source ∈
      generate environment.language environment.free .rootOnly [] (.base "ErMailboxConfig") source := by
    rw [generate_rootOnly, if_pos ⟨typed.2.2.1,
      checkHasType_complete_of_object typed.1 typed.2.2.1⟩]
    exact List.mem_singleton_self _
  have licensed : job.Valid plan [] (.base "ErMailboxConfig") source :=
    ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, (generate_spec _ _ _ _ _ _ _).mp generated⟩
  refine ⟨⟨job, trace, captured, completed, history, target, target⟩, ?_, rfl⟩
  exact ⟨licensed, firing, rfl, rfl, targetTyped⟩

theorem step_readback {source target : Pattern}
    (step : (GeneralOccurrenceSemantics.gslt plan [] (.base "ErMailboxConfig")).Step source target) :
    ContextualStep.Step (ContextualStep.engineBasePremises Engine.RelationEnv.empty) language source target ∧
      Sorted target := by
  obtain ⟨representative, receipt, before, valid, after⟩ := step
  have same := Complete.Classes.equivalent_eq_of_no_equations plan [] (.base "ErMailboxConfig") equations_empty before
  subst representative
  have endpoint := Complete.Classes.equivalent_eq_of_no_equations plan [] (.base "ErMailboxConfig") equations_empty after
  have typed : Sorted receipt.target := valid.2.2.2.2
  rw [← endpoint]
  exact ⟨primitive_readback valid, typed⟩

theorem step_iff_reference {source target : Pattern} (typed : Sorted source) :
    (GeneralOccurrenceSemantics.gslt plan [] (.base "ErMailboxConfig")).Step source target ↔
      ContextualStep.Step (ContextualStep.engineBasePremises Engine.RelationEnv.empty) language source target := by
  constructor
  · exact fun step => (step_readback step).1
  · intro step
    obtain ⟨receipt, valid, endpoint⟩ := primitive_complete typed step
    exact ⟨source, receipt, .refl _, valid, endpoint ▸ Relation.EqvGen.refl _⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Model
