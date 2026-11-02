import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

/-! An actual typed root firing yields a receipt at the root occurrence.
The selected declaration is recovered from its indexed plan entry. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

open Syntax GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

theorem root_receipt (plan : Plan) (enabled : plan.permissions.sites.enabled = true)
    (bound : List TypeExpr) (type : TypeExpr) (source target : Pattern) (index : Nat)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source index trace captured completed history target) :
    ∃ receipt : Receipt, receipt.Valid plan bound type source ∧ receipt.target = target ∧ receipt.job.ordinal = index := by
  cases firing with
  | @fire bound type source target index rule spec captured completed trace history declared specified admitted sourceTyped matched capturedTyped premises reduced targetTyped =>
    have mapped : (plan.rules[index]?).map RulePlan.rule = some rule := by
      simpa only [GeneralPlanEnvironment.environment,List.getElem?_map] using declared
    obtain ⟨entry,atEntry,sameRule⟩ := Option.map_eq_some_iff.mp mapped
    have entrySpecified := GeneralPlanEnvironment.selected_specification plan atEntry
    have sameSpec : spec = entry.binding.spec := Option.some.inj (specified.symm.trans entrySpecified)
    subst rule
    subst spec
    let job : Job := ⟨index,entry,SiteData.here bound type source⟩
    let receipt : Receipt := ⟨job,trace,captured,completed,history,target,target⟩
    have licensed : job.Valid plan bound type source :=
      ⟨List.mk_mem_zipIdx_iff_getElem?.mpr atEntry,.here enabled sourceTyped.2.2.1 sourceTyped.1⟩
    have whole : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source index trace captured completed history target :=
      .fire declared specified admitted sourceTyped matched capturedTyped premises reduced targetTyped
    refine ⟨receipt,?_,rfl,rfl⟩
    exact ⟨licensed,by simpa only [receipt,job,SiteData.here,GeneralPlanEnvironment.environmentWith_empty] using whole,rfl,rfl,targetTyped⟩

#print axioms root_receipt

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
