import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

/-! Valid receipts under root-only permissions expose an actual root firing.
The inverse retains the selected compiled row, captures and premise history.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

open Syntax GeneralTypedSites

theorem rootOnly_receipt {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {receipt : Receipt} (root : plan.permissions.sites = .rootOnly)
    (valid : receipt.Valid plan bound type source) :
    plan.rules[receipt.job.ordinal]? = some receipt.job.declaration ∧
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source receipt.job.ordinal
        receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.target := by
  have licensed := valid.1.2
  rw [root] at licensed
  have generated := (generate_spec _ _ _ _ _ _ _).mpr licensed
  rw [generate_rootOnly] at generated
  split at generated
  · have same : receipt.job.site = SiteData.here bound type source := List.mem_singleton.mp generated
    refine ⟨List.mk_mem_zipIdx_iff_getElem?.mp valid.1.1, ?_⟩
    have firing := valid.2.1
    have output := valid.2.2.2.1
    rw [same] at firing output
    simp only [SiteData.here, DerivedContexts.OneHoleContext.fill] at firing output
    rw [output]
    exact firing
  · cases generated

#print axioms rootOnly_receipt

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
