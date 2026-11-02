import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlProviderPlanWire
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderEpoch

/-! The wire table update is the exact emitted plan of the new provider
epoch. Rule and equation metadata remain unchanged; the provider is the
only operational field replaced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochPlanWire

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax

theorem metadata_same (prepared : Prepared) (first second : GeneralPremise.ProviderSnapshot)
    (firstSignatures : first.signatures = provider.signatures) (secondSignatures : second.signatures = provider.signatures)
    (expected : TypeExpr) :
    OCamlProviderPlanWire.fields (epochPlan prepared first) expected =
      OCamlProviderPlanWire.fields (epochPlan prepared second) expected := by
  have rules : (epochPlan prepared first).rules = (epochPlan prepared second).rules :=
    (epoch_rules prepared first firstSignatures).trans (epoch_rules prepared second secondSignatures).symm
  have equations : (epochPlan prepared first).equations = (epochPlan prepared second).equations :=
    (epoch_equations prepared first firstSignatures).trans (epoch_equations prepared second secondSignatures).symm
  have rewrites : (GeneralPlanEnvironment.environment (epochPlan prepared first)).language.rewrites =
      (GeneralPlanEnvironment.environment (epochPlan prepared second)).language.rewrites := congrArg (List.map GeneralExecutionAdmission.RulePlan.rule) rules
  have specs : (GeneralPlanEnvironment.environment (epochPlan prepared first)).specifications =
      (GeneralPlanEnvironment.environment (epochPlan prepared second)).specifications := by
    change ((epochPlan prepared first).rules.zipIdx.map fun (row, index) => (index, row.binding.spec)) = _
    rw [rules]
    rfl
  have depth : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment (epochPlan prepared first)) =
      StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment (epochPlan prepared second)) := by
    unfold StructuralDescent.checkEnvironment GeneralPremise.specification?
    rw [rewrites, specs]
  have declarations : ∀ equation,
      CompletePlanWire.equationDeclarationTerm (epochPlan prepared first) equation =
        CompletePlanWire.equationDeclarationTerm (epochPlan prepared second) equation := by
    intro equation
    simp only [CompletePlanWire.equationDeclarationTerm, CompletePlanWire.equationDepthTerm, depth]
  unfold OCamlProviderPlanWire.fields
  rw [rewrites, specs, rules, equations, depth]
  congr 1
  exact congrArg (fun encode => encodeList encode (epochPlan prepared second).equations.zipIdx) (funext declarations)

theorem epoch_plan_exact (prepared : Prepared) (first second : GeneralPremise.ProviderSnapshot)
    (firstSignatures : first.signatures = provider.signatures) (secondSignatures : second.signatures = provider.signatures)
    (expected : TypeExpr) :
    ProviderCacheExecution.planTerm prepared.compiled [] [] second
      (OCamlProviderPlanWire.fields (epochPlan prepared first) expected) =
      CompletePlanWire.planTerm (epochPlan prepared second) [] [] expected := by
  rw [metadata_same prepared first second firstSignatures secondSignatures expected]
  exact OCamlProviderPlanWire.emitted_plan_exact (epochPlan prepared second) [] [] expected

#print axioms metadata_same
#print axioms epoch_plan_exact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochPlanWire
