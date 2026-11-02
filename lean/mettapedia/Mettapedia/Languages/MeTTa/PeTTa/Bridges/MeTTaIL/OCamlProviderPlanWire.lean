import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ProviderCacheExecution

/-! Provider-cache transport reads the exact emitted plan layout. Existing
rule indexes, equation jobs and binding specifications remain verbatim when
only the provider table changes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlProviderPlanWire

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax

def fields (plan : GeneralExecutionAdmission.Plan) (expected : TypeExpr) :
    ProviderCacheExecution.Fields := {
  rewrites := encodeList InferenceCettaWire.AuthoredRule.rewriteTerm (GeneralPlanEnvironment.environment plan).language.rewrites
  specifications := encodeList PremiseOperationsExecution.GeneralExecution.specificationTerm
    (GeneralPlanEnvironment.environment plan).specifications
  reflection := PremiseOperationsExecution.GeneralExecution.reflectionTerm plan.permissions.reflection
  permissions := InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites
  expected := InferenceCettaWire.AuthoredRule.typeTerm expected
  rules := encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules
  equations := encodeList (CompletePlanWire.equationDeclarationTerm plan) plan.equations.zipIdx
  admitted := CompletePlanWire.admittedTerm (StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan)) }

theorem emitted_plan_exact (plan : GeneralExecutionAdmission.Plan) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (expected : TypeExpr) :
    ProviderCacheExecution.planTerm plan.snapshot.language free bound plan.snapshot.provider (fields plan expected) =
      CompletePlanWire.planTerm plan free bound expected := by
  rfl

#print axioms emitted_plan_exact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlProviderPlanWire
