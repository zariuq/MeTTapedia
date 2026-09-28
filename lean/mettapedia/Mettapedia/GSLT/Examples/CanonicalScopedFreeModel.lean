import Mettapedia.OSLF.Syntax.CanonicalScopedOperationalClassification
import Mettapedia.GSLT.Examples.CanonicalScopedRuleExecution
import Mettapedia.GSLT.Examples.ScopedLamCongFreeModel

/-!
# Checked canonical lambda execution in the certified free model

The actual authored lambda language compiles to scoped premises, and its
open-variable LamCong history is exactly recognized by the certified free
rule algebra. A fabricated child ordinal is excluded at the same endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.CanonicalScopedFreeModel

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution
open Mettapedia.OSLF.Binding.CanonicalScopedOperationalClassification
open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.GSLT.Examples.ScopedLamCongFreeModel
open Mettapedia.GSLT.Examples.CanonicalScopedRuleExecution

private def actualHistory : RuleHistory :=
  .fire 1 [.step 0 0 (.fire 0 [])]

/-- The checked canonical language retains the actual binder-local beta
child and its authored rule and oracle positions. -/
theorem canonical_lamCong_certified :
    (actualHistory, wrappedTarget) ∈
      (canonicalStage? RelationEnv.empty language 1 [] wrappedRedex).getD [] := by
  exact (canonicalStage?_certified_iff RelationEnv.empty language 1 []
    wrappedRedex wrappedTarget actualHistory _ lambda_rules_compile).mpr
      authored_lamCong_certified_derivation

/-- The same endpoint is not a license to invent a second child occurrence.
The canonical route rejects that proposed history. -/
theorem wrong_child_ordinal_absent :
    (.fire 1 [.step 0 1 (.fire 0 [])], wrappedTarget) ∉
      (canonicalStage? RelationEnv.empty language 1 [] wrappedRedex).getD [] := by
  intro emitted
  exact wrong_child_ordinal_not_certified
    ((canonicalStage?_certified_iff RelationEnv.empty language 1 []
      wrappedRedex wrappedTarget
      (.fire 1 [.step 0 1 (.fire 0 [])]) _
      lambda_rules_compile).mp emitted)

#print axioms canonical_lamCong_certified
#print axioms wrong_child_ordinal_absent

end Mettapedia.GSLT.Examples.CanonicalScopedFreeModel
