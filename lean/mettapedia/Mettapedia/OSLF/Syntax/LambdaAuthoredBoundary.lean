import Mettapedia.OSLF.Syntax.LambdaContextualRung
import Mettapedia.OSLF.MeTTaIL.RuleBinding

/-!
# A binder-local premise boundary in the authored lambda rung

The source's LamCong rule asks for a step between bodies in the context of
the lambda binder. A direct translation to the current root `congruence`
premise would have to supply that binder at a premise site of depth zero.
The concrete attempt below is refused by the present occurrence-admission
check. This is a bounded obstruction for that translation, not a theorem that
no richer authored-premise interface can express LamCong.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaAuthoredBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

private def term : TypeExpr := .base "Term"

/-- The displayed LamCong shape translated into the current premise carrier.
Its intended premise is under the lambda binder; the current carrier records
that premise as a root congruence query. -/
def lamCongAttempt : RewriteRule :=
  { name := "LamCong"
    typeContext := [("S", term), ("T", term)]
    premises := [.congruence (.fvar "S") (.fvar "T")]
    left := .apply "Lam" [.lambda none (.fvar "S")]
    right := .apply "Lam" [.lambda none (.fvar "T")] }

/-- Supplying the lambda variable to each occurrence is the natural
dependency-aware reading of the source's body metavariables. -/
def attemptedBinding : RuleBindingSpec :=
  { dependencies := [("S", [term]), ("T", [term])]
    occurrences := [
      { name := "S", site := .left, path := [0, 0],
        arguments := [.bvar 0] },
      { name := "T", site := .right, path := [0, 0],
        arguments := [.bvar 0] },
      { name := "S", site := .premise 0 0 0, path := [],
        arguments := [.bvar 0] },
      { name := "T", site := .premise 0 0 1, path := [],
        arguments := [.bvar 0] }] }

theorem premise_sites_are_root_depth :
    (sitePattern? lamCongAttempt (.premise 0 0 0)).bind
        (occurrenceDepthAt? · [] 0) = some 0 ∧
    (sitePattern? lamCongAttempt (.premise 0 0 1)).bind
        (occurrenceDepthAt? · [] 0) = some 0 := by
  decide

theorem bound_argument_not_ground_at_premise :
    (Pattern.bvar 0).isGroundAt 0 = false := by
  decide

/-- The direct binder-dependent translation is not admitted because its
premise site lacks the binder that the left and right sides possess. -/
theorem attempted_binding_rejected :
    admittedFor lamCongAttempt attemptedBinding = false := by
  decide +kernel

end Mettapedia.OSLF.Binding.LambdaAuthoredBoundary
