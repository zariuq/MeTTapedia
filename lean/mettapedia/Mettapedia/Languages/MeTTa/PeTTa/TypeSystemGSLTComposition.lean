import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# The PeTTa typing tower as a validated definition extension

The guard layer is no longer an ad-hoc list append: it is a first-class
`ValidatedCalculusLanguageExtension` of the core definition — delta as data, executable
disjointness, an explicit conservativity policy (every guard rule
concludes a judgment head the core does not declare), composite validity,
and derivation transport by construction.  The determinism layer joins
the same tower next.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTComposition

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT
open Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard

/-- The guard layer as an extension delta over the core. -/
def guardExtension : CalculusLanguageExtension :=
  { newTerms := TypeSystemGSLTGuard.newTerms
    newJudgments := TypeSystemGSLTGuard.newJudgments
    newRules := TypeSystemGSLTGuard.exportRules
    rename := some "petta-typecheck-v2-guard" }

/-- The composition IS the guard language, definitionally. -/
theorem guard_language_is_composition :
    (guardExtension.apply coreDefinition).toLanguageDef = guardLanguage := by
  rfl

/-- Reassembling the validated extension as the flat authoring type recovers
the one guard definition exactly. -/
theorem guard_definition_is_composition :
    guardExtension.apply coreDefinition = guardDefinition := by
  rfl

/-- Core → guard as a validated extension: disjoint identifiers, the
conservative policy (guard rules conclude only NEW judgment heads), and
the composite's own validity receipt. -/
def coreToGuard : ValidatedCalculusLanguageExtension checked :=
  { extension := guardExtension
    policy := .newJudgmentsOnly
    disjoint := by decide
    policyHolds := by decide
    valid := by
      show guardDefinition.isValid = true
      exact guard_definition_valid }

/-- The tower's composite coincides with the guard module's checked
definition. -/
theorem coreToGuard_target :
    coreToGuard.target.1 = guardDefinition := by rfl

/-- Every core derivation transports unchanged into the composed
definition (Co11's preservation obligation, by construction). -/
def transportCoreDerivation {goal : Pattern}
    (derivation : Derivation checked goal) :
    Derivation coreToGuard.target goal :=
  coreToGuard.transport derivation

end Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTComposition
