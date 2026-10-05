import Mettapedia.Languages.VibeITP.Presentation.Rules
import Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection

/-!
# Vibe-ITP presentation: the kernel as a calculus language definition

The fixed kernel package is one `CalculusLanguageDef`: its `LanguageDef`
declares the data constructors of `Syntax` over one data sort, its judgments
are the kernel judgments, and its rules are `kernelRules`.

This presentation targets Mirek Olšák's
[Vibe-ITP](https://git.olsak.net/mirek/Vibe-ITP). See
`Mettapedia.Languages.VibeITP.Spec.Basic` for the reference revision and sources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection

def kernelProfile : CacheProfile :=
  { dataSort := "VibeData", cacheName := "vibe-itp-kernel-v1" }

def kernelJudgments : List JudgmentDecl :=
  judgmentArities.map fun (head, arity) => { head, arity }

/-- The kernel presentation with an additional list of admitted rules. -/
def kernelDefinitionWith (admitted : List FORule) : CalculusLanguageDef :=
  cacheDefinition kernelProfile constructorArities kernelJudgments
    ((kernelRules ++ admitted).map FORule.toSchema)

def kernelDefinition : CalculusLanguageDef := kernelDefinitionWith []

set_option maxRecDepth 100000 in
theorem kernelDefinition_valid : kernelDefinition.isValid = true := by
  decide +kernel

end Mettapedia.Languages.VibeITP.Presentation
