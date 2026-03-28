import GFCore.Check
import Algorithms.GF.Generated.PaperAmbiguitySig
import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises

/-!
# GF Generated-Bridge Conformance

This module pins the GF→OSLF bridge to a real auto-generated `GrammarSig`
coming from the GF side, not a hand-authored shadow grammar.

We use `Algorithms.GF.Generated.PaperAmbiguitySig.sig`, which is generated from
the GF PGF export pipeline, and then check:

- the generated `LanguageDef` reuses the authored semantic kernel,
- real GF raw terms check successfully through `GFCore.check`,
- the resulting `CheckedExpr` values lower through `gfCheckedExprToPattern`,
- the actual rewrite engine produces the expected semantic reductions.

Positive examples:
- `UseN(man_N)` reduces to `man_N`,
- active voice reduces to passive voice.

Negative examples:
- unsupported shared-kernel rules are excluded rather than silently claimed for
  this generated signature,
- active→passive remains one-directional.
-/

namespace Mettapedia.Languages.GF.GeneratedBridgeConformance

open GFCore
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises

def paperSig : GrammarSig :=
  Algorithms.GF.Generated.PaperAmbiguitySig.sig

def paperLang : LanguageDef :=
  gfRGLLanguageDef paperSig

def validationErrors : List ValidationError :=
  LanguageDef.validate paperLang

def checkedPattern? (t : RawTerm) : Option Pattern :=
  match check paperSig t with
  | .ok e => some (gfCheckedExprToPattern e)
  | .error _ => none

def useNManRaw : RawTerm :=
  .mk "UseN" #[.leaf "man_N"]

def useNManPattern : Pattern :=
  .apply "UseN" [.apply "man_N" []]

def manPattern : Pattern :=
  .apply "man_N" []

def johnNPPattern : Pattern :=
  .apply "UsePN" [.apply "john_PN" []]

def annaNPPattern : Pattern :=
  .apply "UsePN" [.apply "anna_PN" []]

def activeClauseRaw : RawTerm :=
  .mk "PredVP" #[
    .mk "UsePN" #[.leaf "john_PN"],
    .mk "ComplSlash" #[
      .mk "SlashV2a" #[.leaf "see_V2"],
      .mk "UsePN" #[.leaf "anna_PN"]
    ]
  ]

def activeClausePattern : Pattern :=
  .apply "PredVP"
    [ johnNPPattern
    , .apply "ComplSlash"
        [ .apply "SlashV2a" [.apply "see_V2" []]
        , annaNPPattern
        ]
    ]

def passiveClausePattern : Pattern :=
  .apply "PredVP"
    [ annaNPPattern
    , .apply "PassV2" [.apply "see_V2" []]
    ]

def presentSentenceRaw : RawTerm :=
  .mk "UseCl" #[
    .mk "TTAnt" #[.leaf "TPres", .leaf "ASimul"],
    .leaf "PPos",
    activeClauseRaw
  ]

def presentSentencePattern : Pattern :=
  .apply "UseCl"
    [ .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]
    , .apply "PPos" []
    , activeClausePattern
    ]

def temporalPresentPattern : Pattern :=
  .apply "⊛temporal" [activeClausePattern, .apply "0" []]

example : paperLang.name = "PaperAmbiguity" := rfl

example : paperLang.equations = gfSemanticEquationsForSig paperSig := rfl

example : paperLang.rewrites = gfSemanticRewritesForSig paperSig := rfl

example : paperLang.equations.length = 1 := by
  native_decide

example : paperLang.rewrites.length ≥ 4 := by
  native_decide

example : paperLang.equations.map (·.name) = ["UseNIdentity"] := by
  native_decide

example : validationErrors = [] := by
  native_decide

example : checkedPattern? useNManRaw = some useNManPattern := by
  native_decide

example : checkedPattern? activeClauseRaw = some activeClausePattern := by
  native_decide

example : checkedPattern? presentSentenceRaw = some presentSentencePattern := by
  native_decide

/- Positive: a real generated GF term hits the authored `UseN` semantic rule. -/
example : manPattern ∈ rewriteWithContextWithPremises paperLang useNManPattern := by
  native_decide

example :
    DeclReducesWithPremises RelationEnv.empty paperLang useNManPattern manPattern := by
  exact engineWithPremises_sound (lang := paperLang) (p := useNManPattern)
    (q := manPattern) (by native_decide)

/- Positive: active→passive reduction works on a real generated GF clause. -/
example :
    passiveClausePattern ∈
      rewriteWithContextWithPremises paperLang activeClausePattern := by
  native_decide

example :
    DeclReducesWithPremises RelationEnv.empty paperLang
      activeClausePattern passiveClausePattern := by
  exact engineWithPremises_sound (lang := paperLang) (p := activeClausePattern)
    (q := passiveClausePattern) (by native_decide)

/- Negative: the reduction is directional only. -/
example :
    activeClausePattern ∉
      rewriteWithContextWithPremises paperLang passiveClausePattern := by
  native_decide

/- Negative: unsupported shared-kernel rules stay out of the generated bridge. -/
example : "PositAElim" ∉ paperLang.rewrites.map (·.name) := by
  native_decide

example : "UseCompElim" ∉ paperLang.rewrites.map (·.name) := by
  native_decide

example : "UseVElim" ∉ paperLang.rewrites.map (·.name) := by
  native_decide

example : "UseN2Elim" ∉ paperLang.rewrites.map (·.name) := by
  native_decide

example : "UseA2Elim" ∉ paperLang.rewrites.map (·.name) := by
  native_decide

/- Positive: tense reduction now matches real checked GF trees as well. -/
example :
    temporalPresentPattern ∈
      rewriteWithContextWithPremises paperLang presentSentencePattern := by
  native_decide

example :
    DeclReducesWithPremises RelationEnv.empty paperLang
      presentSentencePattern temporalPresentPattern := by
  exact engineWithPremises_sound (lang := paperLang)
    (p := presentSentencePattern) (q := temporalPresentPattern) (by native_decide)

end Mettapedia.Languages.GF.GeneratedBridgeConformance
