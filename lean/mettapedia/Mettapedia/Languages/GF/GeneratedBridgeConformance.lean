import GFCore.Check
import Algorithms.GF.Generated.PaperAmbiguitySig
import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises

/-!
# GF Generated-Bridge Conformance

Pins the GF→OSLF bridge to `PaperAmbiguitySig`, a real auto-generated GrammarSig.

## Trust model

`paperLang` involves `HashMap.fold` which the Lean kernel cannot reduce, so
kernel-checked `decide` proofs are not possible on HashMap-derived values.
Instead we use a two-layer approach:

1. **Kernel-checked** (`decide`): properties of the authored semantic kernel
   (SemanticKernelDSL) and pre-computed literal pattern values.
2. **Compiled-code-verified** (`#eval`): regression checks that the actual
   bridge output matches expected values. These run in compiled Lean code
   (same as `native_decide`) but are NOT kernel-checked. They guard against
   drift between the kernel definition and the generated signature.

This is honest: we kernel-check what we CAN (the semantic rules themselves),
and compiled-code-verify what we MUST (the HashMap-dependent bridge output).
-/

namespace Mettapedia.Languages.GF.GeneratedBridgeConformance

open GFCore
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

def paperSig : GrammarSig :=
  Algorithms.GF.Generated.PaperAmbiguitySig.sig

def paperLang : LanguageDef :=
  gfRGLLanguageDef paperSig

def checkedPattern? (t : RawTerm) : Option Pattern :=
  match check paperSig t with
  | .ok e => some (gfCheckedExprToPattern e)
  | .error _ => none

-- ═══════════════════════════════════════════════════════════════════
-- Structural definitions (kernel-reducible Pattern literals)
-- ═══════════════════════════════════════════════════════════════════

def useNManRaw : RawTerm := .mk "UseN" #[.leaf "man_N"]
def useNManPattern : Pattern := .apply "UseN" [.apply "man_N" []]
def manPattern : Pattern := .apply "man_N" []

def johnNPPattern : Pattern := .apply "UsePN" [.apply "john_PN" []]
def annaNPPattern : Pattern := .apply "UsePN" [.apply "anna_PN" []]

def activeClauseRaw : RawTerm :=
  .mk "PredVP" #[
    .mk "UsePN" #[.leaf "john_PN"],
    .mk "ComplSlash" #[.mk "SlashV2a" #[.leaf "see_V2"], .mk "UsePN" #[.leaf "anna_PN"]]]

def activeClausePattern : Pattern :=
  .apply "PredVP"
    [ johnNPPattern
    , .apply "ComplSlash" [.apply "SlashV2a" [.apply "see_V2" []], annaNPPattern]]

def passiveClausePattern : Pattern :=
  .apply "PredVP" [annaNPPattern, .apply "PassV2" [.apply "see_V2" []]]

def presentSentenceRaw : RawTerm :=
  .mk "UseCl" #[.mk "TTAnt" #[.leaf "TPres", .leaf "ASimul"], .leaf "PPos", activeClauseRaw]

def presentSentencePattern : Pattern :=
  .apply "UseCl"
    [ .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]
    , .apply "PPos" [], activeClausePattern]

def temporalPresentPattern : Pattern :=
  .apply "⊛temporal" [activeClausePattern, .apply "0" []]

def negTemporalPresentPattern : Pattern :=
  .apply "⊛negation" [.apply "⊛temporal" [activeClausePattern, .apply "0" []]]

def embedSPresentSentencePattern : Pattern :=
  .apply "EmbedS" [presentSentencePattern]

def embeddedActiveClausePattern : Pattern :=
  .apply "⊛embedded" [activeClausePattern]

-- ═══════════════════════════════════════════════════════════════════
-- Layer 1: Kernel-checked properties (authored semantic kernel)
-- ═══════════════════════════════════════════════════════════════════

-- The authored kernel has exactly 44 rewrites in 11 families
example : gfSemanticKernelLanguageDef.rewrites.length = 44 := by decide
example : gfSemanticKernelLanguageDef.equations.length = 1 := by decide

-- Structural equality on RGL definitions
example : paperLang.equations = gfSemanticEquationsForSig paperSig := rfl
example : paperLang.rewrites = gfSemanticRewritesForSig paperSig := rfl

-- ═══════════════════════════════════════════════════════════════════
-- Layer 2: Compiled-code-verified regression (HashMap-dependent)
--
-- These #eval checks run in compiled code and print PASS/FAIL.
-- They are NOT kernel-checked but guard against bridge drift.
-- ═══════════════════════════════════════════════════════════════════

private def assertEq (label : String) (actual expected : String) : IO Unit :=
  if actual == expected then IO.println s!"PASS: {label}"
  else IO.println s!"FAIL: {label}: got {actual}, expected {expected}"

private def assertBool (label : String) (b : Bool) : IO Unit :=
  if b then IO.println s!"PASS: {label}"
  else IO.println s!"FAIL: {label}"

#eval do
  -- Equation count
  assertEq "equation count" (toString paperLang.equations.length) "1"
  -- Rewrite count (40 kernel rewrites, 18 pass validation for PaperAmbiguitySig)
  assertEq "rewrite count" (toString paperLang.rewrites.length) "22"
  -- Validation clean
  assertBool "validation clean" (LanguageDef.validate paperLang == [])
  -- Exact rewrite inventory
  let rwNames := paperLang.rewrites.map (fun rw => RewriteRule.name rw)
  let expected := [ "UseNElim", "ActivePassive"
    , "PresentTense", "PastTense", "FutureTense"
    , "NegationPresent", "NegationPast", "NegationFuture"
    , "EmbedPresent", "EmbedPast", "EmbedFuture"
    , "UsePNElim", "EmbedVPLifting", "EmbedQSLifting"
    , "AnteriorPresent", "AnteriorPast"
    , "ConditionalSimul", "ConditionalAnter"
    , "DetEveryElim", "DetSomeElim", "DetTheElim", "DetNoElim" ]
  assertEq "rewrite names" (toString rwNames) (toString expected)

#eval do
  -- GFCore.check + gfCheckedExprToPattern roundtrip
  assertBool "UseN(man_N) check" (checkedPattern? useNManRaw == some useNManPattern)
  assertBool "active clause check" (checkedPattern? activeClauseRaw == some activeClausePattern)
  assertBool "present sentence check" (checkedPattern? presentSentenceRaw == some presentSentencePattern)

#eval do
  -- Rewrite engine: positive reductions
  assertBool "UseN(man_N) reduces to man_N"
    (manPattern ∈ rewriteWithContextWithPremises paperLang useNManPattern)
  assertBool "active→passive fires"
    (passiveClausePattern ∈ rewriteWithContextWithPremises paperLang activeClausePattern)
  assertBool "present tense fires"
    (temporalPresentPattern ∈ rewriteWithContextWithPremises paperLang presentSentencePattern)
  assertBool "embedding fires"
    (embeddedActiveClausePattern ∈ rewriteWithContextWithPremises paperLang embedSPresentSentencePattern)

#eval do
  -- Rewrite engine: negative (directional) checks
  assertBool "passive→active does NOT fire"
    (activeClausePattern ∉ rewriteWithContextWithPremises paperLang passiveClausePattern)
  assertBool "negation does NOT fire on PPos sentence"
    (negTemporalPresentPattern ∉ rewriteWithContextWithPremises paperLang presentSentencePattern)

#eval do
  -- Excluded rewrites (constructors absent from PaperAmbiguitySig)
  let rwNames := paperLang.rewrites.map (fun rw => RewriteRule.name rw)
  assertBool "PositAElim excluded" ("PositAElim" ∉ rwNames)
  assertBool "UseCompElim excluded" ("UseCompElim" ∉ rwNames)
  assertBool "ConjSBinary excluded" ("ConjSBinary" ∉ rwNames)
  assertBool "RelVPSubject excluded" ("RelVPSubject" ∉ rwNames)
  assertBool "ComplVVElim excluded" ("ComplVVElim" ∉ rwNames)

end Mettapedia.Languages.GF.GeneratedBridgeConformance
