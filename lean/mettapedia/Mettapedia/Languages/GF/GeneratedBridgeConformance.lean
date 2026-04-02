import GFCore.Check
import Algorithms.GF.Generated.PaperAmbiguitySig
import Mettapedia.Languages.GF.GFRealSyntaxBridge
import Mettapedia.Languages.GF.ConformanceCertificate
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises

/-!
# GF Generated-Bridge Conformance

Pins the real GF→IR→Lean bridge to `PaperAmbiguitySig`, a generated grammar.

This file is intentionally limited to the authoritative syntax-only path:

- `GFCore.check` validates raw GF terms against the real signature
- `gfCheckedExprToPattern` lowers checked trees to OSLF patterns
- `gfSyntaxLanguageDef` captures the same generated grammar in the MeTTaIL DSL

No invented semantic equations or rewrites are part of this contract.
-/

namespace Mettapedia.Languages.GF.GeneratedBridgeConformance

open GFCore
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.Languages.GF.ConformanceCertificate
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

def paperSig : GrammarSig :=
  Algorithms.GF.Generated.PaperAmbiguitySig.sig

def paperSyntaxLang : LanguageDef :=
  gfSyntaxLanguageDef paperSig

def checkedPattern? (t : RawTerm) : Option Pattern :=
  match check paperSig t with
  | .ok e => some (gfCheckedExprToPattern e)
  | .error _ => none

-- ═══════════════════════════════════════════════════════════════════
-- Structural pattern literals for real checked parses
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

def presentSentenceRaw : RawTerm :=
  .mk "UseCl" #[.mk "TTAnt" #[.leaf "TPres", .leaf "ASimul"], .leaf "PPos", activeClauseRaw]

def presentSentencePattern : Pattern :=
  .apply "UseCl"
    [ .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]
    , .apply "PPos" [], activeClausePattern]

def badTypeRaw : RawTerm := .mk "UseN" #[.leaf "see_V2"]

-- A semantic target that should NOT be reachable in the syntax-only lane.
def temporalPresentPattern : Pattern :=
  .apply "⊛temporal" [activeClausePattern, .apply "0" []]

-- ═══════════════════════════════════════════════════════════════════
-- Layer 1: Kernel-checked facts about the certificate literals
-- ═══════════════════════════════════════════════════════════════════

example : paperTypeNames.length = 16 := by decide
example : paperTermNames.length = 26 := by decide
example : paperEquationCount = 0 := rfl
example : paperRewriteCount = 0 := rfl

-- ═══════════════════════════════════════════════════════════════════
-- Layer 2: Compiled-code-verified exact bridge checks
-- ═══════════════════════════════════════════════════════════════════

private def ensureEq (label : String) (actual expected : String) : IO Unit :=
  if actual == expected then
    IO.println s!"PASS: {label}"
  else
    throw <| IO.userError s!"FAIL: {label}: got {actual}, expected {expected}"

private def ensureBool (label : String) (b : Bool) : IO Unit :=
  if b then
    IO.println s!"PASS: {label}"
  else
    throw <| IO.userError s!"FAIL: {label}"

#eval do
  ensureEq "type count" (toString paperSyntaxLang.types.length) "16"
  ensureEq "term count" (toString paperSyntaxLang.terms.length) "26"
  ensureEq "equation count" (toString paperSyntaxLang.equations.length) "0"
  ensureEq "rewrite count" (toString paperSyntaxLang.rewrites.length) "0"
  ensureBool "validation clean" (LanguageDef.validate paperSyntaxLang == [])
  ensureEq "type names"
    (toString (paperSyntaxLang.types.map (fun t : TypeDecl => t.name)))
    (toString paperTypeNames)
  ensureEq "term names"
    (toString (paperSyntaxLang.terms.map GrammarRule.label))
    (toString paperTermNames)

#eval do
  ensureBool "UseN(man_N) check"
    (checkedPattern? useNManRaw == some useNManPattern)
  ensureBool "active clause check"
    (checkedPattern? activeClauseRaw == some activeClausePattern)
  ensureBool "present sentence check"
    (checkedPattern? presentSentenceRaw == some presentSentencePattern)
  ensureBool "ill-typed UseN(see_V2) rejected"
    (checkedPattern? badTypeRaw == none)

#eval do
  ensureBool "syntax lane has no authored reductions"
    (rewriteWithContextWithPremises paperSyntaxLang presentSentencePattern == [])
  ensureBool "no temporal target produced in syntax lane"
    (temporalPresentPattern ∉ rewriteWithContextWithPremises paperSyntaxLang presentSentencePattern)
  ensureBool "UseN(man_N) does not reduce in syntax lane"
    (manPattern ∉ rewriteWithContextWithPremises paperSyntaxLang useNManPattern)

end Mettapedia.Languages.GF.GeneratedBridgeConformance
