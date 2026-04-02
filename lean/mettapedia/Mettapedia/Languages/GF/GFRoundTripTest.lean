import Mettapedia.Languages.GF.ConformanceCertificate
import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.OSLF.MeTTaIL.ExportGF

/-!
# GF Rendering Conformance Regression

Smoke tests for the authoritative syntax-only GF `LanguageDef`.

The source of truth here is the real generated grammar
`paperSyntaxLang := gfSyntaxLanguageDef paperSig`. Rust and GF outputs are
derived renderings of that actual GF signature, not of an authored semantic
kernel.
-/

namespace Mettapedia.Languages.GF.GFRoundTripTest

open Mettapedia.Languages.GF.ConformanceCertificate
open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.OSLF.MeTTaIL.ExportGF

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Structural certificate facts
-- ═══════════════════════════════════════════════════════════════════

example : paperSyntaxLang.name = "PaperAmbiguity" := rfl
example : paperTypeNames.length = 16 := by decide
example : paperTermNames.length = 26 := by decide
example : paperEquationCount = 0 := rfl
example : paperRewriteCount = 0 := rfl

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Rendering fidelity (compiled-code regression)
-- ═══════════════════════════════════════════════════════════════════

private def rustOutput : String := renderLanguage paperSyntaxLang
private def gfOutput : String := renderGFAbstract paperSyntaxLang

private def hasSubstring (needle haystack : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def assertContains (label needle : String) (haystack : String) : IO Unit :=
  if hasSubstring needle haystack then IO.println s!"PASS: contains {label}"
  else throw <| IO.userError s!"FAIL: missing {label}: {needle}"

private def assertNotContains (label needle : String) (haystack : String) : IO Unit :=
  if hasSubstring needle haystack then
    throw <| IO.userError s!"FAIL: unexpected {label}: {needle}"
  else
    IO.println s!"PASS: excludes {label}"

#eval do
  assertContains "name" "name: PaperAmbiguity," rustOutput
  assertContains "PredVP constructor" "PredVP" rustOutput
  assertContains "UseCl constructor" "UseCl" rustOutput
  assertContains "TPres constructor" "TPres" rustOutput
  assertContains "category S" "S" rustOutput
  assertNotContains "invented temporal operator" "⊛temporal" rustOutput
  assertNotContains "invented embedding operator" "⊛embedded" rustOutput

#eval do
  assertContains "GF abstract name" "abstract PaperAmbiguity" gfOutput
  assertContains "GF cat S" "cat S ;" gfOutput
  assertContains "GF fun PredVP" "fun PredVP" gfOutput
  assertContains "GF fun UseCl" "fun UseCl" gfOutput
  assertNotContains "semantic rewrite comments" "-- rewrite:" gfOutput
  assertNotContains "semantic equation comments" "-- equation:" gfOutput

#eval do
  IO.println s!"Real GF syntax types: {paperSyntaxLang.types.length}"
  IO.println s!"Real GF syntax terms: {paperSyntaxLang.terms.length}"
  IO.println s!"Rust output: {rustOutput.length} chars"
  IO.println s!"GF output: {gfOutput.length} chars"
  if rustOutput.length > 100 && gfOutput.length > 100 then
    IO.println "PASS: Real GF syntax renders non-trivially"
  else
    throw <| IO.userError "FAIL: Some rendering is trivially small"

end Mettapedia.Languages.GF.GFRoundTripTest
