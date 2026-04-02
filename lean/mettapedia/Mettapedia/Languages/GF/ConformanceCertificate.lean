import Algorithms.GF.Generated.PaperAmbiguitySig
import Mettapedia.Languages.GF.GFRealSyntaxBridge

/-!
# GF Conformance Certificate

Pre-computed structural facts for the authoritative syntax-only GF lane.

`paperSyntaxLang := gfSyntaxLanguageDef paperSig` is the real
GF→IR→Lean→LanguageDef object for `PaperAmbiguitySig`: only categories and
constructors from the generated grammar, with zero invented equations or
rewrites.

Because `GrammarSig.funs` is a `HashMap`, the kernel cannot reduce the full
construction directly. We therefore keep literal certificates for the expected
type and term inventories, then use compiled-code regression checks to ensure
the real bridge output matches those literals exactly.
-/

namespace Mettapedia.Languages.GF.ConformanceCertificate

open GFCore
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The PaperAmbiguity grammar signature. -/
def paperSig : GrammarSig :=
  Algorithms.GF.Generated.PaperAmbiguitySig.sig

/-- The authoritative syntax-only LanguageDef computed from `PaperAmbiguitySig`. -/
def paperSyntaxLang : LanguageDef :=
  gfSyntaxLanguageDef paperSig

/-- Pre-computed category names for `paperSyntaxLang.types`. -/
def paperTypeNames : List String :=
  [ "V2", "N", "VP", "Adv", "PN", "VPSlash", "CN", "Tense"
  , "Ant", "Temp", "Det", "NP", "Pol", "Cl", "S", "Prep" ]

/-- Pre-computed constructor names for `paperSyntaxLang.terms`. -/
def paperTermNames : List String :=
  [ "PredVP", "dress_V2", "ComplSlash", "man_N", "PPos", "PrepNP"
  , "in_Prep", "crib_N", "TPres", "ASimul", "AdvCN", "TPast"
  , "with_Prep", "john_PN", "UsePN", "the_Det", "UseCl", "DetCN"
  , "TTAnt", "UseN", "telescope_N", "SlashV2a", "anna_PN", "AdvVP"
  , "baby_N", "see_V2" ]

/-- Pre-computed equation count. -/
def paperEquationCount : Nat := 0

/-- Pre-computed rewrite count. -/
def paperRewriteCount : Nat := 0

-- Kernel-checked facts about the literal certificates.
example : paperTypeNames.length = 16 := by decide
example : paperTermNames.length = 26 := by decide
example : paperEquationCount = 0 := rfl
example : paperRewriteCount = 0 := rfl

-- Positive membership examples.
example : "S" ∈ paperTypeNames := by decide
example : "Cl" ∈ paperTypeNames := by decide
example : "PredVP" ∈ paperTermNames := by decide
example : "UseCl" ∈ paperTermNames := by decide
example : "TPres" ∈ paperTermNames := by decide

-- Negative membership examples.
example : "SC" ∉ paperTypeNames := by decide
example : "PassV2" ∉ paperTermNames := by decide
example : "⊛temporal" ∉ paperTermNames := by decide
example : "EmbedS" ∉ paperTermNames := by decide

private def ensureEq (label : String) (actual expected : String) : IO Unit :=
  if actual == expected then
    IO.println s!"OK: {label}"
  else
    throw <| IO.userError
      s!"MISMATCH: {label}\n  actual:   {actual}\n  expected: {expected}"

#eval do
  let actualTypeNames := paperSyntaxLang.types.map (fun t : TypeDecl => t.name)
  ensureEq "type names" (toString actualTypeNames) (toString paperTypeNames)

#eval do
  let actualTermNames := paperSyntaxLang.terms.map GrammarRule.label
  ensureEq "term names" (toString actualTermNames) (toString paperTermNames)

#eval do
  ensureEq "equation count"
    (toString paperSyntaxLang.equations.length) (toString paperEquationCount)
  ensureEq "rewrite count"
    (toString paperSyntaxLang.rewrites.length) (toString paperRewriteCount)

#eval do
  let errs := LanguageDef.validate paperSyntaxLang
  if errs.isEmpty then
    IO.println "OK: validation clean"
  else
    throw <| IO.userError s!"VALIDATION ERRORS: {errs.length}"

end Mettapedia.Languages.GF.ConformanceCertificate
