import GFCore.Check
import GFCore.Json
import GFCore.SigGen
import Mettapedia.Languages.GF.GFRealSyntaxBridge
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
import Mettapedia.OSLF.MeTTaIL.Export

/-!
# GF Project-Core Conformance

Compiled-code conformance checks for the larger real GF bilingual slice exported
from the RGL "project core" grammar family.

Unlike `PaperAmbiguity`, this slice is currently sourced from generated JSON
artifacts rather than a kernel-reducible in-tree `funsList`, so the checks here
are intentionally regression-style:

- load the generated English and Czech abstract signatures,
- confirm the abstract function layer is identical,
- build syntax-only `LanguageDef`s,
- verify zero equations / zero rewrites / clean validation,
- check a few real core terms against both signatures,
- confirm the syntax-only lane still has no executable reductions.
-/

namespace Mettapedia.Languages.GF.GFProjectCoreConformance

open GFCore
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL

private def engProjectCorePath : System.FilePath :=
  "../algorithms/gf_fragments/generated/GrammarEng.project_core.json"

private def czeProjectCorePath : System.FilePath :=
  "../algorithms/gf_fragments/generated/GrammarCze.project_core.json"

private def ensureEq (label : String) (actual expected : String) : IO Unit :=
  if actual == expected then
    IO.println s!"PASS: {label}"
  else
    throw <| IO.userError
      s!"FAIL: {label}\n  actual:   {actual}\n  expected: {expected}"

private def ensureBool (label : String) (b : Bool) : IO Unit :=
  if b then
    IO.println s!"PASS: {label}"
  else
    throw <| IO.userError s!"FAIL: {label}"

private def sortedFunNames (sig : GrammarSig) : List String :=
  (sig.funs.toList.map (fun (nm, _) => nm)).toArray.qsort (fun a b => a < b) |>.toList

private def sortedCatNames (sig : GrammarSig) : List String :=
  sig.categories.qsort (fun a b => a < b) |>.toList

private def sortedTypeNames (lang : LanguageDef) : List String :=
  (lang.types.map (fun t => t.name)).toArray.qsort (fun a b => a < b) |>.toList

private def sortedTermNames (lang : LanguageDef) : List String :=
  (lang.terms.map GrammarRule.label).toArray.qsort (fun a b => a < b) |>.toList

private def checkedPattern? (sig : GrammarSig) (t : RawTerm) : Option Pattern :=
  match check sig t with
  | .ok e => some (gfCheckedExprToPattern e)
  | .error _ => none

def existSomethingRaw : RawTerm :=
  .mk "UseCl" #[
    .mk "TTAnt" #[.leaf "TPres", .leaf "ASimul"],
    .leaf "PPos",
    .mk "ExistNP" #[.leaf "something_NP"]]

def existSomethingPattern : Pattern :=
  .apply "UseCl"
    [ .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]
    , .apply "PPos" []
    , .apply "ExistNP" [.apply "something_NP" []] ]

def questionExistRaw : RawTerm :=
  .mk "UseQCl" #[
    .mk "TTAnt" #[.leaf "TPres", .leaf "ASimul"],
    .leaf "PPos",
    .mk "QuestCl" #[.mk "ExistNP" #[.leaf "something_NP"]]]

def questionExistPattern : Pattern :=
  .apply "UseQCl"
    [ .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]
    , .apply "PPos" []
    , .apply "QuestCl" [.apply "ExistNP" [.apply "something_NP" []]] ]

def progressiveHaveRaw : RawTerm :=
  .mk "UseCl" #[
    .mk "TTAnt" #[.leaf "TPres", .leaf "ASimul"],
    .leaf "PPos",
    .mk "PredVP" #[
      .mk "UsePron" #[.leaf "he_Pron"],
      .mk "ProgrVP" #[
        .mk "ComplSlash" #[
          .mk "SlashV2a" #[.leaf "have_V2"],
          .leaf "something_NP"]]]]

def progressiveHavePattern : Pattern :=
  .apply "UseCl"
    [ .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]
    , .apply "PPos" []
    , .apply "PredVP"
        [ .apply "UsePron" [.apply "he_Pron" []]
        , .apply "ProgrVP"
            [ .apply "ComplSlash"
                [ .apply "SlashV2a" [.apply "have_V2" []]
                , .apply "something_NP" [] ] ] ] ]

private def runProjectCoreSummary : IO Unit := do
  let engSig ← GFCore.sigFromPGFJsonFile engProjectCorePath
  let czeSig ← GFCore.sigFromPGFJsonFile czeProjectCorePath
  let engLang := gfSyntaxLanguageDef engSig
  let czeLang := gfSyntaxLanguageDef czeSig

  ensureEq "project-core grammar name (Eng)" engSig.grammar "Grammar"
  ensureEq "project-core grammar name (Cze)" czeSig.grammar "Grammar"
  ensureEq "project-core startCats (Eng)" (toString engSig.startCats.toList) "[S]"
  ensureEq "project-core startCats (Cze)" (toString czeSig.startCats.toList) "[S]"
  ensureEq "project-core function count (Eng)"
    (toString engSig.funs.size) "384"
  ensureEq "project-core function count (Cze)"
    (toString czeSig.funs.size) "384"
  ensureEq "project-core category count (Eng)"
    (toString engSig.categories.size) "90"
  ensureEq "project-core category count (Cze)"
    (toString czeSig.categories.size) "90"
  ensureBool "project-core abstract function names align"
    (sortedFunNames engSig == sortedFunNames czeSig)
  ensureBool "project-core abstract categories align"
    (sortedCatNames engSig == sortedCatNames czeSig)

  ensureEq "project-core LanguageDef type count (Eng)"
    (toString engLang.types.length) "90"
  ensureEq "project-core LanguageDef type count (Cze)"
    (toString czeLang.types.length) "90"
  ensureEq "project-core LanguageDef term count (Eng)"
    (toString engLang.terms.length) "384"
  ensureEq "project-core LanguageDef term count (Cze)"
    (toString czeLang.terms.length) "384"
  ensureEq "project-core LanguageDef rewrite count (Eng)"
    (toString engLang.rewrites.length) "0"
  ensureEq "project-core LanguageDef rewrite count (Cze)"
    (toString czeLang.rewrites.length) "0"
  ensureEq "project-core LanguageDef equation count (Eng)"
    (toString engLang.equations.length) "0"
  ensureEq "project-core LanguageDef equation count (Cze)"
    (toString czeLang.equations.length) "0"
  ensureBool "project-core type inventories align after lowering"
    (sortedTypeNames engLang == sortedTypeNames czeLang)
  ensureBool "project-core term inventories align after lowering"
    (sortedTermNames engLang == sortedTermNames czeLang)
  ensureBool "project-core Eng validates cleanly" (LanguageDef.validate engLang == [])
  ensureBool "project-core Cze validates cleanly" (LanguageDef.validate czeLang == [])
  ensureBool "project-core rendered LanguageDef agrees across Eng/Cze"
    (Export.renderLanguage engLang == Export.renderLanguage czeLang)

private def runProjectCoreExamples : IO Unit := do
  let engSig ← GFCore.sigFromPGFJsonFile engProjectCorePath
  let czeSig ← GFCore.sigFromPGFJsonFile czeProjectCorePath
  let engLang := gfSyntaxLanguageDef engSig
  ensureBool "ExistNP sentence checks in Eng"
    (checkedPattern? engSig existSomethingRaw == some existSomethingPattern)
  ensureBool "ExistNP sentence checks in Cze"
    (checkedPattern? czeSig existSomethingRaw == some existSomethingPattern)
  ensureBool "QuestCl/UseQCl question checks in Eng"
    (checkedPattern? engSig questionExistRaw == some questionExistPattern)
  ensureBool "QuestCl/UseQCl question checks in Cze"
    (checkedPattern? czeSig questionExistRaw == some questionExistPattern)
  ensureBool "ProgrVP sentence checks in Eng"
    (checkedPattern? engSig progressiveHaveRaw == some progressiveHavePattern)
  ensureBool "ProgrVP sentence checks in Cze"
    (checkedPattern? czeSig progressiveHaveRaw == some progressiveHavePattern)
  ensureBool "project-core syntax lane has no reductions for ExistNP"
    (rewriteWithContextWithPremises engLang existSomethingPattern == [])
  ensureBool "project-core syntax lane has no reductions for QuestCl"
    (rewriteWithContextWithPremises engLang questionExistPattern == [])
  ensureBool "project-core syntax lane has no reductions for ProgrVP"
    (rewriteWithContextWithPremises engLang progressiveHavePattern == [])

#eval runProjectCoreSummary

#eval runProjectCoreExamples

end Mettapedia.Languages.GF.GFProjectCoreConformance
