/-
# Deterministic statement-level DTTBench profile-demand fixtures

This executable serializes the Lean demand analysis one frozen statement at a
time.  The meta row pins the two kernel sources and the generated DTTBench
statement module; `check` rejects any byte-level fixture drift.
-/

import Mettapedia.GSLT.LanguageDef.LF.DTTBenchDemand

namespace Mettapedia.GSLT.LanguageDef.LFDTTBenchDemandMain

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.GSLT.LanguageDef.LFDTTBenchDemand
open Mettapedia.GSLT.LanguageDef.PureDTTBench31

/-- SHA-256 of `MettaKernel/kernel/kernel_signature_lf_v0.metta`. -/
def basicKernelSha256 : String :=
  "91b510838ef3568e5d18504d10fcf1ffa658362271c1871bf735f598265bf548"

/-- SHA-256 of `MettaKernel/kernel/kernel_signature_lf_indexed_v0.metta`. -/
def indexedKernelSha256 : String :=
  "bf9ce2eb2d6c8deccfaa167faeb58d384444b9ef9f883bba0cd9b4430424e290"

/-- SHA-256 of the frozen Lean-owned `Pure/DTTBench31.lean` module. -/
def dttbenchModuleSha256 : String :=
  "51a8070f7b44bbc4ad6776a0db8c2905aeb3eab5cd2b9523b6f0366e62e66809"

private def jsonEscapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | character => character.toString

private def jsonString (value : String) : String :=
  "\"" ++ String.join (value.toList.map jsonEscapeChar) ++ "\""

private def jsonBool (value : Bool) : String :=
  if value then "true" else "false"

private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def sortName : Srt → String
  | .type => "type"
  | .kind => "kind"

private def renderOptionalSort : Option Srt → String
  | none => "null"
  | some sort => jsonString (sortName sort)

private def renderRule (rule : ProductRule) : String :=
  jsonString s!"{sortName rule.domain}:{sortName rule.codomain}:{sortName rule.result}"

private def renderStatement (statement : Statement) : String :=
  let demandedRules :=
    ((demand? indexed statement.goal).getD []).eraseDups.map renderRule
  "{" ++
    "\"kind\":\"statement_demand\"," ++
    "\"group\":" ++ jsonString statement.group ++ "," ++
    "\"name\":" ++ jsonString statement.name ++ "," ++
    "\"source_path\":" ++ jsonString statement.sourcePath ++ "," ++
    "\"source_sha256\":" ++ jsonString statement.sourceSha256 ++ "," ++
    "\"canonical_path\":" ++ jsonString statement.canonicalPath ++ "," ++
    "\"canonical_sha256\":" ++ jsonString statement.canonicalSha256 ++ "," ++
    "\"normalized_type_sha256\":" ++
      jsonString statement.normalizedTypeSha256 ++ "," ++
    "\"basic_profile_forms\":" ++
      jsonBool (statementWithin basic statement) ++ "," ++
    "\"indexed_profile_forms\":" ++
      jsonBool (statementWithin indexed statement) ++ "," ++
    "\"result_sort\":" ++
      renderOptionalSort (inferSort analysisFuel indexed [] statement.goal) ++ "," ++
    "\"required_product_rules\":" ++ jsonArray demandedRules ++
  "}"

private def renderMeta : String :=
  "{" ++
    "\"kind\":\"meta\"," ++
    "\"schema\":\"gslt.lf.dttbench_profile_demand.v1\"," ++
    "\"row_count\":" ++ toString statements.length ++ "," ++
    "\"basic_kernel_sha256\":" ++ jsonString basicKernelSha256 ++ "," ++
    "\"indexed_kernel_sha256\":" ++ jsonString indexedKernelSha256 ++ "," ++
    "\"dttbench_module_sha256\":" ++ jsonString dttbenchModuleSha256 ++ "," ++
    "\"dttbench_generator_sha256\":" ++ jsonString generatorSha256 ++
  "}"

def renderFixtures : String :=
  String.intercalate "\n" (renderMeta :: statements.map renderStatement) ++ "\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["write", outputPath] =>
      let output := renderFixtures
      IO.FS.writeFile outputPath output
      IO.println s!"wrote {output.toUTF8.size} bytes to {outputPath}"
      pure 0
  | ["check", fixturePath] =>
      let actual ← IO.FS.readFile fixturePath
      if actual = renderFixtures then
        IO.println s!"fixture parity OK: {fixturePath}"
        pure 0
      else
        IO.eprintln s!"fixture drift: regenerate {fixturePath} from DTTBenchDemandMain.lean"
        pure 1
  | _ =>
      IO.eprintln "usage: DTTBenchDemandMain (write|check) <fixture.jsonl>"
      pure 1

end Mettapedia.GSLT.LanguageDef.LFDTTBenchDemandMain

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.LFDTTBenchDemandMain.main arguments
