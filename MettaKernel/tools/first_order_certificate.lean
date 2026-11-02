import Mettapedia.GSLT.LanguageDef.FirstOrderCertificateData
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-! Candidate production over the actual supplied rule inventory. The portable
module is read and validated independently; every returned article is checked
against it. Search budgets describe producer work, not logical completeness. -/

open Lean (Json)
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.FirstOrderPremiseSearch
open Mettapedia.GSLT.LanguageDef.FirstOrderCertificateData

private def run (input output moduleFile : System.FilePath) (steps depth : Nat) : IO UInt32 := do
  let inputJson ← unwrap (Json.parse (← IO.FS.readFile input))
  let rules ← unwrap do (← arrayField inputJson "rules").mapM rule
  let moduleText ← IO.FS.readFile moduleFile
  let some definition := ModuleFormat.Portable.readValidatedCalculus? moduleText |
    throw (IO.userError "the supplied module failed calculus validation")
  let encodedRules := InferenceCettaWire.encodeList InferenceCettaWire.encodeRule
  unless CettaWire.Term.render (encodedRules definition.val.rules) =
      CettaWire.Term.render (encodedRules (rules.toList.map FORule.toSchema)) do
    throw (IO.userError "candidate inventory differs from the admitted module")
  let requests ← unwrap (arrayField inputJson "requests")
  let mut results := #[]
  let mut passed := true
  for request in requests do
    let name ← unwrap (stringField request "name")
    let goal ← unwrap do pattern (← field request "goal")
    let selectedSeed ← unwrap do
      match field request "seed" with
      | .error _ => pure none
      | .ok value => seed value
    let report := search rules.toList goal selectedSeed ⟨steps, depth, steps⟩
    let certified := checkedCandidate definition goal report
    let report := match report.outcome with
      | .candidate _ => if certified.isSome then report else
          { report with outcome := .fault "candidate refused by the independent checker" }
      | _ => report
    let row ← unwrap (reportJson name goal report)
    results := results.push row
    let success := match report.outcome with | .candidate _ => true | _ => false
    passed := passed && success
    IO.println s!"{name}: {if success then "checked" else "unfinished"}; {report.attempts} rule attempts"
  IO.FS.writeFile output ((Json.mkObj [("results", .arr results)]).compress ++ "\n")
  return if passed then 0 else 1

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [input, output, "--module", moduleFile, "--budget", budget, "--depth", depth] =>
      let some steps := budget.toNat? | throw (IO.userError "budget must be a natural number")
      let some depth := depth.toNat? | throw (IO.userError "depth must be a natural number")
      run input output moduleFile steps depth
  | _ => throw (IO.userError
      "expected INPUT OUTPUT --module MODULE --budget STEPS --depth DEPTH")
