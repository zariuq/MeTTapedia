import Mettapedia.Languages.Lean.Recursion.Export
import Mettapedia.Languages.Lean.Recursion.Coverage
import Mettapedia.Languages.Lean.Recursion.ProofArguments
import Mettapedia.Languages.Lean.Declarations.TargetEnvironment

/-!
Export checked recursion interfaces from a target module inventory.
LEAN_RECURSION_TARGET defaults to core; LEAN_RECURSION_OUT optionally selects
the output directory. LEAN_RECURSION_CHECK=1 compares a fresh export without
writing files. Source modules are listed in the target's modules.txt.
-/

open Lean Meta
open Mettapedia.Languages.Lean

#eval show MetaM Unit from do
  let target := (← IO.getEnv "LEAN_RECURSION_TARGET").getD "core"
  let directory : System.FilePath := "artifacts/lean-declarations" / target
  discard <| Declarations.TargetEnvironment.load directory
  let entries := Recursion.Derive.registry.getState (← getEnv)
  let wrappers := Recursion.Wrappers.registry.getState (← getEnv)
  let fuels := Recursion.FuelDerive.registry.getState (← getEnv)
  let receipts : System.FilePath := (← IO.getEnv "LEAN_RECURSION_RECEIPTS").getD
    s!"artifacts/lean-code-equations/{target}/receipts.tsv"
  let rows ← IO.FS.lines receipts
  let mut roots : Array Name := if target == "core" then #[``Nat.div, ``Nat.mod] else #[]
  for row in rows.toList.drop 1 do
    let spelling := (row.splitOn "\t").headD ""
    if !spelling.isEmpty && !roots.contains spelling.toName then roots := roots.push spelling.toName
  for name in roots do
    unless (← getEnv).contains name do throwError "recursion coverage root is not imported: {name}"
  let mut findings ← Recursion.Coverage.audit roots
  let mut text := (← Recursion.Export.render entries) ++ (← Recursion.Export.wrappers wrappers) ++
    (← Recursion.Export.fuelReadings fuels)
  for index in [:findings.size] do
    let finding := findings[index]!
    if finding.required && !finding.recorded && !finding.recursive then
      text := text ++ (← Recursion.ProofArguments.render finding.source)
      findings := findings.set! index { finding with recorded := true }
  let missing := findings.filter fun finding => finding.required && !finding.recorded
  unless missing.isEmpty do
    throwError "recursion interfaces missing: {missing.map (·.source)}"
  text := text.trimAsciiEnd.toString ++ "\n"
  let coverage := "source\timplementation\trequired\trecorded\trecursive\n" ++
    String.intercalate "\n" (findings.toList.map fun finding =>
      s!"{finding.source}\t{finding.implementation}\t{finding.required}\t{finding.recorded}\t{finding.recursive}") ++ "\n"
  let rootText := String.intercalate "\n" (roots.toList.map Name.toString) ++ "\n"
  let out : System.FilePath := (← IO.getEnv "LEAN_RECURSION_OUT").getD directory.toString
  let outputs := [("recursion.metta", text), ("recursion-coverage.tsv", coverage), ("recursion-roots.txt", rootText)]
  if (← IO.getEnv "LEAN_RECURSION_CHECK") == some "1" then
    for (file, fresh) in outputs do
      unless (← IO.FS.readFile (out / file)) == fresh do throwError "{file} differs from regeneration"
    IO.println "check: recursion artifacts equal a fresh export"
  else
    IO.FS.createDirAll out
    for (file, value) in outputs do IO.FS.writeFile (out / file) value
    IO.println s!"exported {entries.size} recursion interfaces, {wrappers.size} source wrappers and {fuels.size} fuel readings"
