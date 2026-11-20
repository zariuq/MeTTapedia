import Mettapedia.Machines.ObserverLicence
import Mettapedia.Machines.OrderedRead
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

/-!
The kernel declarations are checked separately from Lean's generated partial
runtime companions. A companion must have the compiler's exact recursive
name shape and an existing safe, total parent. No authored unsafe/partial
definition or new logical axiom is accepted.
-/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let prefixes := [`Mettapedia.Machines.ObserverLicence, `Mettapedia.Machines.OrderedRead]
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut companions : Nat := 0
  for (name, info) in environment.constants.toList do
    if prefixes.any (fun scopePrefix => scopePrefix.isPrefixOf name) then
      if info.isUnsafe then
        throwError "Unsafe declaration: {name}"
      if info.isPartial then
        let some parent := Compiler.isUnsafeRecName? name
          | throwError "Noncompiler partial declaration: {name}"
        let some parentInfo := environment.find? parent
          | throwError "Missing total parent for {name}"
        if parentInfo.isUnsafe || parentInfo.isPartial then
          throwError "Invalid parent for {name}"
        companions := companions + 1
        continue
      if let .axiomInfo _ := info then
        throwError "Added axiom: {name}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless allowed.contains dependency do
          throwError "Unexpected axiom {dependency} in {name}"
      declarations := declarations + 1
      if let .thmInfo _ := info then
        theorems := theorems + 1
  if declarations == 0 || theorems == 0 then
    throwError "The requested namespaces were not audited"
  logInfo m!"W5 strict audit: {declarations} safe logical declarations; {theorems} theorem constants; {companions} compiler companions; only standard axioms"
