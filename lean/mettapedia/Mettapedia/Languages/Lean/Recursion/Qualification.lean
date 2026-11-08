import Mettapedia.Languages.Lean.Recursion.Core
import Mettapedia.Languages.Lean.Recursion.Controls
import Mettapedia.Languages.Lean.Recursion.Coverage

/-!
# Source-linked recursion qualification

Besides the malformed recipe/relation controls, an omitted registry entry
must remain a coverage failure even though its source function still exists.
This prevents a partial inventory from silently qualifying a dependency.
-/

open Lean Meta
open Mettapedia.Languages.Lean.Recursion

#eval show MetaM Unit from do
  let env ← getEnv
  let records := Derive.registry.getState env
  let wrappers := Wrappers.registry.getState env
  let complete ← Coverage.auditWith records wrappers #[``Nat.gcd]
  unless complete.any (fun finding => finding.source == ``Nat.gcd && finding.required && finding.recorded) do
    throwError "registered gcd recursion was not accounted for"
  let incomplete ← Coverage.auditWith (records.filter (·.source != ``Nat.gcd)) wrappers #[``Nat.gcd]
  unless incomplete.any (fun finding => finding.source == ``Nat.gcd && finding.required && !finding.recorded) do
    throwError "omitted recursion interface was silently qualified"
  IO.println "recursion coverage detects an omitted interface"

#print axioms MeasuredCore.Gcd.functionBridge
#print axioms MeasuredCore.MergeSort.functionBridge
#print axioms RelationalCore.Merge.functionBridge
#print axioms StructuralCore.DivGo.functionBridge
#print axioms StructuralCore.ModGo.functionBridge
#print axioms Core.Div.bridge
#print axioms Core.Mod.bridge
#print axioms Controls.changed_at_zero
#print axioms Controls.badRelation_not_wellFounded
